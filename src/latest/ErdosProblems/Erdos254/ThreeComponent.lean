/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.SumsetBohr

namespace Erdos254

open Filter Set

/-- The three-component criterion used in Fan's proof. The first two components
give a piecewise Bohr set; finitely many terms of the third make it thick, and
the remaining terms have syndetic subset sums. -/
theorem three_component_complete {B₁ B₂ C : Set ℕ}
    (h₁₂ : Disjoint B₁ B₂) (h₁C : Disjoint B₁ C) (h₂C : Disjoint B₂ C)
    (hi₁ : B₁.Infinite) (hi₂ : B₂.Infinite) (hiC : C.Infinite)
    (hd₁ : HasBoundedDefect B₁) (hd₂ : HasBoundedDefect B₂) (hdC : HasBoundedDefect C)
    (hdiv : PhaseDivergent C) : IsComplete (B₁ ∪ B₂ ∪ C) := by
  have hPB : ContainsPiecewiseBohr (subsetSums (B₁ ∪ B₂)) := by
    apply (syndetic_sumset_piecewiseBohr (syndetic_subsetSums hi₁ hd₁)
      (syndetic_subsetSums hi₂ hd₂)).mono
    rintro n ⟨a, ha, b, hb, rfl⟩
    exact IsSumOfDistinct.add h₁₂ ha hb
  have hBC : Disjoint (B₁ ∪ B₂) C := disjoint_union_left.mpr ⟨h₁C, h₂C⟩
  obtain ⟨E, hEC, hthick⟩ := finite_support_thick_of_piecewiseBohr hBC hPB hdiv
  have hsyndetic : IsSyndetic (subsetSums (C \ (E : Set ℕ))) :=
    syndetic_subsetSums (hiC.sdiff E.finite_toSet) (hdC.sdiff_finset E)
  have hdisj : Disjoint (C \ (E : Set ℕ)) ((B₁ ∪ B₂) ∪ (E : Set ℕ)) := by
    apply Set.disjoint_left.mpr
    rintro n hn (hb | he)
    · exact Set.disjoint_left.mp hBC hb hn.1
    · exact hn.2 he
  apply (complete_union_of_syndetic_thick hdisj hsyndetic hthick).mono
  rintro n (hn | (hb | he))
  · exact Or.inr hn.1
  · exact Or.inl hb
  · exact Or.inr (hEC he)

/-- The criterion is stable under every finite deletion. -/
theorem three_component_stronglyComplete {B₁ B₂ C : Set ℕ}
    (h₁₂ : Disjoint B₁ B₂) (h₁C : Disjoint B₁ C) (h₂C : Disjoint B₂ C)
    (hi₁ : B₁.Infinite) (hi₂ : B₂.Infinite) (hiC : C.Infinite)
    (hd₁ : HasBoundedDefect B₁) (hd₂ : HasBoundedDefect B₂) (hdC : HasBoundedDefect C)
    (hdiv : PhaseDivergent C) : IsStronglyComplete (B₁ ∪ B₂ ∪ C) := by
  intro D
  have h := three_component_complete
    (h₁₂.mono sdiff_subset sdiff_subset) (h₁C.mono sdiff_subset sdiff_subset)
    (h₂C.mono sdiff_subset sdiff_subset)
    (hi₁.sdiff D.finite_toSet) (hi₂.sdiff D.finite_toSet) (hiC.sdiff D.finite_toSet)
    (hd₁.sdiff_finset D) (hd₂.sdiff_finset D) (hdC.sdiff_finset D) (hdiv.sdiff_finset D)
  apply h.mono
  rintro n ((hn | hn) | hn)
  · exact ⟨Or.inl (Or.inl hn.1), hn.2⟩
  · exact ⟨Or.inl (Or.inr hn.1), hn.2⟩
  · exact ⟨Or.inr hn.1, hn.2⟩

end Erdos254
