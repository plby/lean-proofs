import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbar

/-!
# An actual two-variable compact-support antiholomorphic primitive

For a smooth closed `(0,1)` form `f dbar(z) + g dbar(w)`, uniform compact
support in `w` suffices: Cauchy–Green applied to `g` solves both coordinate
equations.  In particular every compactly supported smooth closed form on
the actual two-dimensional complex vector space has a smooth primitive.
No global Cousin or bundle-classification assertion is an input.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open HolomorphicCousin

/-- The closedness equation is the actual equality of antiholomorphic partial
derivatives, with the order fixed by `f dbar(z) + g dbar(w)`. -/
def IsDbarClosed (f g : ℂ × ℂ → ℂ) : Prop :=
  ∀ q, dbarFirst g q = dbarSecond f q

/-- The explicit integral solves both components of the closed form. -/
theorem cauchySecond_solves_closed_form {f g : ℂ × ℂ → ℂ} {kf kg : Set ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hkf : IsCompact kf) (hkg : IsCompact kg)
    (hfk : ∀ z w, w ∉ kf → f (z, w) = 0)
    (hgk : ∀ z w, w ∉ kg → g (z, w) = 0)
    (hclosed : IsDbarClosed f g) :
    ContDiff ℝ ∞ (cauchySecond g) ∧
      (∀ q, dbarFirst (cauchySecond g) q = f q) ∧
      ∀ q, dbarSecond (cauchySecond g) q = g q := by
  refine ⟨contDiff_cauchySecond hg hkg hgk, ?_, ?_⟩
  · intro q
    rw [dbarFirst_cauchySecond (hg.of_le (by simp)) hkg hgk]
    have he : dbarFirst g = dbarSecond f := funext hclosed
    rw [he]
    exact cauchySecond_dbarSecond (hf.of_le (by simp)) hkf hfk q
  · exact dbarSecond_cauchySecond (hg.of_le (by simp)) hkg hgk

/-- A compact support in the full space projects to a genuine common compact
support for all slices in the integrated coordinate. -/
theorem exists_compact_second_support {f : ℂ × ℂ → ℂ}
    (hf : HasCompactSupport f) :
    ∃ k : Set ℂ, IsCompact k ∧ ∀ z w, w ∉ k → f (z, w) = 0 := by
  refine ⟨Prod.snd '' tsupport f, hf.image continuous_snd, ?_⟩
  intro z w hw
  by_contra hn
  exact hw ⟨(z, w), subset_tsupport f hn, rfl⟩

/-- Compactly supported smooth closed `(0,1)` forms on `ℂ²` have an actual
smooth primitive, witnessed by the convergent partial Cauchy–Green integral. -/
theorem exists_smooth_primitive_of_compact_support {f g : ℂ × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g)
    (hclosed : IsDbarClosed f g) :
    ∃ u : ℂ × ℂ → ℂ, ContDiff ℝ ∞ u ∧
      (∀ q, dbarFirst u q = f q) ∧ ∀ q, dbarSecond u q = g q := by
  obtain ⟨kf, hkf, hfk⟩ := exists_compact_second_support hcf
  obtain ⟨kg, hkg, hgk⟩ := exists_compact_second_support hcg
  exact ⟨cauchySecond g,
    cauchySecond_solves_closed_form hf hg hkf hkg hfk hgk hclosed⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
