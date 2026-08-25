import Mathlib

/-!
# Ownership of a closed interval covered by two sets

A finite exceptional contact set cannot account for a missing point of a
closed owner.  Missing interior points would give an entire open interval
of exceptional contacts; closedness then supplies the original endpoints.
-/

open Set

namespace Puzzling139335.N4OuterPair

/-- A closed set covering a nondegenerate interval up to finitely many
contacts with another set contains the entire closed interval. -/
theorem closed_interval_subset_of_finite_other {A B : Set ℝ} {a b : ℝ}
    (hA : IsClosed A) (hcover : Icc a b ⊆ A ∪ B)
    (hB : (B ∩ Icc a b).Finite) (hab : a < b) : Icc a b ⊆ A := by
  have hinner : Ioo a b ⊆ A := by
    intro x hx
    by_contra hxA
    have hopen : IsOpen (Ioo a b \ A) := isOpen_Ioo.sdiff hA
    obtain ⟨u, v, huv, hsub⟩ := hopen.exists_Ioo_subset ⟨x, hx, hxA⟩
    have hfinite : (Ioo u v).Finite := hB.subset (by
      intro z hz
      have hz' := hsub hz
      have hzI : z ∈ Icc a b := Ioo_subset_Icc_self hz'.1
      exact ⟨(hcover hzI).resolve_left hz'.2, hzI⟩)
    exact Ioo_infinite huv hfinite
  rw [← closure_Ioo hab.ne]
  exact closure_minimal hinner hA

/-- In particular, at most one contact with the other set leaves the
entire closed interval in the closed owner. -/
theorem closed_interval_subset_of_subsingleton_other {A B : Set ℝ} {a b : ℝ}
    (hA : IsClosed A) (hcover : Icc a b ⊆ A ∪ B)
    (hB : (B ∩ Icc a b).Subsingleton) (hab : a < b) : Icc a b ⊆ A :=
  closed_interval_subset_of_finite_other hA hcover hB.finite hab

/-- The exceptional set may be known to be a subsingleton globally,
rather than only on the interval. -/
theorem closed_interval_subset_of_subsingleton_set {A B : Set ℝ} {a b : ℝ}
    (hA : IsClosed A) (hcover : Icc a b ⊆ A ∪ B)
    (hB : B.Subsingleton) (hab : a < b) : Icc a b ⊆ A :=
  closed_interval_subset_of_subsingleton_other hA hcover
    (hB.anti inter_subset_left) hab

/-- A cover of a nondegenerate real interval by two sets has at least one
contact set containing two distinct points. No closedness is needed. -/
theorem nontrivial_contacts_of_interval_cover {A B : Set ℝ} {a b : ℝ}
    (hcover : Icc a b ⊆ A ∪ B) (hab : a < b) :
    (A ∩ Icc a b).Nontrivial ∨ (B ∩ Icc a b).Nontrivial := by
  rcases (A ∩ Icc a b).subsingleton_or_nontrivial with hA | hA
  · rcases (B ∩ Icc a b).subsingleton_or_nontrivial with hB | hB
    · exfalso
      apply Icc_infinite hab
      apply (hA.finite.union hB.finite).subset
      intro x hx
      rcases hcover hx with hxA | hxB
      · exact Or.inl ⟨hxA, hx⟩
      · exact Or.inr ⟨hxB, hx⟩
    · exact Or.inr hB
  · exact Or.inl hA

end Puzzling139335.N4OuterPair
