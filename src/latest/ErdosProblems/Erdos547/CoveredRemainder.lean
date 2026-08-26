import ErdosProblems.Erdos547.MatchingCombination

/-!
# Saturation in an unoccupied covered region
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem remainder_saturation_of_covered_region (w : EdgeWeights G) (d : V)
    (σ : SkewMatching G γ) (ν F : FractionalMatching G)
    (hF : ∀ u v, F.weight u v ≤ ν.weight u v) (U : Finset V)
    (hzero : ∀ u ∈ U, F.load u = 0)
    (hcover : ∀ u ∈ U, w.weight d u ≤ σ.load u + ν.load u) :
    w.degreeOn U d ≤
      (w.truncate (fun u ↦ σ.load u + F.load u)
        (fun u ↦ add_nonneg (σ.load_nonneg u) (F.load_nonneg u))).saturation
          (ν.sub F hF).load d + ∑ u ∈ U, σ.load u := by
  let w' := w.truncate (fun u ↦ σ.load u + F.load u)
    (fun u ↦ add_nonneg (σ.load_nonneg u) (F.load_nonneg u))
  have hpoint (u : V) (hu : u ∈ U) :
      w.weight d u ≤ min (w'.weight d u) ((ν.sub F hF).load u) + σ.load u := by
    have he : (ν.sub F hF).load u = ν.load u := by
      rw [FractionalMatching.sub_load, hzero u hu, sub_zero]
    change w.weight d u ≤ min (max 0 (w.weight d u - (σ.load u + F.load u))) _ + _
    rw [hzero u hu, add_zero, he]
    have hh : w.weight d u - σ.load u ≤
        min (max 0 (w.weight d u - σ.load u)) (ν.load u) :=
      le_min (le_max_right _ _) (by linarith [hcover u hu])
    linarith
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsum
  have hbound : (∑ u ∈ U, min (w'.weight d u) ((ν.sub F hF).load u)) ≤
      w'.saturation (ν.sub F hF).load d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun u _ _ ↦ le_min (w'.nonnegative d u) ((ν.sub F hF).load_nonneg u))
  exact hsum.trans (add_le_add hbound le_rfl)

theorem SkewMatching.IsSuballocation.sum_load_outside_le {σ : SkewMatching G γ}
    {τ : SkewMatching G δ} (h : τ.IsSuballocation σ) (U : Finset V)
    (hzero : ∀ u ∈ U, τ.load u = 0) :
    (∑ u ∈ U, σ.load u) ≤ σ.total - τ.total := by
  calc
    _ = ∑ u ∈ U, (σ.load u - τ.load u) := Finset.sum_congr rfl fun u hu ↦ by
      rw [hzero u hu, sub_zero]
    _ ≤ ∑ u, (σ.load u - τ.load u) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun u _ _ ↦ sub_nonneg.mpr (h.load_le u))
    _ = _ := by rw [Finset.sum_sub_distrib, σ.sum_load, τ.sum_load]

theorem exists_skew_in_covered_remainder (w : EdgeWeights G) (d : V)
    (σ τ : SkewMatching G δ) (hτ : τ.IsSuballocation σ) (ν F : FractionalMatching G)
    (hF : ∀ u v, F.weight u v ≤ ν.weight u v) (U : Finset V)
    (hFzero : ∀ u ∈ U, F.load u = 0) (hτzero : ∀ u ∈ U, τ.load u = 0)
    (hcover : ∀ u ∈ U, w.weight d u ≤ σ.load u + ν.load u)
    (a γ : ℝ) (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (hdegree : a + (σ.total - τ.total) ≤ w.degreeOn U d) :
    ∃ α : SkewMatching G γ, α.DominatedByFractional (ν.sub F hF) ∧
      α.Fits (w.truncate (fun u ↦ σ.load u + F.load u)
        (fun u ↦ add_nonneg (σ.load_nonneg u) (F.load_nonneg u))) d ∧ α.total = a := by
  have hs := remainder_saturation_of_covered_region w d σ ν F hF U hFzero hcover
  have hu := hτ.sum_load_outside_le U hτzero
  apply exists_skew_of_saturation_exact _ _ d γ hγ a ha
  linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_skew_in_covered_remainder
