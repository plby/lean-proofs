import ErdosProblems.Erdos547.SeparatedRows

/-!
# Decreasing edge weights to prescribe anchor saturations exactly
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem AnchoredPair.mono_weights {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {w w' : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d)
    (hw : ∀ u v, w.weight u v ≤ w'.weight u v) : AnchoredPair σ τ w' c d :=
  ⟨h.adjacent, h.capacity, fun u ↦ (h.fits_left u).trans (hw c u),
    fun u ↦ (h.fits_right u).trans (hw d u),
    fun u ↦ (h.joint u).trans (max_le_max (hw c u) (hw d u))⟩

namespace EdgeWeights

def capScaleRows (w : EdgeWeights G) (l : V → ℝ) (hl : ∀ u, 0 ≤ l u)
    (t : V → ℝ) (ht : ∀ u, 0 ≤ t u) (ht1 : ∀ u, t u ≤ 1) : EdgeWeights G where
  weight u v := t u * min (w.weight u v) (l v)
  nonnegative u v := mul_nonneg (ht u) (le_min (w.nonnegative u v) (hl v))
  at_most_one u v :=
    ((mul_le_mul_of_nonneg_right (ht1 u) (le_min (w.nonnegative u v) (hl v))).trans_eq
      (one_mul _)).trans ((min_le_left _ _).trans (w.at_most_one u v))
  supported u v huv := by rw [w.supported u v huv, min_eq_left (hl v), mul_zero]

omit [Fintype V] in
theorem capScaleRows_le (w : EdgeWeights G) (l : V → ℝ) (hl : ∀ u, 0 ≤ l u)
    (t : V → ℝ) (ht : ∀ u, 0 ≤ t u) (ht1 : ∀ u, t u ≤ 1) (u v : V) :
    (w.capScaleRows l hl t ht ht1).weight u v ≤ w.weight u v :=
  ((mul_le_mul_of_nonneg_right (ht1 u) (le_min (w.nonnegative u v) (hl v))).trans_eq
    (one_mul _)).trans (min_le_left _ _)

theorem capScaleRows_saturation (w : EdgeWeights G) (l : V → ℝ) (hl : ∀ u, 0 ≤ l u)
    (t : V → ℝ) (ht : ∀ u, 0 ≤ t u) (ht1 : ∀ u, t u ≤ 1) (u : V) :
    (w.capScaleRows l hl t ht ht1).saturation l u = t u * w.saturation l u := by
  have hbound (v : V) : (w.capScaleRows l hl t ht ht1).weight u v ≤ l v :=
    ((mul_le_mul_of_nonneg_right (ht1 u) (le_min (w.nonnegative u v) (hl v))).trans_eq
      (one_mul _)).trans (min_le_right _ _)
  calc
    _ = ∑ v, (w.capScaleRows l hl t ht ht1).weight u v :=
      Finset.sum_congr rfl fun v _ ↦ min_eq_left (hbound v)
    _ = _ := by simp only [capScaleRows, ← Finset.mul_sum, saturation]

theorem exists_prescribed_saturation (w : EdgeWeights G) (l r : V → ℝ)
    (hl : ∀ u, 0 ≤ l u) (hr : ∀ u, 0 ≤ r u) (hbound : ∀ u, r u ≤ w.saturation l u) :
    ∃ w' : EdgeWeights G, (∀ u v, w'.weight u v ≤ w.weight u v) ∧
      ∀ u, w'.saturation l u = r u := by
  let t := fun u ↦ min (r u) (w.saturation l u) / w.saturation l u
  have ht (u : V) : 0 ≤ t u := capped_ratio_nonneg (hr u) (w.saturation_nonneg l hl u)
  have ht1 (u : V) : t u ≤ 1 := capped_ratio_le_one (w.saturation_nonneg l hl u)
  refine ⟨w.capScaleRows l hl t ht ht1, w.capScaleRows_le l hl t ht ht1, ?_⟩
  intro u
  rw [w.capScaleRows_saturation]
  change (min (r u) (w.saturation l u) / w.saturation l u) * w.saturation l u = _
  rw [capped_ratio_mul (hr u) (w.saturation_nonneg l hl u), min_eq_left (hbound u)]

theorem exists_two_prescribed_saturations (w : EdgeWeights G) (l : V → ℝ)
    (hl : ∀ u, 0 ≤ l u) {c d : V} (hcd : c ≠ d) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hcr : r ≤ w.saturation l c) (hds : s ≤ w.saturation l d) :
    ∃ w' : EdgeWeights G, (∀ u v, w'.weight u v ≤ w.weight u v) ∧
      w'.saturation l c = r ∧ w'.saturation l d = s := by
  classical
  let target := fun u ↦ if u = c then r else if u = d then s else w.saturation l u
  have ht (u : V) : 0 ≤ target u := by
    dsimp [target]
    split_ifs
    · exact hr
    · exact hs
    · exact w.saturation_nonneg l hl u
  have hb (u : V) : target u ≤ w.saturation l u := by
    dsimp [target]
    split_ifs with hc hd
    · simpa only [hc] using hcr
    · simpa only [hd] using hds
    · exact le_rfl
  obtain ⟨w', hw', htarget⟩ := w.exists_prescribed_saturation l target hl ht hb
  refine ⟨w', hw', ?_, ?_⟩
  · simpa only [target, ite_true] using htarget c
  · simpa only [target, if_neg (Ne.symm hcd), ite_true] using htarget d

end EdgeWeights

end Erdos547.DPRS

#print axioms Erdos547.DPRS.EdgeWeights.exists_two_prescribed_saturations
