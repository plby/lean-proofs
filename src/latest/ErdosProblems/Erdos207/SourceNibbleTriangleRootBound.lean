/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleMixedWeights

/-! # Empty and nonempty triangle-root cases of the local-degree moment bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceNibble_extension_zero_of_bad_triangle_root
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j j' : ℕ)
    (w p : ℝ≥0) (H : Finset (SourceNibbleCoordinate V))
    (hbad : T ∈ H.toLeft ∨ j' - j < H.toLeft.card) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H = 0 := by
  classical
  unfold extensionWeight
  apply sum_eq_zero
  intro x _hx
  apply if_neg
  intro hroot
  have hleft : H.toLeft ⊆ x.1.2 := (subset_disjSum.mp hroot).1
  have hm := sourceNibbleCode_data x.2
  rcases hbad with hT | hcard
  · have hnot := (mem_sdiff.mp (hm.2.2.1 (hleft hT))).2
    exact hnot (mem_singleton_self T)
  · have hle := card_le_card hleft
    rw [hm.2.2.2.1] at hle
    exact (not_lt_of_ge hle) hcard

theorem SourceVortexWellSpread.nibble_mixed_empty_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j' F y z) (T : TripleOn V)
    (j : ℕ) (hj : 4 ≤ j) (hjj : j ≤ j') (w p : ℝ≥0) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) ∅ ≤
      (((j' - j + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 3) * y) * w ^ (j' - j) *
        (W.terminalSize : ℝ≥0) ^ (j - 3)) * p ^ (3 * (j - 3)) := by
  rw [sourceNibble_extension_empty_eq W F T (fun E hE ↦ (h.uniform E hE).1)
    (fun E hE ↦ (h.uniform E hE).2) hj hjj]
  exact mul_le_mul_of_nonneg_right (h.nibble_singleton_omission_weight_le T j hj hjj w) zero_le

theorem SourceVortexWellSpread.nibble_mixed_triangle_root_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j' F y z) (T : TripleOn V)
    (j : ℕ) (hj : 4 ≤ j) (hjj : j ≤ j') (w p : ℝ≥0) (hp : p ≤ 1)
    (H : Finset (SourceNibbleCoordinate V)) (hH : H.toLeft.Nonempty) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H ≤
      ((j' - j - H.toLeft.card + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z) *
        w ^ (j' - j - H.toLeft.card) * (W.terminalSize : ℝ≥0) ^ (j - 4) := by
  classical
  by_cases hT : T ∈ H.toLeft
  · rw [sourceNibble_extension_zero_of_bad_triangle_root W F T j j' w p H (Or.inl hT)]
    exact zero_le
  by_cases hcard : H.toLeft.card ≤ j' - j
  · apply (sourceNibble_extension_le_root_omission W F T j j' w p hp H).trans
    simpa only [singleton_union] using
      h.nibble_nonempty_triangle_root_weight_le T H.toLeft j hj hjj hH hT hcard w
  · rw [sourceNibble_extension_zero_of_bad_triangle_root W F T j j' w p H (Or.inr (lt_of_not_ge hcard))]
    exact zero_le

end

end Erdos207
