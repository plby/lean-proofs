/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleOrderFourBound
import ErdosProblems.Erdos207.SourceNibbleMomentCoefficient

/-! # The full source mixed maximum-weight estimate for local configurations -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace SourceVortexWellSpread

variable {V : Type*} [Fintype V] [DecidableEq V] {ell j' : ℕ}
  {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}

theorem nibble_mixed_empty_uniform_weight_le
    (h : SourceVortexWellSpread W j' F y z) (T : TripleOn V)
    (j : ℕ) (hj : 4 ≤ j) (hjj : j ≤ j') (w p : ℝ≥0) (hw : 1 ≤ w) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) ∅ ≤
      sourceNibbleMomentCoefficient ell j' w * y * p ^ (3 * (j - 3)) *
        (W.terminalSize : ℝ≥0) ^ (j - 3) := by
  apply (h.nibble_mixed_empty_weight_le T j hj hjj w p).trans
  have hc := sourceNibble_small_coefficient_le ell j' (j' - j) (j' - 3)
    (Nat.sub_le _ _) (by omega) w y hw
  calc
    _ ≤ (sourceNibbleMomentCoefficient ell j' w * y * (W.terminalSize : ℝ≥0) ^ (j - 3)) *
        p ^ (3 * (j - 3)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc zero_le) zero_le
    _ = _ := by ring

theorem nibble_mixed_nonempty_uniform_weight_le
    (h : SourceVortexWellSpread W j' F y z) (T : TripleOn V)
    (j : ℕ) (hj : 4 ≤ j) (hjj : j ≤ j') (w p : ℝ≥0) (hw : 1 ≤ w) (hp : p ≤ 1)
    (H : Finset (SourceNibbleCoordinate V)) (hH : H.Nonempty) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H ≤
      sourceNibbleMomentCoefficient ell j' w * z * (W.terminalSize : ℝ≥0) ^ (j - 4) := by
  classical
  by_cases hleft : H.toLeft.Nonempty
  · apply (h.nibble_mixed_triangle_root_weight_le T j hj hjj w p hp H hleft).trans
    have hc := sourceNibble_small_coefficient_le ell j' (j' - j - H.toLeft.card) (j' - 2)
      (by omega) le_rfl w z hw
    exact mul_le_mul_of_nonneg_right hc zero_le
  · have hleft0 : H.toLeft = ∅ := not_nonempty_iff_eq_empty.mp hleft
    have hright : H.toRight.Nonempty := by
      by_contra hn
      have hr0 : H.toRight = ∅ := not_nonempty_iff_eq_empty.mp hn
      have hzero : H = ∅ := by
        rw [← toLeft_disjSum_toRight (u := H), hleft0, hr0]
        simp
      exact hH.ne_empty hzero
    obtain ⟨e, he⟩ := hright
    by_cases horder : j' = 4
    · subst j'
      have hj4 : j = 4 := by omega
      subst j
      apply (h.nibble_mixed_order_four_weight_le T w p hp H e he).trans
      simpa only [Nat.sub_self, pow_zero, mul_one, one_mul] using
        mul_le_mul_of_nonneg_right (sourceNibbleMomentCoefficient_one_le ell 4 w hw) (show 0 ≤ z from zero_le)
    · have hj' : 5 ≤ j' := by have := h.order; omega
      apply (h.nibble_mixed_edge_root_weight_le T j hj hj' hjj w p hp H hleft0 e he).trans
      have hc := sourceNibble_small_coefficient_le ell j' (j' - j) (j' - 2) (Nat.sub_le _ _) le_rfl w z hw
      exact mul_le_mul_of_nonneg_right hc zero_le

theorem nibble_mixed_hasExtensionBound
    (h : SourceVortexWellSpread W j' F y z) (T : TripleOn V)
    (j : ℕ) (hj : 4 ≤ j) (hjj : j ≤ j') (w p : ℝ≥0) (hw : 1 ≤ w) (hp : p ≤ 1)
    (hz : z ≤ y * p ^ (3 * (j - 3)) * W.terminalSize) :
    HasExtensionBound (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p)
      (sourceNibbleMomentCoefficient ell j' w * y * p ^ (3 * (j - 3)) *
        (W.terminalSize : ℝ≥0) ^ (j - 3)) := by
  intro H
  rcases H.eq_empty_or_nonempty with rfl | hH
  · exact h.nibble_mixed_empty_uniform_weight_le T j hj hjj w p hw
  · exact (h.nibble_mixed_nonempty_uniform_weight_le T j hj hjj w p hw hp H hH).trans
      (sourceNibble_nonempty_scale_le W.terminalSize (sourceNibbleMomentCoefficient ell j' w) y z p j hj hz)

end SourceVortexWellSpread

end

end Erdos207
