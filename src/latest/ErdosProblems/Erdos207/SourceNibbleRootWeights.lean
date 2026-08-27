/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGeneralMomentWeights

/-! # Exact root exponents for mixed local-configuration moments -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceNibble_nonempty_triangle_root_exponent
    {V : Type*} [DecidableEq V] (T : TripleOn V) (H : TripleSystemOn V)
    (j j' : ℕ) (hj : 4 ≤ j) (hH : H.Nonempty) (hT : T ∉ H) (hcard : H.card ≤ j' - j)
    (hjj : j ≤ j') :
    vortexRootExponent j' (insert T H).card = H.card + 4 := by
  have hh := card_pos.mpr hH
  rw [card_insert_of_notMem hT]
  unfold vortexRootExponent
  split_ifs with hbad
  · rcases hbad with hbad | hbad <;> omega
  · omega

theorem sourceNibble_singleton_ratio
    (n : ℝ≥0) (hn : 0 < n) (j j' : ℕ) (hj : 4 ≤ j) (hjj : j ≤ j') :
    n ^ (j' - 3) / n ^ (j' - j) = n ^ (j - 3) := by
  have he : j' - 3 = (j' - j) + (j - 3) := by omega
  rw [he, pow_add, mul_div_cancel_left₀ _ (pow_ne_zero _ hn.ne')]

theorem sourceNibble_nonempty_triangle_root_ratio
    (n : ℝ≥0) (hn : 0 < n) (j j' h : ℕ)
    (hj : 4 ≤ j) (hjj : j ≤ j') (hh : h ≤ j' - j) :
    n ^ (j' - (h + 4)) / n ^ (j' - j - h) = n ^ (j - 4) := by
  have he : j' - (h + 4) = (j' - j - h) + (j - 4) := by omega
  rw [he, pow_add, mul_div_cancel_left₀ _ (pow_ne_zero _ hn.ne')]

theorem sourceNibble_pair_fan_ratio
    (n : ℝ≥0) (hn : 0 < n) (j j' : ℕ) (hj : 4 ≤ j) (hj' : 5 ≤ j') (hjj : j ≤ j') :
    n * (n ^ (j' - 5) / n ^ (j' - j)) = n ^ (j - 4) := by
  rw [← mul_div_assoc, ← pow_succ']
  have he : j' - 5 + 1 = (j' - j) + (j - 4) := by omega
  rw [he, pow_add, mul_div_cancel_left₀ _ (pow_ne_zero _ hn.ne')]

theorem SourceVortexWellSpread.nibble_singleton_omission_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j' F y z) (T : TripleOn V)
    (j : ℕ) (hj : 4 ≤ j) (hjj : j ≤ j') (w : ℝ≥0) :
    sourceRootOmissionWeight W F {T} (j' - j) w ≤
      ((j' - j + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 3) * y) * w ^ (j' - j) *
        (W.terminalSize : ℝ≥0) ^ (j - 3) := by
  have hbound := h.singleton_omission_weight_le (f := j' - j) T w
  rw [mul_div_assoc, sourceNibble_singleton_ratio _ (by exact_mod_cast h.terminal_nonempty) j j' hj hjj] at hbound
  exact hbound

theorem SourceVortexWellSpread.nibble_nonempty_triangle_root_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j' F y z) (T : TripleOn V) (H : TripleSystemOn V)
    (j : ℕ) (hj : 4 ≤ j) (hjj : j ≤ j') (hH : H.Nonempty) (hT : T ∉ H)
    (hcard : H.card ≤ j' - j) (w : ℝ≥0) :
    sourceRootOmissionWeight W F (insert T H) (j' - j - H.card) w ≤
      ((j' - j - H.card + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z) *
        w ^ (j' - j - H.card) * (W.terminalSize : ℝ≥0) ^ (j - 4) := by
  have hQcard : (insert T H).card ≤ j' - 2 := by rw [card_insert_of_notMem hT]; omega
  have hbound := h.root_omission_weight_le (f := j' - j - H.card)
    (insert T H) (insert_nonempty _ _) hQcard w
  rw [sourceNibble_nonempty_triangle_root_exponent T H j j' hj hH hT hcard hjj,
    mul_div_assoc, sourceNibble_nonempty_triangle_root_ratio _
      (by exact_mod_cast h.terminal_nonempty) j j' H.card hj hjj hcard] at hbound
  exact hbound

end

end Erdos207
