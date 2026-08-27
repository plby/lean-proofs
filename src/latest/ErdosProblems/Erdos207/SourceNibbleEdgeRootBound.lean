/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleEdgeFan

/-! # The edge-only rooted weight bound above order four -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.nibble_pair_omission_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j' F y z) (T T' : TripleOn V) (hne : T ≠ T')
    (hj' : 5 ≤ j') (j : ℕ) (w : ℝ≥0) :
    sourceRootOmissionWeight W F {T, T'} (j' - j) w ≤
      ((j' - j + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z) * w ^ (j' - j) *
        (W.terminalSize : ℝ≥0) ^ (j' - 5) / (W.terminalSize : ℝ≥0) ^ (j' - j) := by
  have hcard : ({T, T'} : TripleSystemOn V).card = 2 := by simp [hne]
  have hexp : vortexRootExponent j' ({T, T'} : TripleSystemOn V).card = 5 := by
    rw [hcard]
    unfold vortexRootExponent
    split_ifs with hbad
    · rcases hbad with hbad | hbad <;> omega
    · rfl
  have hbound := h.root_omission_weight_le (f := j' - j) {T, T'} (by simp) (by rw [hcard]; omega) w
  simpa only [hexp] using hbound

theorem sourceNibble_extension_zero_of_diag_root_edge
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j j' : ℕ)
    (w p : ℝ≥0) (H : Finset (SourceNibbleCoordinate V))
    (e : Sym2 V) (he : e ∈ H.toRight) (hdiag : e.IsDiag) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H = 0 := by
  classical
  unfold extensionWeight
  apply sum_eq_zero
  intro x _hx
  apply if_neg
  intro hroot
  obtain ⟨T', hT', _hremaining⟩ := sourceNibble_root_edge_witness x.2 hroot he
  have heT' := (mem_filter.mp (mem_erase.mp hT').2).2.1
  exact not_isDiag_of_mem_tripleEdgeFinset heT' hdiag

theorem SourceVortexWellSpread.nibble_mixed_edge_root_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j' F y z) (T : TripleOn V)
    (j : ℕ) (hj : 4 ≤ j) (hj' : 5 ≤ j') (hjj : j ≤ j') (w p : ℝ≥0) (hp : p ≤ 1)
    (H : Finset (SourceNibbleCoordinate V)) (hleft : H.toLeft = ∅)
    (e : Sym2 V) (he : e ∈ H.toRight) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H ≤
      ((j' - j + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z) * w ^ (j' - j) *
        (W.terminalSize : ℝ≥0) ^ (j - 4) := by
  classical
  by_cases hoff : ¬ e.IsDiag
  · let K : ℝ≥0 := ((j' - j + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z) * w ^ (j' - j)
    let n : ℝ≥0 := W.terminalSize
    have hn : 0 < n := by dsimp [n]; exact_mod_cast h.terminal_nonempty
    have hcount : (((sourceTerminalEdgeFan W e).erase T).card : ℝ≥0) ≤ n := by
      dsimp [n]
      exact_mod_cast (card_erase_le (s := sourceTerminalEdgeFan W e) (a := T)).trans (card_sourceTerminalEdgeFan_le W e hoff)
    apply (sourceNibble_extension_le_fan_omissions W F T j j' w p hp H hleft e he).trans
    calc
      _ ≤ ∑ _T' ∈ (sourceTerminalEdgeFan W e).erase T, K * n ^ (j' - 5) / n ^ (j' - j) := by
        apply sum_le_sum
        intro T' hT'
        exact h.nibble_pair_omission_weight_le T T' (mem_erase.mp hT').1.symm hj' j w
      _ = (((sourceTerminalEdgeFan W e).erase T).card : ℝ≥0) * (K * n ^ (j' - 5) / n ^ (j' - j)) := by simp
      _ ≤ n * (K * n ^ (j' - 5) / n ^ (j' - j)) := mul_le_mul_of_nonneg_right hcount zero_le
      _ = K * (n * (n ^ (j' - 5) / n ^ (j' - j))) := by ring
      _ = _ := by rw [sourceNibble_pair_fan_ratio n hn j j' hj hj' hjj]
  · rw [sourceNibble_extension_zero_of_diag_root_edge W F T j j' w p H e he (not_not.mp hoff)]
    exact zero_le

end

end Erdos207
