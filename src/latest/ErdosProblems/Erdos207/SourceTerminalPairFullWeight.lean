/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceFullRootWeight

/-! # The order-four full-weight saving from source condition WS3 -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.terminal_pair_full_remainder_weight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W 4 F y z)
    (T : TripleOn V) (P : VortexPairOn V) {E : TripleSystemOn V}
    (hE : E ∈ W.terminalPairExtensions F T P) :
    setWeight (vortexTripleWeight W 1) (E \ {T}) = 1 / W.terminalSize := by
  obtain ⟨hEF, hTE, D, hDE, hlevel, _hpair⟩ :=
    (W.mem_terminalPairExtensions_iff F T P E).mp hE
  have hcard : (E.erase T).card = 1 := by
    rw [card_erase_of_mem hTE, (h.uniform E hEF).1]
  have herase : E.erase T = {D} :=
    eq_of_subset_of_card_le (singleton_subset_iff.mpr hDE) (by simpa using hcard.le)
      |>.symm
  simp only [sdiff_singleton_eq_erase, herase, setWeight, prod_singleton,
    vortexTripleWeight, hlevel, Vortex.terminalSize]

theorem SourceVortexWellSpread.terminal_pair_full_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W 4 F y z)
    (T : TripleOn V) (P : VortexPairOn V) (hPT : ¬ P.1 ⊆ T.1) :
    (∑ E ∈ W.terminalPairExtensions F T P,
      setWeight (vortexTripleWeight W 1) (E \ {T})) ≤ z / W.terminalSize := by
  calc
    _ = ∑ _E ∈ W.terminalPairExtensions F T P, (1 : ℝ≥0) / W.terminalSize := by
      apply sum_congr rfl
      intro E hE
      exact h.terminal_pair_full_remainder_weight T P hE
    _ = ((W.terminalPairExtensions F T P).card : ℝ≥0) / W.terminalSize := by
      simp [div_eq_mul_inv]
    _ ≤ _ := by
      gcongr
      exact h.order_four_pair rfl T P hPT

end

end Erdos207
