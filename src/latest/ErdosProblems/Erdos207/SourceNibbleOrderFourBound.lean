/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleRootedCount

/-! # The order-four exceptional edge-root case, with the WS3 side condition -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.nibble_mixed_order_four_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W 4 F y z) (T : TripleOn V) (w p : ℝ≥0) (hp : p ≤ 1)
    (H : Finset (SourceNibbleCoordinate V)) (e : Sym2 V) (he : e ∈ H.toRight) :
    extensionWeight (fun x : sourceNibbleCodes W F T 4 4 ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H ≤ z := by
  classical
  by_cases hoff : ¬ e.IsDiag
  · by_cases hbase : e.toFinset ⊆ T.1
    · rw [sourceNibble_extension_zero_of_base_root_edge W F T 4 4
        (fun E hE ↦ (h.uniform E hE).2) w p H e he
        ((mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mpr hbase)]
      exact zero_le
    · have hcard : ((((sourceNibbleCodes W F T 4 4).filter
          (fun x ↦ H ⊆ sourceNibbleCoordinates T x)).card) : ℝ≥0) ≤
          ((W.terminalPairExtensions F T ⟨e.toFinset, Sym2.card_toFinset_of_not_isDiag e hoff⟩).card : ℝ≥0) := by
        exact_mod_cast sourceNibble_equal_orders_rooted_card_le_terminal_pairs W F T 4 H e he hoff
      exact (sourceNibble_equal_orders_extension_le_count W F T 4 w p hp H).trans
        (hcard.trans (h.order_four_pair rfl T ⟨e.toFinset, Sym2.card_toFinset_of_not_isDiag e hoff⟩ hbase))
  · rw [sourceNibble_extension_zero_of_diag_root_edge W F T 4 4 w p H e he (not_not.mp hoff)]
    exact zero_le

end

end Erdos207
