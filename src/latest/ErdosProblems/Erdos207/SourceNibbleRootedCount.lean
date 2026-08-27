/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleEdgeRootBound

/-! # Rooted witness counts when no old triangles remain selected -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceNibble_extension_zero_of_base_root_edge
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j j' : ℕ)
    (hpacking : ∀ E ∈ F, IsPackingOn E) (w p : ℝ≥0) (H : Finset (SourceNibbleCoordinate V))
    (e : Sym2 V) (he : e ∈ H.toRight) (heT : e ∈ tripleEdgeFinset T) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H = 0 := by
  classical
  unfold extensionWeight
  apply sum_eq_zero
  intro x _hx
  apply if_neg
  intro hroot
  obtain ⟨T', hT', hremaining⟩ := sourceNibble_root_edge_witness x.2 hroot he
  have hm := sourceNibbleCode_data x.2
  have hT'E : T' ∈ x.1.1 := (mem_sdiff.mp (mem_sdiff.mp hremaining).1).1
  have hdis := (hpacking x.1.1 hm.1).isTriangleDecomposition.pairwiseDisjoint_tripleEdgeFinset
    hm.2.1 hT'E (mem_erase.mp hT').1.symm
  exact disjoint_left.mp hdis heT (mem_filter.mp (mem_erase.mp hT').2).2.1

theorem sourceNibble_equal_orders_extension_le_count
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j : ℕ)
    (w p : ℝ≥0) (hp : p ≤ 1) (H : Finset (SourceNibbleCoordinate V)) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H ≤
      (((sourceNibbleCodes W F T j j).filter (fun x ↦ H ⊆ sourceNibbleCoordinates T x)).card : ℝ≥0) := by
  classical
  unfold extensionWeight
  rw [← Finset.sum_subtype (sourceNibbleCodes W F T j j)
    (p := fun x ↦ x ∈ sourceNibbleCodes W F T j j) (fun _ ↦ Iff.rfl)
    (fun x ↦ if H ⊆ sourceNibbleCoordinates T x then
      setWeight (sourceNibbleMixedWeight W w p) (sourceNibbleCoordinates T x \ H) else 0)]
  calc
    _ ≤ ∑ x ∈ sourceNibbleCodes W F T j j, if H ⊆ sourceNibbleCoordinates T x then (1 : ℝ≥0) else 0 := by
      apply sum_le_sum
      intro x hx
      by_cases hroot : H ⊆ sourceNibbleCoordinates T x
      · rw [if_pos hroot, if_pos hroot]
        have hempty : x.2 = ∅ := card_eq_zero.mp (by simpa only [Nat.sub_self] using (sourceNibbleCode_data hx).2.2.2.1)
        have hbound := sourceNibbleCoordinates_remainder_weight_le W w p hp T x H
        simpa only [hempty, empty_sdiff, setWeight, prod_empty] using hbound
      · simp only [if_neg hroot, le_refl]
    _ = _ := by rw [← sum_filter]; simp

theorem sourceNibble_equal_orders_rooted_card_le_terminal_pairs
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j : ℕ)
    (H : Finset (SourceNibbleCoordinate V)) (e : Sym2 V) (he : e ∈ H.toRight) (hoff : ¬ e.IsDiag) :
    ((sourceNibbleCodes W F T j j).filter (fun x ↦ H ⊆ sourceNibbleCoordinates T x)).card ≤
      (W.terminalPairExtensions F T ⟨e.toFinset, Sym2.card_toFinset_of_not_isDiag e hoff⟩).card := by
  classical
  apply card_le_card_of_injOn Prod.fst
  · intro x hx
    have hm := mem_filter.mp hx
    have hd := sourceNibbleCode_data hm.1
    obtain ⟨T', hT', hremaining⟩ := sourceNibble_root_edge_witness hm.1 hm.2 he
    have hfan := (mem_filter.mp (mem_erase.mp hT').2).2
    apply (W.mem_terminalPairExtensions_iff F T _ x.1).mpr
    refine ⟨hd.1, hd.2.1, T', ?_, hfan.2, ?_⟩
    · exact mem_erase.mpr ⟨(mem_erase.mp hT').1, (mem_sdiff.mp (mem_sdiff.mp hremaining).1).1⟩
    · exact (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T' hoff).mp hfan.1
  · intro x hx y hy heq
    have hxempty : x.2 = ∅ := card_eq_zero.mp (by
      simpa only [Nat.sub_self] using (sourceNibbleCode_data (mem_filter.mp hx).1).2.2.2.1)
    have hyempty : y.2 = ∅ := card_eq_zero.mp (by
      simpa only [Nat.sub_self] using (sourceNibbleCode_data (mem_filter.mp hy).1).2.2.2.1)
    exact Prod.ext heq (hxempty.trans hyempty.symm)

end

end Erdos207
