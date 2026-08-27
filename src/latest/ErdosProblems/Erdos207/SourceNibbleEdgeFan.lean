/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleMixedWeights
import ErdosProblems.Erdos207.TerminalOmissionOmittedRootTransfer
import ErdosProblems.Erdos207.VortexPairWeight
import ErdosProblems.Erdos207.PreliminaryEdgeSupply

/-! # Exposing a terminal triangle through a prescribed mixed-root edge -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceTerminalEdgeFan
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (e : Sym2 V) : Finset (TripleOn V) :=
  univ.filter (fun T ↦ e ∈ tripleEdgeFinset T ∧ W.level T = Fin.last ell)

theorem card_sourceTerminalEdgeFan_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (e : Sym2 V) (hoff : ¬ e.IsDiag) :
    (sourceTerminalEdgeFan W e).card ≤ W.terminalSize := by
  have hsub : sourceTerminalEdgeFan W e ⊆
      (universeTriplesContainingPair e.toFinset).filter (fun T ↦ W.level T = Fin.last ell) := by
    intro T hT
    have hm := (mem_filter.mp hT).2
    exact mem_filter.mpr ⟨mem_universeTriplesContainingPair_iff.mpr
      ((mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mp hm.1), hm.2⟩
  apply (card_le_card hsub).trans
  simpa only [VortexPairLevelTriple, Fintype.card_coe, Vortex.terminalSize] using card_vortexPairLevelTriple_le V W e.toFinset
    (Sym2.card_toFinset_of_not_isDiag e hoff) (Fin.last ell)

theorem sourceNibble_root_edge_witness
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T : TripleOn V}
    {x : TripleSystemOn V × TripleSystemOn V} (hx : x ∈ sourceNibbleCodes W F T j j')
    {H : Finset (SourceNibbleCoordinate V)} (hroot : H ⊆ sourceNibbleCoordinates T x)
    {e : Sym2 V} (he : e ∈ H.toRight) :
    ∃ T' ∈ (sourceTerminalEdgeFan W e).erase T, T' ∈ sourceNibbleRemaining T x := by
  have hright := (subset_disjSum.mp hroot).2 he
  obtain ⟨T', hT', heT'⟩ := mem_biUnion.mp hright
  have hne : T' ≠ T := by
    intro heq
    have hnot := (mem_sdiff.mp (mem_sdiff.mp hT').1).2
    exact hnot (by simp [heq])
  exact ⟨T', mem_erase.mpr ⟨hne, mem_filter.mpr ⟨mem_univ T', heT', (sourceNibbleCode_data hx).2.2.2.2 T' hT'⟩⟩, hT'⟩

theorem sourceNibble_extension_le_fan_omissions
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j j' : ℕ)
    (w p : ℝ≥0) (hp : p ≤ 1) (H : Finset (SourceNibbleCoordinate V)) (hleft : H.toLeft = ∅)
    (e : Sym2 V) (he : e ∈ H.toRight) :
    extensionWeight (fun x : sourceNibbleCodes W F T j j' ↦ sourceNibbleCoordinates T x.1)
      (sourceNibbleMixedWeight W w p) H ≤
      ∑ T' ∈ (sourceTerminalEdgeFan W e).erase T, sourceRootOmissionWeight W F {T, T'} (j' - j) w := by
  classical
  unfold extensionWeight
  rw [← Finset.sum_subtype (sourceNibbleCodes W F T j j')
    (p := fun x ↦ x ∈ sourceNibbleCodes W F T j j') (fun _ ↦ Iff.rfl)
    (fun x ↦ if H ⊆ sourceNibbleCoordinates T x then
      setWeight (sourceNibbleMixedWeight W w p) (sourceNibbleCoordinates T x \ H) else 0)]
  calc
    _ ≤ ∑ x ∈ sourceNibbleCodes W F T j j', ∑ T' ∈ (sourceTerminalEdgeFan W e).erase T,
        if T' ∈ sourceNibbleRemaining T x then setWeight (vortexTripleWeight W w) x.2 else 0 := by
      apply sum_le_sum
      intro x hx
      by_cases hroot : H ⊆ sourceNibbleCoordinates T x
      · rw [if_pos hroot]
        have hdrop := sourceNibbleCoordinates_remainder_weight_le W w p hp T x H
        rw [hleft, sdiff_empty] at hdrop
        apply hdrop.trans
        obtain ⟨T', hT', hremaining⟩ := sourceNibble_root_edge_witness hx hroot he
        have hsingle := single_le_sum (s := (sourceTerminalEdgeFan W e).erase T)
          (f := fun S ↦ if S ∈ sourceNibbleRemaining T x then setWeight (vortexTripleWeight W w) x.2 else 0)
          (a := T') (fun _ _ ↦ zero_le) hT'
        simpa only [if_pos hremaining] using hsingle
      · rw [if_neg hroot]
        exact zero_le
    _ = ∑ T' ∈ (sourceTerminalEdgeFan W e).erase T, ∑ x ∈ sourceNibbleCodes W F T j j',
        if T' ∈ sourceNibbleRemaining T x then setWeight (vortexTripleWeight W w) x.2 else 0 := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro T' _hT'
      have hbound := sourceRootOmission_omitted_root_weight_le W F {T} {T'} (j' - j) w
      simp only [singleton_subset_iff, singleton_union] at hbound
      rw [← sum_filter]
      exact hbound

end

end Erdos207
