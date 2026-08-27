/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeResidualEdges
import ErdosProblems.Erdos207.PreliminaryResidualInternalKernel

/-! # Raw internal outcomes provide the relative structural inputs without a success assumption -/

namespace Erdos207

open Finset

noncomputable section

theorem NewTrianglesUseScheduledOuterEdges.remove_old
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P pre added : TripleSystemOn V}
    (hG : G ≤ leaveGraph P) (hdis : Disjoint P added) (hpre : pre ⊆ added)
    (huse : NewTrianglesUseScheduledOuterEdges U
      (preliminaryResidualInternalEdges G U (P ∪ pre)) (P ∪ pre) (P ∪ added)) :
    NewTrianglesUseScheduledOuterEdges U (preliminaryResidualInternalEdges G U pre) pre added := by
  have hschedule := preliminaryResidualInternalEdges_union_eq_of_le_leaveGraph (U := U) hG (hdis.mono_right hpre)
  intro T hT
  have hnew : T ∈ (P ∪ added) \ (P ∪ pre) := by
    have ht := mem_sdiff.mp hT
    refine mem_sdiff.mpr ⟨mem_union_right P ht.1, ?_⟩
    intro hold
    rcases mem_union.mp hold with hTP | hTpre
    · exact disjoint_left.mp hdis hTP ht.1
    · exact ht.2 hTpre
  obtain ⟨e, he, hne, w, hw, hTeq⟩ := huse T hnew
  exact ⟨e, hschedule ▸ he, hne, w, hw, hTeq⟩

theorem RawResidualInternalOutcomeGood.relative_added_structure
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Ω → SimpleGraph V} {A P0 : Ω → TripleSystemOn V}
    {bits : Ω → Sym2 V → Bool} {D R : ℕ} {ω : Ω} {z : InternalEdgeGreedyStateOn V}
    (hz : RawResidualInternalOutcomeGood W i F G A P0 bits D R ω z)
    (P pre : TripleSystemOn V) (hstart : P0 ω = P ∪ pre)
    (hpacking : IsPackingOn (P0 ω)) (havoid : AvoidsForbidden (P0 ω) F)
    (hdis : Disjoint P pre) (hG : G ω ≤ leaveGraph P) :
    let added := pre ∪ rawResidualInternalAdded P0 ω z
    rawResidualInternalAdded P0 ω z ⊆ A ω ∧ IsPackingOn (P ∪ added) ∧
      Disjoint P added ∧ Disjoint pre (rawResidualInternalAdded P0 ω z) ∧
      AvoidsForbidden (P ∪ added) F ∧
      NewTrianglesUseScheduledOuterEdges (W.U i.succ)
        (preliminaryResidualInternalEdges (G ω) (W.U i.succ) pre) pre added := by
  dsimp only
  have hsubset := hz.1.1.initial_subset
  have hunion : P ∪ (pre ∪ rawResidualInternalAdded P0 ω z) = z.chosen := by
    rw [← union_assoc, ← hstart]
    exact union_sdiff_of_subset hsubset
  have hnew : rawResidualInternalAdded P0 ω z ⊆ A ω := by
    intro T hT
    exact (mem_union.mp (hz.2.1 (mem_sdiff.mp hT).1)).resolve_left (mem_sdiff.mp hT).2
  have hdisnew : Disjoint (P0 ω) (rawResidualInternalAdded P0 ω z) := by
    exact disjoint_left.mpr (fun _ hT hnew ↦ (mem_sdiff.mp hnew).2 hT)
  have hPnew : Disjoint P (rawResidualInternalAdded P0 ω z) :=
    hdisnew.mono_left (hstart.symm ▸ subset_union_left)
  have hprenew : Disjoint pre (rawResidualInternalAdded P0 ω z) :=
    hdisnew.mono_left (hstart.symm ▸ subset_union_right)
  have hPadded : Disjoint P (pre ∪ rawResidualInternalAdded P0 ω z) := disjoint_union_right.mpr ⟨hdis, hPnew⟩
  refine ⟨hnew, hunion.symm ▸ hz.1.1.isPacking hpacking, hPadded, hprenew,
    hunion.symm ▸ hz.1.1.avoidsForbidden havoid, ?_⟩
  apply NewTrianglesUseScheduledOuterEdges.remove_old hG hPadded subset_union_left
  simpa only [hunion, ← hstart] using hz.2.2.1

theorem RawResidualInternalFiberGood.supported_relative_added_structure
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Ω → SimpleGraph V} {A P0 : Ω → TripleSystemOn V}
    {bits : Ω → Sym2 V → Bool} {D R : ℕ} {ω : Ω}
    (hgood : RawResidualInternalFiberGood W i F G A P0 bits D R ω)
    (P pre : TripleSystemOn V) (hstart : P0 ω = P ∪ pre)
    (hpacking : IsPackingOn (P0 ω)) (havoid : AvoidsForbidden (P0 ω) F)
    (hdis : Disjoint P pre) (hG : G ω ≤ leaveGraph P) :
    (rawResidualInternalKernel W i F G A P0 bits D ω).SupportedOn fun z ↦
      let added := pre ∪ rawResidualInternalAdded P0 ω z
      rawResidualInternalAdded P0 ω z ⊆ A ω ∧ IsPackingOn (P ∪ added) ∧
        Disjoint P added ∧ Disjoint pre (rawResidualInternalAdded P0 ω z) ∧
        AvoidsForbidden (P ∪ added) F ∧
        NewTrianglesUseScheduledOuterEdges (W.U i.succ)
          (preliminaryResidualInternalEdges (G ω) (W.U i.succ) pre) pre added := by
  intro z hz
  exact (hgood.supportedOn_outcome z hz).relative_added_structure P pre hstart hpacking havoid hdis hG

end

end Erdos207
