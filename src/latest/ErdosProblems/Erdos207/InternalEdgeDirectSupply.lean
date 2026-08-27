/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeTerminalRootSuccess

/-!
# Retrospective internal success from direct extension supplies

The terminal-success argument does not intrinsically need full iteration
typicality.  It only uses typicality once, to manufacture a reserve whose
two spokes occur often enough for every scheduled edge.  This file exposes
the sharper interface with those one-edge extension counts as direct
hypotheses.  It is the form used after the preliminary cover, where the
available family is state-dependent.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Direct-supply form of the raw scheduled internal law.  A terminal rooted
cap still rules out every remembered low-candidate failure. -/
theorem exists_scheduledOuterEdge_rawLaw_terminalRootSuccess_of_directSupply
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A P0 : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell)
    (E : Finset (Sym2 V))
    (hE : E ⊆ internalOuterEdges G (W.U i.succ))
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (r : ℝ≥0) (hr : r ≤ 1)
    (a D d R k : ℕ) (hD : 0 < D)
    (hsupply : ∀ e ∈ E,
      let S := iterationExtensionVertices A
        (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
      ((a + D : ℕ) : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * S.card / 4)
    (hsmall :
      ∑ e ∈ E,
        (let S := iterationExtensionVertices A
            (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ);
          Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * S.card) / 4)) < 1)
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (hincidence : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    (hscalar : 4 * d + R * k ≤ a) :
    ∃ bits : Sym2 V → Bool,
      let S : Sym2 V → Finset V := fun e ↦
        iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
      let hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := fun e he ↦
        out_fst_ne_snd_of_mem_graphEdges
          (internalOuterEdges_subset_graphEdges G (W.U i.succ)
            (hE (by simpa only [Finset.mem_toList] using he)))
      let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) bits S
        E.toList hne D P0
      L.SupportedOn (fun z ↦
        InternalEdgeProcessInvariant F P0 E.toList E.toList.length z ∧
        z.chosen ⊆ P0 ∪ A ∧
        NewTrianglesUseScheduledOuterEdges
          (W.U i.succ) E P0 z.chosen ∧
        InternalEdgeFailureCertificate F G (W.U i.succ) bits S E.toList
          hne D E.toList.length z) ∧
      (∀ z, 0 < L.mass z → RootedActiveCapsGood F z.chosen R →
        z.failed = false ∧
          ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      ∀ Q : TripleSystemOn V,
        L.probability (fun z ↦ Q ⊆ z.chosen \ P0) ≤
          ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hedge : ∀ e ∈ E, e ∈ graphEdges G := by
    intro e he
    exact internalOuterEdges_subset_graphEdges G (W.U i.succ) (hE he)
  have houter : ∀ e ∈ E,
      e.out.1 ∉ W.U i.succ ∧ e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp (hE he)).2
  obtain ⟨bits, hbits⟩ :=
    exists_reserve_realization_with_extension_supplies htri i E
      (fun e : Sym2 V ↦ e.out.1) (fun e : Sym2 V ↦ e.out.2)
      (fun e he ↦ out_fst_ne_snd_of_mem_graphEdges (hedge e he))
      (fun e he ↦ (houter e he).1) (fun e he ↦ (houter e he).2)
      r hr (fun _e ↦ a + D) (fun e he ↦ hsupply e he) hsmall
  have hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := by
    intro e he
    exact out_fst_ne_snd_of_mem_graphEdges
      (hedge e (by simpa only [Finset.mem_toList] using he))
  have hu : ∀ e, e ∈ E.toList → e.out.1 ∉ W.U i.succ := by
    intro e he
    exact (houter e (by simpa only [Finset.mem_toList] using he)).1
  have hv : ∀ e, e ∈ E.toList → e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (houter e (by simpa only [Finset.mem_toList] using he)).2
  have hSU : ∀ e, e ∈ E.toList → S e ⊆ W.U i.succ := by
    intro e _he
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hAactive : ∀ e (he : e ∈ E.toList)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G (W.U i.succ) (S e)
        e.out.1 e.out.2 bits →
      internalEdgeTriangle e (hne e he) w ∈ A := by
    intro e he w hw
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (hne e he) (hu e he) (hv e he)
      (mem_activeReserveWedgeVertices_iff.mp hw).1
  have hAplain : ∀ e (he : e ∈ E.toList) (w : V), ∀ hw : w ∈ S e,
      let w' : ThirdVertex e.out.1 e.out.2 :=
        ⟨w, fun h ↦ (hu e he) (h ▸ hSU e he hw),
          fun h ↦ (hv e he) (h ▸ hSU e he hw)⟩
      thirdVertexTriple (hne e he) w' ∈ A := by
    intro e he w hw
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (hne e he) (hu e he) (hv e he) hw
  let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) bits S
    E.toList hne D P0
  have hinv := internalEdgeGreedyProcessLaw_supported_processInvariant
    F G (W.U i.succ) bits S E.toList hne D P0
  have hambient := internalEdgeGreedyProcessLaw_supported_ambient
    F G (W.U i.succ) bits S E.toList hne D P0 A hAactive
  have huseList := internalEdgeGreedyProcessLaw_supported_usesScheduledOuterEdges
    F G (W.U i.succ) bits S E.toList hne hSU D P0
  have hElist : E.toList.toFinset = E := by
    ext e
    simp
  have huse : L.SupportedOn (fun z ↦
      NewTrianglesUseScheduledOuterEdges
        (W.U i.succ) E P0 z.chosen) := by
    intro z hz
    have hz' := huseList z hz
    simpa only [hElist] using hz'
  have hfailure := internalEdgeGreedyProcessLaw_supported_failureCertificate
    F G (W.U i.succ) bits S E.toList hne D hD P0
  have hall : L.SupportedOn (fun z ↦
      InternalEdgeProcessInvariant F P0 E.toList E.toList.length z ∧
      z.chosen ⊆ P0 ∪ A ∧
      NewTrianglesUseScheduledOuterEdges
        (W.U i.succ) E P0 z.chosen ∧
      InternalEdgeFailureCertificate F G (W.U i.succ) bits S E.toList
        hne D E.toList.length z) := by
    intro z hz
    exact ⟨hinv z hz, hambient z hz, huse z hz, hfailure z hz⟩
  refine ⟨bits, ?_⟩
  dsimp only
  refine ⟨hall, ?_, ?_⟩
  · intro z hz hroot
    have hzall := hall z hz
    have hfalse := internalEdge_terminal_notFailed_of_rootedCap
      hpacking0 havoid0 hinitial hfamily houter hincidence
        (fun e he ↦ Nat.le_of_lt (hbits e he)) hSU
        hAplain hscalar hzall.1 hzall.2.1 hzall.2.2.1 hzall.2.2.2 hroot
    refine ⟨hfalse, ?_⟩
    intro e he
    exact hzall.1.covers_mem hfalse e
      (by simpa only [Finset.mem_toList] using he)
  · intro Q
    exact internalEdgeGreedyProcess_probability_subset_newChosen_le_sharp
      F G (W.U i.succ) bits S E.toList hne E.nodup_toList hu hv hSU
        D hD P0 Q

end

end Erdos207
