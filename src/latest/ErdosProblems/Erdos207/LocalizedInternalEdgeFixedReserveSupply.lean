/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternalKernel
import ErdosProblems.Erdos207.LocalizedInternalEdgeTerminalRootSuccess
import ErdosProblems.Erdos207.LocalizedInternalEdgeTerminalNewRootSuccess
import ErdosProblems.Erdos207.LocalizedRootedThreatExtraction

/-!
# Raw internal cover from an already sampled reserve

The existing direct-supply theorem samples a fresh reserve.  In the KSSS
ordering the reserve has already been exposed before the preliminary phase.
This file isolates the deterministic second half: an existing bit
realization with enough active wedges supports the same retrospective
terminal-success certificate and sharp C4 estimate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem scheduledOuterEdge_rawLaw_terminalLocalizedRootSuccess_of_fixedReserve
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A P0 : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A)
    (E : Finset (Sym2 V)) (hE : E ⊆ internalOuterEdges G U)
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (bits : Sym2 V → Bool)
    (a D d R k : ℕ) (hD : 0 < D)
    (hsupply : ∀ e ∈ E,
      let S := iterationExtensionVertices A
        (SimpleGraph.edge e.out.1 e.out.2) U
      a + D ≤ (activeReserveWedgeVertices G U S
        e.out.1 e.out.2 bits).card)
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (hincidence : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    (hscalar : 4 * d + R * k ≤ a) :
    let S : Sym2 V → Finset V := fun e ↦
      iterationExtensionVertices A
        (SimpleGraph.edge e.out.1 e.out.2) U
    let hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := fun e he ↦
      out_fst_ne_snd_of_mem_graphEdges
        (internalOuterEdges_subset_graphEdges G U
          (hE (by simpa only [Finset.mem_toList] using he)))
    let L := internalEdgeGreedyProcessLaw F G U bits S
      E.toList hne D P0
    L.SupportedOn (fun z ↦
        InternalEdgeProcessInvariant F P0 E.toList E.toList.length z ∧
        z.chosen ⊆ P0 ∪ A ∧
        NewTrianglesUseScheduledOuterEdges U E P0 z.chosen ∧
        InternalEdgeFailureCertificate F G U bits S E.toList
          hne D E.toList.length z) ∧
      (∀ z, 0 < L.mass z → RootedActiveCapsGoodIn F z.chosen U R →
        z.failed = false ∧
          ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      ∀ Q : TripleSystemOn V,
        L.probability (fun z ↦ Q ⊆ z.chosen \ P0) ≤
          ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) U
  have hedge : ∀ e ∈ E, e ∈ graphEdges G := by
    intro e he
    exact internalOuterEdges_subset_graphEdges G U (hE he)
  have houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp (hE he)).2
  have hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := by
    intro e he
    exact out_fst_ne_snd_of_mem_graphEdges
      (hedge e (by simpa only [Finset.mem_toList] using he))
  have hu : ∀ e, e ∈ E.toList → e.out.1 ∉ U := by
    intro e he
    exact (houter e (by simpa only [Finset.mem_toList] using he)).1
  have hv : ∀ e, e ∈ E.toList → e.out.2 ∉ U := by
    intro e he
    exact (houter e (by simpa only [Finset.mem_toList] using he)).2
  have hSU : ∀ e, e ∈ E.toList → S e ⊆ U := by
    intro e _he
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge e.out.1 e.out.2) U
  have hAactive : ∀ e (he : e ∈ E.toList)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G U (S e)
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
  let L := internalEdgeGreedyProcessLaw F G U bits S
    E.toList hne D P0
  have hinv := internalEdgeGreedyProcessLaw_supported_processInvariant
    F G U bits S E.toList hne D P0
  have hambient := internalEdgeGreedyProcessLaw_supported_ambient
    F G U bits S E.toList hne D P0 A hAactive
  have huseList := internalEdgeGreedyProcessLaw_supported_usesScheduledOuterEdges
    F G U bits S E.toList hne hSU D P0
  have hElist : E.toList.toFinset = E := by
    ext e
    simp
  have huse : L.SupportedOn (fun z ↦
      NewTrianglesUseScheduledOuterEdges U E P0 z.chosen) := by
    intro z hz
    have hz' := huseList z hz
    simpa only [hElist] using hz'
  have hfailure := internalEdgeGreedyProcessLaw_supported_failureCertificate
    F G U bits S E.toList hne D hD P0
  have hall : L.SupportedOn (fun z ↦
      InternalEdgeProcessInvariant F P0 E.toList E.toList.length z ∧
      z.chosen ⊆ P0 ∪ A ∧
      NewTrianglesUseScheduledOuterEdges U E P0 z.chosen ∧
      InternalEdgeFailureCertificate F G U bits S E.toList
        hne D E.toList.length z) := by
    intro z hz
    exact ⟨hinv z hz, hambient z hz, huse z hz, hfailure z hz⟩
  refine ⟨hall, ?_, ?_⟩
  · intro z hz hroot
    have hzall := hall z hz
    have hrootScheduled : ∀ e ∈ E,
        (rootedActiveForbiddenConfigurationsIn F z.chosen
          e.out.1 e.out.2 (S e)).card ≤ R := by
      apply hroot.scheduled E S
      · intro e he
        exact hne e (by simpa only [Finset.mem_toList] using he)
      · intro e he
        exact hSU e (by simpa only [Finset.mem_toList] using he)
    have hfalse := internalEdge_terminal_notFailed_of_localizedRootedCap
      hpacking0 havoid0 hinitial hfamily houter hincidence hsupply hSU
        hAplain hscalar hzall.1 hzall.2.1 hzall.2.2.1 hzall.2.2.2
        hrootScheduled
    refine ⟨hfalse, ?_⟩
    intro e he
    exact hzall.1.covers_mem hfalse e
      (by simpa only [Finset.mem_toList] using he)
  · intro Q
    exact internalEdgeGreedyProcess_probability_subset_newChosen_le_sharp
      F G U bits S E.toList hne E.nodup_toList hu hv hSU D hD P0 Q

/-- Fixed-reserve raw law whose terminal implication charges only
configurations activated after `P0`. -/
theorem scheduledOuterEdge_rawLaw_terminalLocalizedNewRootSuccess_of_fixedReserve
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A Plegal P0 : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A)
    (E : Finset (Sym2 V)) (hE : E ⊆ internalOuterEdges G U)
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (havailable : ∀ T ∈ A, ¬ CompletesForbidden F Plegal T)
    (bits : Sym2 V → Bool)
    (a D d R k : ℕ) (hD : 0 < D)
    (hsupply : ∀ e ∈ E,
      let S := iterationExtensionVertices A
        (SimpleGraph.edge e.out.1 e.out.2) U
      a + D ≤ (activeReserveWedgeVertices G U S
        e.out.1 e.out.2 bits).card)
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (hincidence : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    (hscalar : 4 * d + R * k ≤ a) :
    let S : Sym2 V → Finset V := fun e ↦
      iterationExtensionVertices A
        (SimpleGraph.edge e.out.1 e.out.2) U
    let hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := fun e he ↦
      out_fst_ne_snd_of_mem_graphEdges
        (internalOuterEdges_subset_graphEdges G U
          (hE (by simpa only [Finset.mem_toList] using he)))
    let L := internalEdgeGreedyProcessLaw F G U bits S
      E.toList hne D P0
    L.SupportedOn (fun z ↦
        InternalEdgeProcessInvariant F P0 E.toList E.toList.length z ∧
        z.chosen ⊆ P0 ∪ A ∧
        NewTrianglesUseScheduledOuterEdges U E P0 z.chosen ∧
        InternalEdgeFailureCertificate F G U bits S E.toList
          hne D E.toList.length z) ∧
      (∀ z, 0 < L.mass z →
        NewRootedActiveCapsGoodIn F Plegal z.chosen A U R →
        z.failed = false ∧
          ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      ∀ Q : TripleSystemOn V,
        L.probability (fun z ↦ Q ⊆ z.chosen \ P0) ≤
          ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) U
  have hedge : ∀ e ∈ E, e ∈ graphEdges G := by
    intro e he
    exact internalOuterEdges_subset_graphEdges G U (hE he)
  have houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp (hE he)).2
  have hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := by
    intro e he
    exact out_fst_ne_snd_of_mem_graphEdges
      (hedge e (by simpa only [Finset.mem_toList] using he))
  have hu : ∀ e, e ∈ E.toList → e.out.1 ∉ U := by
    intro e he
    exact (houter e (by simpa only [Finset.mem_toList] using he)).1
  have hv : ∀ e, e ∈ E.toList → e.out.2 ∉ U := by
    intro e he
    exact (houter e (by simpa only [Finset.mem_toList] using he)).2
  have hSU : ∀ e, e ∈ E.toList → S e ⊆ U := by
    intro e _he
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge e.out.1 e.out.2) U
  have hAplain : ∀ e (he : e ∈ E.toList) (w : V), ∀ hw : w ∈ S e,
      let w' : ThirdVertex e.out.1 e.out.2 :=
        ⟨w, fun h ↦ (hu e he) (h ▸ hSU e he hw),
          fun h ↦ (hv e he) (h ▸ hSU e he hw)⟩
      thirdVertexTriple (hne e he) w' ∈ A := by
    intro e he w hw
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (hne e he) (hu e he) (hv e he) hw
  have hlocal :=
    scheduledOuterEdge_rawLaw_terminalLocalizedRootSuccess_of_fixedReserve
      htri E hE hpacking0 havoid0 hinitial bits a D d R k hD hsupply
        hfamily hincidence hscalar
  let L := internalEdgeGreedyProcessLaw F G U bits S E.toList hne D P0
  refine ⟨hlocal.1, ?_, hlocal.2.2⟩
  intro z hz hroot
  have hzall := hlocal.1 z hz
  have hfalse := internalEdge_terminal_notFailed_of_localizedNewRootedCap
    hpacking0 havoid0 hinitial havailable hfamily houter hincidence
      hsupply hSU hAplain hscalar hzall.1 hzall.2.1 hzall.2.2.1
      hzall.2.2.2 hroot
  refine ⟨hfalse, ?_⟩
  intro e he
  exact hzall.1.covers_mem hfalse e
    (by simpa only [Finset.mem_toList] using he)

end

end Erdos207
