/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternalKernel

/-! # Unconditional structural support of the actual raw internal kernel -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def RawResidualInternalStructure
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V) (A P0 : Ω → TripleSystemOn V)
    (bits : Ω → Sym2 V → Bool) (threshold : ℕ) (ω : Ω) (z : InternalEdgeGreedyStateOn V) : Prop :=
  let E := preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω)
  InternalEdgeProcessInvariant F (P0 ω) E.toList E.toList.length z ∧
    z.chosen ⊆ P0 ω ∪ A ω ∧
    NewTrianglesUseScheduledOuterEdges (W.U i.succ) E (P0 ω) z.chosen ∧
    InternalEdgeFailureCertificate F (G ω) (W.U i.succ) (bits ω)
      (residualInternalExtensionSet W i (A ω)) E.toList
      (residualInternalEdgeNe (G ω) (W.U i.succ) (P0 ω)) threshold E.toList.length z

theorem rawResidualInternalKernel_supported_structure
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V) (A P0 : Ω → TripleSystemOn V)
    (bits : Ω → Sym2 V → Bool) (threshold : ℕ) (hthreshold : 0 < threshold) (ω : Ω) :
    (rawResidualInternalKernel W i F G A P0 bits threshold ω).SupportedOn
      (RawResidualInternalStructure W i F G A P0 bits threshold ω) := by
  let E := preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω)
  let S := residualInternalExtensionSet W i (A ω)
  let hne := residualInternalEdgeNe (G ω) (W.U i.succ) (P0 ω)
  have houter : ∀ e ∈ E, e.out.1 ∉ W.U i.succ ∧ e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges (G ω) (W.U i.succ) (P0 ω) he)).2
  have hSU : ∀ e, e ∈ E.toList → S e ⊆ W.U i.succ := by
    intro e _
    exact iterationExtensionVertices_subset _ _ _
  have hAactive : ∀ e (he : e ∈ E.toList) (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices (G ω) (W.U i.succ) (S e) e.out.1 e.out.2 (bits ω) →
      internalEdgeTriangle e (hne e he) w ∈ A ω := by
    intro e he w hw
    have heE : e ∈ E := by simpa only [mem_toList] using he
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem (hne e he)
      (houter e heE).1 (houter e heE).2 (mem_activeReserveWedgeVertices_iff.mp hw).1
  have hinv := internalEdgeGreedyProcessLaw_supported_processInvariant
    F (G ω) (W.U i.succ) (bits ω) S E.toList hne threshold (P0 ω)
  have hambient := internalEdgeGreedyProcessLaw_supported_ambient
    F (G ω) (W.U i.succ) (bits ω) S E.toList hne threshold (P0 ω) (A ω) hAactive
  have huse := internalEdgeGreedyProcessLaw_supported_usesScheduledOuterEdges
    F (G ω) (W.U i.succ) (bits ω) S E.toList hne hSU threshold (P0 ω)
  have hfailure := internalEdgeGreedyProcessLaw_supported_failureCertificate
    F (G ω) (W.U i.succ) (bits ω) S E.toList hne threshold hthreshold (P0 ω)
  intro z hz
  refine ⟨hinv z hz, hambient z hz, ?_, hfailure z hz⟩
  have hElist : E.toList.toFinset = E := by ext e; simp
  simpa only [hElist] using huse z hz

theorem rawResidualInternalKernel_probability_subset_new_le
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V) (A P0 : Ω → TripleSystemOn V)
    (bits : Ω → Sym2 V → Bool) (threshold : ℕ) (hthreshold : 0 < threshold)
    (ω : Ω) (Q : TripleSystemOn V) :
    (rawResidualInternalKernel W i F G A P0 bits threshold ω).probability
      (fun z ↦ Q ⊆ rawResidualInternalAdded P0 ω z) ≤ (threshold : ℝ≥0)⁻¹^Q.card := by
  let E := preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω)
  have houter : ∀ e ∈ E.toList, e.out.1 ∉ W.U i.succ ∧ e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges (G ω) (W.U i.succ) (P0 ω)
        (by simpa only [mem_toList] using he))).2
  exact internalEdgeGreedyProcess_probability_subset_newChosen_le_sharp
    F (G ω) (W.U i.succ) (bits ω) (residualInternalExtensionSet W i (A ω)) E.toList
    (residualInternalEdgeNe (G ω) (W.U i.succ) (P0 ω)) E.nodup_toList
    (fun e he ↦ (houter e he).1) (fun e he ↦ (houter e he).2)
    (fun _ _ ↦ iterationExtensionVertices_subset _ _ _) threshold hthreshold (P0 ω) Q

theorem RawResidualInternalStructure.complete_internalCover
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Ω → SimpleGraph V} {A P0 : Ω → TripleSystemOn V}
    {bits : Ω → Sym2 V → Bool} {threshold : ℕ} {ω : Ω} {z : InternalEdgeGreedyStateOn V}
    (houtcome : RawResidualInternalStructure W i F G A P0 bits threshold ω z)
    (hnotFailed : z.failed = false) :
    GreedyReachable F (P0 ω) z.chosen ∧ z.chosen ⊆ P0 ω ∪ A ω ∧
      (z.chosen \ P0 ω).card ≤ (internalOuterEdges (G ω) (W.U i.succ)).card ∧
      ∀ e ∈ internalOuterEdges (G ω) (W.U i.succ), (coveredGraph z.chosen).Adj e.out.1 e.out.2 := by
  let E := preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω)
  have hinv := houtcome.1
  refine ⟨hinv.1, houtcome.2.1, ?_, ?_⟩
  · calc
      _ ≤ E.toList.length := hinv.2.1
      _ = E.card := by simp
      _ ≤ _ := card_le_card
        (preliminaryResidualInternalEdges_subset_internalOuterEdges (G ω) (W.U i.succ) (P0 ω))
  · intro e he
    by_cases hcovered : (coveredGraph (P0 ω)).Adj e.out.1 e.out.2
    · exact coveredGraph_mono hinv.1.initial_subset hcovered
    · apply hinv.covers_mem hnotFailed e
      rw [mem_toList]
      apply mem_inter.mpr
      refine ⟨he, mem_sdiff.mpr ⟨internalOuterEdges_subset_outerGraphEdges (G ω) (W.U i.succ) he, ?_⟩⟩
      intro heGraph
      exact hcovered (graph_adj_out_of_mem_graphEdges heGraph)

end

end Erdos207
