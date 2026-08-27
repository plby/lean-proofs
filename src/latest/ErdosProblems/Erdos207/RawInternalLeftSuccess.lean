/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawResidualInternalStructure
import ErdosProblems.Erdos207.InternalEdgeLeftMomentSuccess
import ErdosProblems.Erdos207.SourceLeftCapsProbability

/-! # Actual raw-internal success, with prior failures kept in the probability budget -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem RawResidualInternalStructure.notFailed_of_leftCaps
    {Ω V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Ω → SimpleGraph V} {Γ : SimpleGraph V} {A P0 : Ω → TripleSystemOn V}
    {bits : Ω → Sym2 V → Bool} {threshold d leftCap : ℕ} {ω : Ω} {z : InternalEdgeGreedyStateOn V}
    (houtcome : RawResidualInternalStructure W i F G A P0 bits threshold ω z)
    (I D : TripleSystemOn V) (hclass : z.chosen = I ∪ D)
    (hpacking0 : IsPackingOn (P0 ω)) (havoid0 : AvoidsForbidden (P0 ω) F)
    (hbase : G ω ≤ Γ)
    (hlevel : ∀ T ∈ A ω, (W.prefix i.castSucc).level T = Fin.last i.val)
    (hinitial : ∀ T ∈ A ω, ¬ CompletesForbidden F I T)
    (hinitialPair : ∀ T ∈ A ω, TriangleAvoidsGraph (coveredGraph (P0 ω)) T)
    (hincidence : ∀ v : V,
      (scheduledEdgesAt (preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω)) v).card ≤ d)
    (hsupply : ∀ e ∈ preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω),
      4*d+leftCap+threshold ≤ (activeReserveWedgeVertices (G ω) (W.U i.succ)
        (residualInternalExtensionSet W i (A ω) e) e.out.1 e.out.2 (bits ω)).card)
    (hleft : SourceLeftCaps (W.prefix i.castSucc) F (W.U i.succ) Γ I D
      (reserveEdges (G ω) (W.U i.succ) (bits ω)) leftCap) :
    z.failed = false := by
  let E := preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω)
  have houter : ∀ e ∈ E, e.out.1 ∉ W.U i.succ ∧ e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges (G ω) (W.U i.succ) (P0 ω) he)).2
  apply internalEdge_terminal_notFailed_of_scheduled_left_cap (W.prefix i.castSucc)
    hclass (houtcome.1.1.isPacking hpacking0) (houtcome.1.1.avoidsForbidden havoid0) hbase houter
    (fun _ _ ↦ iterationExtensionVertices_subset _ _ _) _ hlevel hinitial hinitialPair
    hincidence houtcome.2.2.1 hsupply _ houtcome.2.2.2
  · intro e he w hw
    have heE : e ∈ E := by simpa only [mem_toList] using he
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (residualInternalEdgeNe (G ω) (W.U i.succ) (P0 ω) e he)
      (houter e heE).1 (houter e heE).2 hw
  · intro e he
    have heG := internalOuterEdges_subset_graphEdges (G ω) (W.U i.succ)
      (preliminaryResidualInternalEdges_subset_internalOuterEdges (G ω) (W.U i.succ) (P0 ω) he)
    have heΓ : e ∈ graphEdges Γ := by
      rw [mem_graphEdges_iff] at heG ⊢
      exact (SimpleGraph.edgeSet_subset_edgeSet.mpr hbase) heG
    exact_mod_cast hleft e heΓ

theorem FiniteLaw.rawResidualInternal_failure_probability_le
    {Ω V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V) (Γ : SimpleGraph V) (A P0 : Ω → TripleSystemOn V)
    (bits : Ω → Sym2 V → Bool) (threshold d leftCap : ℕ) (hthreshold : 0 < threshold)
    (initial : Ω → TripleSystemOn V) (later : Ω × InternalEdgeGreedyStateOn V → TripleSystemOn V)
    (Good : Ω → Prop) (priorError leftError : ℝ≥0)
    (hclass : (L.jointBind (rawResidualInternalKernel W i F G A P0 bits threshold)).SupportedOn
      fun z ↦ z.2.chosen = initial z.1 ∪ later z)
    (hpacking0 : ∀ ω, Good ω → IsPackingOn (P0 ω))
    (havoid0 : ∀ ω, Good ω → AvoidsForbidden (P0 ω) F)
    (hbase : ∀ ω, Good ω → G ω ≤ Γ)
    (hlevel : ∀ ω, Good ω → ∀ T ∈ A ω, (W.prefix i.castSucc).level T = Fin.last i.val)
    (hinitial : ∀ ω, Good ω → ∀ T ∈ A ω, ¬ CompletesForbidden F (initial ω) T)
    (hinitialPair : ∀ ω, Good ω → ∀ T ∈ A ω, TriangleAvoidsGraph (coveredGraph (P0 ω)) T)
    (hincidence : ∀ ω, Good ω → ∀ v : V,
      (scheduledEdgesAt (preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω)) v).card ≤ d)
    (hsupply : ∀ ω, Good ω → ∀ e ∈ preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω),
      4*d+leftCap+threshold ≤ (activeReserveWedgeVertices (G ω) (W.U i.succ)
        (residualInternalExtensionSet W i (A ω) e) e.out.1 e.out.2 (bits ω)).card)
    (hprior : L.probability (fun ω ↦ ¬ Good ω) ≤ priorError)
    (hleft : (L.jointBind (rawResidualInternalKernel W i F G A P0 bits threshold)).probability
      (fun z ↦ ¬ SourceLeftCaps (W.prefix i.castSucc) F (W.U i.succ) Γ (initial z.1) (later z)
        (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) leftCap) ≤ leftError) :
    (L.jointBind (rawResidualInternalKernel W i F G A P0 bits threshold)).probability
      (fun z ↦ z.2.failed = true) ≤ priorError+leftError := by
  let K := rawResidualInternalKernel W i F G A P0 bits threshold
  let joint := L.jointBind K
  let LeftGood := fun z : Ω × InternalEdgeGreedyStateOn V ↦
    SourceLeftCaps (W.prefix i.castSucc) F (W.U i.succ) Γ (initial z.1) (later z)
      (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) leftCap
  have hstruct : joint.SupportedOn fun z ↦
      RawResidualInternalStructure W i F G A P0 bits threshold z.1 z.2 ∧
      z.2.chosen = initial z.1 ∪ later z := by
    intro z hz
    have hmass : 0 < (K z.1).mass z.2 := ((L.jointBind_mass_pos_iff K z.1 z.2).mp hz).2
    exact ⟨rawResidualInternalKernel_supported_structure W i F G A P0 bits threshold hthreshold z.1 z.2 hmass,
      hclass z hz⟩
  calc
    _ ≤ joint.probability (fun z ↦ ¬ Good z.1 ∨ ¬ LeftGood z) := by
      apply joint.probability_mono_of_supported hstruct
      intro z hz hfailed
      by_contra hnot
      have hg : Good z.1 := by tauto
      have hl : LeftGood z := by tauto
      have hfalse := hz.1.notFailed_of_leftCaps (initial z.1) (later z) hz.2
        (hpacking0 z.1 hg) (havoid0 z.1 hg) (hbase z.1 hg) (hlevel z.1 hg)
        (hinitial z.1 hg) (hinitialPair z.1 hg) (hincidence z.1 hg) (hsupply z.1 hg) hl
      simp [hfailed] at hfalse
    _ ≤ joint.probability (fun z ↦ ¬ Good z.1) + joint.probability (fun z ↦ ¬ LeftGood z) :=
      joint.probability_or_le _ _
    _ ≤ _ := by
      have hprior' : joint.probability (fun z ↦ ¬ Good z.1) ≤ priorError := by
        rw [L.probability_jointBind_fst K (fun ω ↦ ¬ Good ω)]
        exact hprior
      exact add_le_add hprior' hleft

end

end Erdos207
