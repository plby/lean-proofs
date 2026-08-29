/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalEndpointFairCompletion
import ErdosProblems.Erdos599.SourceRootedPathSelection
import ErdosProblems.Erdos599.SingularSafeCompletedMachine

/-!
# Original-graph finite linkage extracted after endpoint fairness

Selection is made only after every auxiliary vertex has been completed.
It preserves exact source coverage by the same limiting reference at the
same club frontier. It does not discard vertices during the fair recursion.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint.StableState

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {Z : Set V}

/-- The selected paths are in the original graph, finite, disjoint, and
endpoint-clean. The full-reference source-cover condition is unchanged. -/
theorem exists_linkageProjection (S : StableState C Z) (hcomplete : S.carrier ⊆ S.completed) :
    ∃ P : Set Gamma.DPath,
      CardinalInduction.IsLinkageBetween Gamma (Gamma.source ∩ S.carrier) Gamma.target P ∧
      familyEdges P ⊆ RealEdges (Gamma := web C) Gamma.graph.Adj S.family ∧
      Gamma.vertexSet P ⊆ S.carrier ∧ #(Gamma.vertexSet P) ≤ kappa ∧
      Gamma.source ⊆ Gamma.initialSet P ∪ Gamma.initialSet
        (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier S.index) \
          referencePathsMeeting C.ladder.limitWarp (Gamma.vertexSet P)) := by
  let E := RealEdges (Gamma := web C) Gamma.graph.Adj S.family
  have hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2} := fun _ he ↦ he.2
  have hleft : Relator.LeftUnique fun x y ↦ (x, y) ∈ E :=
    fun _ _ _ hx hy ↦ (IsWarp.familyEdges_biUnique S.blueprint.isWarp).1 hx.1 hy.1
  have hvertices : ∀ e ∈ E, e.1 ∈ S.carrier ∧ e.2 ∈ S.carrier :=
    fun _ he ↦ familyEdges_subset_vertexSet_prod S.family he.1
  have hroots : ∀ a ∈ Gamma.source ∩ S.carrier, ¬HasIncoming E a := by
    rintro a ⟨ha, _haV⟩ ⟨x, hxa⟩
    exact S.blueprint.source_no_incoming ha ⟨x, hxa.1⟩
  have hreach : ∀ a ∈ Gamma.source ∩ S.carrier, ∃ b ∈ Gamma.target,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b := by
    rintro a ⟨_ha, haV⟩
    obtain ⟨b, hb, _haV', hab⟩ := hcomplete haV
    exact ⟨b, hb, hab⟩
  obtain ⟨P, hP, hPfin, hPI, hPT, hPE, hPV⟩ :=
    SourceRootedPathSelection.exists_finiteWarp hEadj hleft
      (A := Gamma.source ∩ S.carrier) Set.inter_subset_right hvertices hroots hreach
  refine ⟨P, ⟨hP, hPfin, hPI, hPT, ?_⟩, hPE, hPV,
    (Cardinal.mk_subtype_mono hPV).trans S.blueprint.card_vertices, ?_⟩
  · intro p hp
    obtain ⟨q, rfl⟩ := hPfin hp
    exact CardinalInduction.SingularSafeCompletedMachine.isPathBetween_of_normalized
      C.normalized Set.inter_subset_left q
      (hPI ▸ ⟨Sum.inl q, hp, rfl⟩) (hPT ⟨Sum.inl q, hp, rfl⟩)
  · intro a ha
    by_cases haV : a ∈ S.carrier
    · exact Or.inl (hPI ▸ ⟨ha, haV⟩)
    · rcases S.blueprint.covers_source ha with haInitial | haReference
      · exact False.elim (haV (initialSet_subset_vertexSet S.family haInitial))
      · right
        obtain ⟨p, hp, hpa⟩ := haReference
        refine ⟨p, ⟨hp.1, ?_⟩, hpa⟩
        rintro ⟨hpY, x, hxp, hxP⟩
        exact hp.2 ⟨hpY, x, hxp, hPV hxP⟩

#print axioms exists_linkageProjection

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint.StableState

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open Set Cardinal Order DirectedPath Ladder ColouredSafeEndpointBlueprint
open ColouredSafeEndpointBlueprint.StableState

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- The actual causal fair construction followed by original-graph
selection. Initialization and the cardinal induction premise remain explicit. -/
theorem exists_endpointFiniteLinkage
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa) (hsub : HasHereditarySubdivisionIncidence Gamma.graph)
    (S : StableState C (globalCarrier Gamma kappa hkappa hGamma seed hseed)) :
    ∃ (U : StableState C (globalCarrier Gamma kappa hkappa hGamma seed hseed))
      (P : Set Gamma.DPath), S.Extends U ∧
      CardinalInduction.IsLinkageBetween Gamma (Gamma.source ∩ U.carrier) Gamma.target P ∧
      Gamma.source ∩ S.carrier ⊆ Gamma.initialSet P ∧
      Gamma.vertexSet P ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      #(Gamma.vertexSet P) ≤ kappa ∧
      Gamma.source ⊆ Gamma.initialSet P ∪ Gamma.initialSet
        (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier U.index) \
          referencePathsMeeting C.ladder.limitWarp (Gamma.vertexSet P)) := by
  obtain ⟨U, hSU, hcomplete⟩ := exists_endpointFullyCompleted hkappa hGamma hseed C hC hext hsub S
  obtain ⟨P, hP, _hPE, hPV, hcard, hcover⟩ := U.exists_linkageProjection hcomplete
  refine ⟨U, P, hSU, hP, ?_, hPV.trans U.contained, hcard, hcover⟩
  rintro x ⟨hxA, hxS⟩
  exact hP.initialSet_eq ▸ ⟨hxA, hSU.vertices hxS⟩

#print axioms exists_endpointFiniteLinkage

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
