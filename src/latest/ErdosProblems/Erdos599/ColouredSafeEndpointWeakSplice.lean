/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointWeakSourceCoverage
import ErdosProblems.Erdos599.ColouredSafeConnectorSplice
import ErdosProblems.Erdos599.ColouredSafeGraphLift
import ErdosProblems.Erdos599.MarkedRayFiniteEdgeStability

/-!
# Inserting the actual endpoint-pruned weak switch

Reuse the graph-independent connector splice and exact real-family lift.
All companions are inserted, and exact initial, terminal, carrier and edge
identities retain source accounting. The actual protected-switch producer
then yields a small roofed source-covered replacement, preserving every
predicate-parametric marked-ray condition. Fixed-stage capture is explicit.
-/

noncomputable section

namespace Erdos599.ColouredSafeAmbientOccurrence.TouchedWeakSwitch

open Set Cardinal DirectedPath Alternating Blueprint
open ColouredSafeReverseReachability ColouredSafeGraphLift

universe u

variable {V : Type u} {Gamma D : DWeb V} {Y : Set Gamma.DPath} {s t : V}

/-- The real connector and every companion are inserted in any ambient
supergraph, retaining their literal vertices and real edges. -/
theorem exists_spliceIn_with_rayTrace
    {A : Occurrence Y s} (T : TouchedWeakSwitch A t)
    (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
    {W : Set D.DPath} (hW : D.IsWarp W) (hedge : (s, t) ∈ familyEdges W)
    (hne : s ≠ t)
    (hconnector : T.connector.support ∩ D.vertexSet W ⊆ {s, t})
    (hcompanions : Disjoint (Gamma.vertexSet T.companions) (D.vertexSet W)) :
    ∃ U : Set D.DPath, D.IsWarp U ∧
      D.initialSet U = D.initialSet W ∪ Gamma.initialSet T.companions ∧
      D.terminalFrontier U = D.terminalFrontier W ∪ Gamma.terminalFrontier T.companions ∧
      D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet T.paths ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges T.paths ∧
      T.connector.edgeSet ⊆ familyEdges U ∧
      ∀ r : Ray D.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray D.graph, Sum.inr r0 ∈ W ∧ r0.edgeSet \ {(s, t)} ⊆ r.edgeSet := by
  let K : Set D.DPath := liftFamily hAdj T.paths
  let p : FinitePath D.graph := T.connector.lift hAdj
  have hK : D.IsWarp K := liftFamily_isWarp hAdj T.isWarp
  have hKfinite : D.HasFiniteCharacter K := liftFamily_finiteCharacter hAdj T.finiteCharacter
  have hpK : (Sum.inl p : D.DPath) ∈ K := ⟨.inl T.connector, T.connector_mem, rfl⟩
  have hKfresh : D.vertexSet K ∩ D.vertexSet W ⊆ {s, t} := by
    rw [liftFamily_vertexSet]
    rintro x ⟨⟨q, hq, hxq⟩, hxW⟩
    by_cases hqConn : q = .inl T.connector
    · subst q
      exact hconnector ⟨hxq, hxW⟩
    · exact False.elim (Set.disjoint_left.mp hcompanions ⟨q, ⟨hq, hqConn⟩, hxq⟩ hxW)
  obtain ⟨U, hU, hUI, hUT, hUV, hUE, hpE, htrace⟩ :=
    hW.exists_connectorSplice_with_rayTrace hK hKfinite hedge p hpK
      T.connector_start T.connector_finish hne hKfresh
  have hCI : Gamma.initialSet T.companions = Gamma.initialSet T.paths \ {s} := by
    rw [companions, DWeb.IsWarp.initialSet_sdiff_singleton Gamma T.isWarp T.connector_mem,
      show Path.initial (.inl T.connector : Gamma.DPath) = s from T.connector_start]
  have hCT : Gamma.terminalFrontier T.companions = Gamma.terminalFrontier T.paths \ {t} := by
    rw [companions, DWeb.IsWarp.terminalFrontier_sdiff_singleton
      Gamma T.isWarp T.connector_mem rfl, T.connector_finish]
  refine ⟨U, hU, ?_, ?_, ?_, ?_, ?_, htrace⟩
  · simpa only [K, liftFamily_initialSet, ← hCI] using hUI
  · simpa only [K, liftFamily_terminalFrontier, ← hCT] using hUT
  · simpa only [K, liftFamily_vertexSet] using hUV
  · simpa only [K, liftFamily_edges] using hUE
  · have heq : p.edgeSet = T.connector.edgeSet :=
      path_edges_lift hAdj (.inl T.connector : Gamma.DPath)
    exact heq ▸ hpE

#print axioms exists_spliceIn_with_rayTrace

end Erdos599.ColouredSafeAmbientOccurrence.TouchedWeakSwitch

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence ColouredSafeHammock
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

universe u

variable {V : Type u} {Gamma D : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- An actual weak-edge replacement preserving the original full-reference
source condition, small roofed carrier, terminal legality and marked rays.
The uniform fixed-stage filter is not inferred from existential capture. -/
theorem endpoint_weak_exists_sourceCovered_splice
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hAdj : ∀ {x y}, Gamma.graph.Adj x y → D.graph.Adj x y)
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {W : Set D.DPath} (hW : D.IsWarp W) (hWcard : #(D.vertexSet W) ≤ kappa)
    (hWRoof : D.vertexSet W ⊆ Gamma.roof (C.ladder.frontier a))
    (hcover : Gamma.source ⊆ D.initialSet W ∪ Gamma.initialSet
      (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
        referencePathsMeeting C.ladder.limitWarp (D.vertexSet W)))
    {marked : V → V → Prop} (hmarked : D.InfinitelyManyMarkedEdges W marked)
    {s t : V} (hedge : (s, t) ∈ familyEdges W) (hne : s ≠ t)
    {extra : Occurrence (reference C.ladder.limitWarp s (some t)) s → Prop}
    (h : HasCard (reference C.ladder.limitWarp s (some t)) s (some t) extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (hnot : ¬HasCard (reference C.ladder.limitWarp s (some t)) s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa)) :
    ∃ A : Occurrence (reference C.ladder.limitWarp s (some t)) s,
      A ∈ goodRoutes (reference C.ladder.limitWarp s (some t)) s (some t) extra ∧
      ∃ hARoof : A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a),
        ∃ T : TouchedWeakSwitch (A.retypeEndpointStageReference C.legal hARoof) t,
          ∃ U : Set D.DPath, D.IsWarp U ∧
            D.initialSet U = D.initialSet W ∪ Gamma.initialSet T.companions ∧
            D.terminalFrontier U =
              D.terminalFrontier W ∪ Gamma.terminalFrontier T.companions ∧
            D.vertexSet U = D.vertexSet W ∪ Gamma.vertexSet T.paths ∧
            familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges T.paths ∧
            T.connector.edgeSet ⊆ familyEdges U ∧
            #(D.vertexSet U) ≤ kappa ∧
            D.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) ∧
            D.InfinitelyManyMarkedEdges U marked ∧
            D.terminalFrontier U ⊆ D.terminalFrontier W ∪ C.ladder.frontier a ∧
            Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
              (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
                referencePathsMeeting C.ladder.limitWarp (D.vertexSet U)) := by
  obtain ⟨A, hA, hARoof, T, hcomp, hconn, hTRoof, hEss⟩ :=
    C.endpoint_weak_hasCard_exists_essentialTouchedSwitch_avoiding ha hne h hroof hnot hWcard
  obtain ⟨U, hU, hUI, hUT, hUV, hUE, hpE, htrace⟩ :=
    T.exists_spliceIn_with_rayTrace hAdj hW hedge hne hconn hcomp
  have hUcard : #(D.vertexSet U) ≤ kappa := by
    rw [hUV]
    exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite
      hWcard (T.carrier_countable.le_aleph0.trans C.capacity_infinite))
  have hURoof : D.vertexSet U ⊆ Gamma.roof (C.ladder.frontier a) := by
    rw [hUV]
    exact Set.union_subset hWRoof hTRoof
  have hends : endpoints s (some t) ⊆ D.vertexSet W := by
    rw [endpoints_some, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact familyEdges_subset_vertexSet_prod W hedge
  have hsource : Gamma.source ⊆ D.initialSet U ∪ Gamma.initialSet
      (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a) \
        referencePathsMeeting C.ladder.limitWarp (D.vertexSet U)) := by
    apply ColouredSafeEndpointSourceCoverage.sourceCondition_of_endpointWeakSwitch
      C.legal hARoof T hTRoof hends hcover
    · rw [hUI]
      exact Set.subset_union_left
    · rw [hUI]
      exact Set.subset_union_right
    · rw [hUV]
  have hterm : D.terminalFrontier U ⊆ D.terminalFrontier W ∪ C.ladder.frontier a := by
    rw [hUT]
    apply Set.union_subset Set.subset_union_left
    intro x hx
    right
    have htOff : t ∉ Gamma.vertexSet (stageReference C.legal a s (some t)) := by
      intro ht
      exact Set.disjoint_left.mp ColouredSafeEndpointStageReference.vertexSet_disjoint_endpoints
        ht (Or.inr rfl)
    rw [T.companions_terminalFrontier htOff] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    rw [← ladderReference.terminalFrontier_eq C.legal]
    exact ⟨p, hEss hp, hpx⟩
  exact ⟨A, hA, hARoof, T, U, hU, hUI, hUT, hUV, hUE, hpE, hUcard, hURoof,
    DWeb.infinitelyManyMarkedEdges_of_rayTrace hmarked (Set.finite_singleton (s, t)) htrace,
    hterm, hsource⟩

#print axioms endpoint_weak_exists_sourceCovered_splice

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
