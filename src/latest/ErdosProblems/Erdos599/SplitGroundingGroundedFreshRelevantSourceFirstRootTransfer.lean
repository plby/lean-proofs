/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantTerminalSettlement
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# Moving a selected root to the source-first relevant frontier

For the canonical ladder, the limiting warp is self-roofed.  Consequently
every gadget decoded by a selected auxiliary path lies in the auxiliary
roof, and so does every endpoint of the stopped simultaneous relation.
A concrete relation root of any relevant boundary point can therefore be
cut at its first relevant-boundary hit.  The result is an actual rooted
member of the source-first frontier, not a detached rooted boundary point.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingErasedDecode GroundingErasedSwitchRelation
open GroundingSimultaneousDecode
open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev RootTransferInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev RootTransferIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev RootTransferControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev RootTransferFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev RootTransferEdges : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt
    (RootTransferIndexed (L := L) (hL := hL) (hground := hground)) S
    (RootTransferControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (RootTransferFrontier (L := L) (hL := hL) (S := S))

private theorem recorded_mem_limitWarp
    (hL : L.IsSplitKappaHindrance)
    {a : Ladder.Stage kappa} {p : Gamma.DPath}
    (hchosen : L.chosen a = some p) : p ∈ L.limitWarp := by
  exact (L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
    (by
      change a.1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 a.2)).1

private theorem familyEdge_endpoints_mem_roofRegion
    (hroof : Gamma.vertexSet L.limitWarp ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion)
    {x y : V}
    (hxy : (x, y) ∈
      (RootTransferInput (L := L) (hL := hL)).familyEdges) :
    x ∈ (RootTransferInput (L := L) (hL := hL)).roofRegion ∧
      y ∈ (RootTransferInput (L := L) (hL := hL)).roofRegion := by
  obtain ⟨p, hp, hxyP⟩ := hxy
  exact ⟨hroof ⟨p, hp, (p.edgeSet_subset_support_prod hxyP).1⟩,
    hroof ⟨p, hp, (p.edgeSet_subset_support_prod hxyP).2⟩⟩

private theorem finiteSource_mem_roofRegion
    (hroof : Gamma.vertexSet L.limitWarp ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion)
    {x : V}
    (hx : x ∈ (RootTransferInput (L := L) (hL := hL)).finiteSource) :
    x ∈ (RootTransferInput (L := L) (hL := hL)).roofRegion := by
  change x ∈ L.groundedFiniteTerminalSet at hx
  obtain ⟨a, _ha, p, hchosen, hterminal⟩ := hx
  exact hroof ⟨p, recorded_mem_limitWarp hL hchosen,
    Gamma.terminal_mem_support hterminal⟩

private theorem proxyPath_support_subset_roofRegion
    (hroof : Gamma.vertexSet L.limitWarp ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion)
    (i : L.groundedInfiniteRecords) :
    ((RootTransferInput (L := L) (hL := hL)).proxyPath i).support ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion := by
  obtain ⟨a, _ha, hchosen⟩ := i.2
  intro x hx
  exact hroof ⟨i.1, recorded_mem_limitWarp hL hchosen, hx⟩

private theorem targetMarker_mem_roofRegion
    (hroof : Gamma.vertexSet L.limitWarp ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion)
    {x : V}
    (hx : x ∈ (RootTransferInput (L := L) (hL := hL)).targetMarkers) :
    x ∈ (RootTransferInput (L := L) (hL := hL)).roofRegion := by
  obtain ⟨p, hp, hxp⟩ := hx.2
  exact hroof ⟨p, hp.1, hxp⟩

private theorem oldAllowed_mem_roofRegion
    (hroof : Gamma.vertexSet L.limitWarp ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion)
    {x : V}
    (hx : x ∈ (RootTransferInput (L := L) (hL := hL)).offLadder ∨
      x ∈ (RootTransferInput (L := L) (hL := hL)).finiteSource ∨
      x ∈ (RootTransferInput (L := L) (hL := hL)).targetMarkers) :
    x ∈ (RootTransferInput (L := L) (hL := hL)).roofRegion := by
  rcases hx with hx | hx | hx
  · exact hx.1
  · exact finiteSource_mem_roofRegion hroof hx
  · exact targetMarker_mem_roofRegion hroof hx

/-- Every original vertex represented by a gadget on a selected auxiliary
path lies in the auxiliary roof, provided the limiting ladder is self-roofed
there. -/
theorem splitGrounded_decodedVertexCarrier_subset_roofRegion_of_selfRoof
    (hroof : Gamma.vertexSet L.limitWarp ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion)
    (p : FinitePath
      (RootTransferInput (L := L) (hL := hL)).lambda.graph)
    (hpSource : p.start ∈
      (RootTransferInput (L := L) (hL := hL)).lambda.source) :
    (RootTransferInput (L := L) (hL := hL)).decodedVertexCarrier p ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion := by
  let J := RootTransferInput (L := L) (hL := hL)
  intro x hx
  simp only [PopularAuxiliary.Input.decodedVertexCarrier,
    Set.mem_iUnion] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  cases a with
  | old y =>
      have hxy : x = y := by
        simpa [PopularAuxiliary.Input.gadgetCarrier] using hxa
      subst x
      by_cases hstart : (PopularAuxiliary.Input.LambdaVertex.old y : J.LV) =
          p.start
      · have hsourceOld : PopularAuxiliary.Input.LambdaVertex.old y ∈
            J.lambda.source := hstart ▸ hpSource
        exact finiteSource_mem_roofRegion hroof
          ((J.mem_lambda_source_old y).1 hsourceOld)
      · obtain ⟨b, hba⟩ :=
          FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
            p ha hstart
        have hAdj : J.lambda.graph.Adj b (.old y) :=
          p.edgeSet_subset_adj hba
        cases b with
        | old z =>
            have h := (J.lambda_adj_old_old z y).1 hAdj
            exact oldAllowed_mem_roofRegion hroof
              (h.2.1.elim Or.inl (fun h ↦ Or.inr (Or.inr h)))
        | edge z w =>
            have h := (J.lambda_adj_edge_old z w y).1 hAdj
            rcases h.2 with rfl | hy
            · exact (familyEdge_endpoints_mem_roofRegion hroof h.1).1
            · exact oldAllowed_mem_roofRegion hroof
                (hy.1.elim Or.inl (fun h ↦ Or.inr (Or.inr h)))
        | proxy i =>
            have h := (J.lambda_adj_proxy_old i y).1 hAdj
            exact oldAllowed_mem_roofRegion hroof
              (h.1.elim Or.inl (fun h ↦ Or.inr (Or.inr h)))
  | edge y z =>
      have hEnds : x = y ∨ x = z := by
        simpa [PopularAuxiliary.Input.gadgetCarrier, eq_comm] using hxa
      have hnotStart :
          (PopularAuxiliary.Input.LambdaVertex.edge y z : J.LV) ≠ p.start := by
        intro heq
        exact J.not_mem_lambda_source_edge y z (heq ▸ hpSource)
      obtain ⟨b, hba⟩ :=
        FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          p ha hnotStart
      have hAdj : J.lambda.graph.Adj b (.edge y z) :=
        p.edgeSet_subset_adj hba
      have hyz : (y, z) ∈ J.familyEdges := by
        cases b with
        | old q => exact ((J.lambda_adj_old_edge q y z).1 hAdj).1
        | edge q r => exact ((J.lambda_adj_edge_edge q r y z).1 hAdj).2.1
        | proxy i => exact ((J.lambda_adj_proxy_edge i y z).1 hAdj).1
      exact hEnds.elim
        (fun h ↦ h ▸ (familyEdge_endpoints_mem_roofRegion hroof hyz).1)
        (fun h ↦ h ▸ (familyEdge_endpoints_mem_roofRegion hroof hyz).2)
  | proxy i =>
      have hnotIncoming :
          ¬ (PopularAuxiliary.Input.LambdaVertex.proxy i : J.LV) ≠ p.start := by
        intro hne
        obtain ⟨b, hba⟩ :=
          FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
            p ha hne
        exact J.lambda_not_adj_to_proxy b i (p.edgeSet_subset_adj hba)
      have hstart :
          (PopularAuxiliary.Input.LambdaVertex.proxy i : J.LV) = p.start :=
        not_not.mp hnotIncoming
      exact proxyPath_support_subset_roofRegion hroof i hxa

private theorem directionEdge_endpoints_mem_vertexSet
    {D : Digraph V} (Q : Alternating.AltPath D)
    {d : Alternating.Direction} {e : V × V}
    (he : e ∈ Q.directionEdges d) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hlQ, _hld, hel⟩ := he
  have hend := l.path.edgeSet_subset_support_prod hel
  cases Q with
  | trivial v => simp [Alternating.AltPath.links] at hlQ
  | finite Q =>
      obtain ⟨j, rfl⟩ := hlQ
      exact ⟨Set.mem_iUnion.2 ⟨j, hend.1⟩,
        Set.mem_iUnion.2 ⟨j, hend.2⟩⟩
  | infinite Q =>
      obtain ⟨j, rfl⟩ := hlQ
      exact ⟨Set.mem_iUnion.2 ⟨j, hend.1⟩,
        Set.mem_iUnion.2 ⟨j, hend.2⟩⟩

/-- Both endpoints of every edge of the actual stopped canonical switch lie
in the auxiliary roof.  For a residual edge this follows from membership in
the limiting ladder; for an inserted forward edge it follows from the exact
decoded carrier of the active selected route. -/
theorem splitGroundedFreshRelevant_switchedEdge_endpoints_mem_roofRegion
    (hroof : Gamma.vertexSet L.limitWarp ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion)
    {e : V × V}
    (he : e ∈ RootTransferEdges (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)) :
    e.1 ∈ (RootTransferInput (L := L) (hL := hL)).roofRegion ∧
      e.2 ∈ (RootTransferInput (L := L) (hL := hL)).roofRegion := by
  let U := RootTransferIndexed (L := L) (hL := hL) (hground := hground)
  let K := RootTransferControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let T := RootTransferFrontier (L := L) (hL := hL) (S := S)
  change e ∈ erasedSelectedSwitchedEdgesAt U S K T at he
  rcases he with hbase | hforward
  · exact familyEdge_endpoints_mem_roofRegion hroof hbase.1.1
  · have hforward' : e ∈ erasedSelectedDirectionEdgesAt U S K T .forward :=
      hforward.1
    simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at hforward'
    obtain ⟨c, hec⟩ := hforward'
    have hends := directionEdge_endpoints_mem_vertexSet
      (selectedErasedCompression U S K (chosenRequest c.1)).path hec
    have hcarrier :=
      GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
        U S K (chosenRequest c.1)
    have hpSource :
        (strongSelectedPath U S K (chosenRequest c.1)).start ∈
          (RootTransferInput (L := L) (hL := hL)).lambda.source :=
      (strongSelectedWarp U S K).starts_in_source
        ⟨chosenRequest c.1, rfl⟩
    exact ⟨
      splitGrounded_decodedVertexCarrier_subset_roofRegion_of_selfRoof
        hroof _ hpSource (hcarrier hends.1),
      splitGrounded_decodedVertexCarrier_subset_roofRegion_of_selfRoof
        hroof _ hpSource (hcarrier hends.2)⟩

private theorem source_subset_rootTransfer_roofRegion :
    Gamma.source ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion := by
  have hroof : Gamma.source ⊆ Gamma.roof
      (Gamma.terminalFrontier
        (RootTransferInput (L := L) (hL := hL)).ladder.paths) := by
    simpa only [RootTransferInput, splitGroundedPopularAuxiliaryInput,
      limitWarp] using
        hL.legal.roofsSourceAtStages (Ladder.finalStage kappa)
  intro x hx
  rw [PopularAuxiliary.Input.roofRegion,
    PopularAuxiliary.Input.terminalCut,
    PopularAuxiliary.Input.essentialLadder,
    Gamma.terminalFrontier_essentialWarpPart, Gamma.roof_essential]
  exact hroof hx

/-- A concrete root of an arbitrary relevant boundary point can be stopped
at its first relevant-boundary hit without losing its source or its actual
switched-relation path.  The first hit is, by construction, a member of the
source-first relevant frontier.  This is the ancestry-preserving replacement
for treating an unrelated rooted frontier point as progress. -/
theorem splitGroundedFreshRelevant_exists_sourceFirst_root_of_relevant_root
    (hroof : Gamma.vertexSet L.limitWarp ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion)
    {A : Set V} (hA : A ⊆ Gamma.source)
    {b : V} (hb : b ∈ L.splitGroundedRelevantBB hL.legal S.cut)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RootTransferEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a b) :
    ∃ t ∈ RootTransferFrontier (L := L) (hL := hL) (S := S),
      ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RootTransferEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t := by
  let U := RootTransferIndexed (L := L) (hL := hL) (hground := hground)
  let K := RootTransferControls (L := L) (hL := hL)
    (hground := hground) (hnotFresh := hnotFresh) (S := S)
  let T := RootTransferFrontier (L := L) (hL := hL) (S := S)
  let E := erasedSelectedSwitchedEdgesAt U S K T
  obtain ⟨P⟩ := exists_rootedPath_of_reflTransGen
    (Gamma := Gamma)
    (erasedSelectedSwitchedEdgesAt_subset_adj U S K T) hroot
  have hPStartRoof : P.path.start ∈
      (RootTransferInput (L := L) (hL := hL)).roofRegion :=
    source_subset_rootTransfer_roofRegion (hA P.start_mem)
  have hPSupport : P.path.support ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion := by
    intro x hx
    by_cases hxStart : x = P.path.start
    · exact hxStart ▸ hPStartRoof
    · obtain ⟨y, hyx⟩ :=
        FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          P.path hx hxStart
      exact
        (splitGroundedFreshRelevant_switchedEdge_endpoints_mem_roofRegion
          hroof (P.edgeSet_subset hyx)).2
  have hbSupport : b ∈ P.path.support := by
    simpa only [P.finish_eq] using P.path.finish_mem_support
  have hmeet : P.path.walk.Meets
      (L.splitGroundedRelevantBB hL.legal S.cut) :=
    ⟨b, hbSupport, hb⟩
  let q := P.path.firstHit
    (L.splitGroundedRelevantBB hL.legal S.cut) hmeet
  have hqStart : q.start = P.path.start := rfl
  have hqBoundary : q.finish ∈
      L.splitGroundedRelevantBB hL.legal S.cut :=
    P.path.firstHit_finish_mem
      (L.splitGroundedRelevantBB hL.legal S.cut) hmeet
  have hqEdges : q.edgeSet ⊆ E :=
    (P.path.firstHit_edgeSet_subset
      (L.splitGroundedRelevantBB hL.legal S.cut) hmeet).trans
        P.edgeSet_subset
  have hqReach : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) q.start q.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ q.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      exact hqEdges hxy
    · exact Alternating.Walk.reflTransGen_edgeSet q.walk
  refine ⟨q.finish, ?_, P.path.start, P.start_mem, ?_⟩
  · refine ⟨q, hA P.start_mem, rfl, ?_, hqBoundary, ?_⟩
    · exact
        (P.path.firstHit_support_subset
          (L.splitGroundedRelevantBB hL.legal S.cut) hmeet).trans hPSupport
    · intro x hx
      exact P.path.firstHit_no_mem_before
        (L.splitGroundedRelevantBB hL.legal S.cut) hmeet hx
  · simpa only [E, hqStart] using hqReach

/-- Self-roofing of the limiting ladder is exactly the geometric hypothesis
needed by the preceding root-transfer theorem. -/
theorem splitGroundedFreshRelevant_exists_sourceFirst_root_of_relevant_root_of_selfRoofing
    (hself : Gamma.vertexSet L.limitWarp ⊆
      Gamma.roof (Gamma.terminalFrontier L.limitWarp))
    {A : Set V} (hA : A ⊆ Gamma.source)
    {b : V} (hb : b ∈ L.splitGroundedRelevantBB hL.legal S.cut)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RootTransferEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a b) :
    ∃ t ∈ RootTransferFrontier (L := L) (hL := hL) (S := S),
      ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RootTransferEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t := by
  have hroof : Gamma.vertexSet L.limitWarp ⊆
      (RootTransferInput (L := L) (hL := hL)).roofRegion := by
    intro x hx
    rw [PopularAuxiliary.Input.roofRegion,
      PopularAuxiliary.Input.terminalCut,
      PopularAuxiliary.Input.essentialLadder,
      Gamma.terminalFrontier_essentialWarpPart, Gamma.roof_essential]
    exact hself hx
  exact splitGroundedFreshRelevant_exists_sourceFirst_root_of_relevant_root
    hroof hA hb hroot

/-- An old request exit is already a point of `CV`, hence of the relevant
boundary.  A root of that exit can therefore be cut at the first relevant
boundary point without changing either the source or the switched-relation
path.  This is the positive native-`T` outcome for an old control; edge
requests deliberately remain outside this theorem. -/
theorem splitGroundedFreshRelevant_exists_sourceFirst_root_of_oldRequest
    (hself : Gamma.vertexSet L.limitWarp ⊆
      Gamma.roof (Gamma.terminalFrontier L.limitWarp))
    {A : Set V} (hA : A ⊆ Gamma.source)
    (old : oldRequests (RootTransferInput (L := L) (hL := hL)) S.cut)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RootTransferEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a old.1) :
    ∃ t ∈ RootTransferFrontier (L := L) (hL := hL) (S := S),
      ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RootTransferEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t := by
  apply splitGroundedFreshRelevant_exists_sourceFirst_root_of_relevant_root_of_selfRoofing
    (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S) hself hA
  · exact L.splitGroundedCV_subset_relevantBB hL.legal S.cut old.2.1
  · exact hroot

/-- Exact control-facing form of
`splitGroundedFreshRelevant_exists_sourceFirst_root_of_oldRequest`.  It
consumes the equality saying that the control's chosen tagged request is an
old request and a root of the actual selected-route exit. -/
theorem splitGroundedFreshRelevant_exists_sourceFirst_root_of_oldControlExit
    (hself : Gamma.vertexSet L.limitWarp ⊆
      Gamma.roof (Gamma.terminalFrontier L.limitWarp))
    {A : Set V} (hA : A ⊆ Gamma.source)
    (c : ControlRequest (RootTransferInput (L := L) (hL := hL)) S.cut)
    (old : oldRequests (RootTransferInput (L := L) (hL := hL)) S.cut)
    (hc : chosenRequest c = Sum.inl old)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RootTransferEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a
          (requestExit (chosenRequest c))) :
    ∃ t ∈ RootTransferFrontier (L := L) (hL := hL) (S := S),
      ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RootTransferEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t := by
  apply splitGroundedFreshRelevant_exists_sourceFirst_root_of_oldRequest
    (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S) hself hA old
  simpa only [hc, requestExit] using hroot

/-- Canonical specialization: the ladder construction itself supplies the
self-roofing hypothesis, so the root transfer has no geometric provider. -/
theorem canonicalLadder_splitGroundedFreshRelevant_exists_sourceFirst_root_of_relevant_root
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : (canonicalLadder Gamma kappa preferred).IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa
      (canonicalLadder Gamma kappa preferred).phiGround)
    (hnotFresh : ¬ Stationary.IsStationaryBelow kappa
      (canonicalLadder Gamma kappa preferred).freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      ((canonicalLadder Gamma kappa preferred).splitGroundedPopularAuxiliaryIndexed
        hL hground))
    {A : Set V} (hA : A ⊆ Gamma.source)
    {b : V}
    (hb : b ∈ (canonicalLadder Gamma kappa preferred).splitGroundedRelevantBB
      hL.legal S.cut)
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RootTransferEdges
          (L := canonicalLadder Gamma kappa preferred)
          (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a b) :
    ∃ t ∈ RootTransferFrontier
        (L := canonicalLadder Gamma kappa preferred)
        (hL := hL) (S := S),
      ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RootTransferEdges
            (L := canonicalLadder Gamma kappa preferred)
            (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a t := by
  let L := canonicalLadder Gamma kappa preferred
  have hself : Gamma.vertexSet L.limitWarp ⊆
      Gamma.roof (Gamma.terminalFrontier L.limitWarp) := by
    simpa only [L, limitWarp] using
      (canonicalLadder_geometry (G := Gamma) preferred hNoEnter).selfRoofing
        (Ladder.finalStage kappa)
  exact splitGroundedFreshRelevant_exists_sourceFirst_root_of_relevant_root_of_selfRoofing
    (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S) hself hA hb hroot

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGrounded_decodedVertexCarrier_subset_roofRegion_of_selfRoof
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_switchedEdge_endpoints_mem_roofRegion
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_exists_sourceFirst_root_of_relevant_root
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_exists_sourceFirst_root_of_relevant_root_of_selfRoofing
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_exists_sourceFirst_root_of_oldRequest
#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshRelevant_exists_sourceFirst_root_of_oldControlExit
#print axioms
  Erdos599.DWeb.KappaLadder.canonicalLadder_splitGroundedFreshRelevant_exists_sourceFirst_root_of_relevant_root
