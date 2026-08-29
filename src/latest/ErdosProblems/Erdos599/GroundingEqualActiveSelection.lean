/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualFamilyThinning
import ErdosProblems.Erdos599.GroundingErasedCarrierRank

/-!
# Active thinning of the target-pure equal family

The equal branch must not simultaneously retain every decoded seed route:
distinct auxiliary gadgets can project to conflicting original vertices.
This file isolates the collision carrier exposed by one earlier auxiliary
path.  It is countable, and every later path whose decoded original carrier
meets the earlier decoded carrier meets this countable auxiliary carrier.
Consequently the source indices of paths conflicting with one fixed earlier
path are nonstationary.  This is the local input for the stationary active
selector; unlike the all-seed switch it remains valid in the presence of
hidden proxy sources.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingEqualActiveSelection

open DirectedPath Stationary
open GroundingSimultaneousDecode GroundingErasedCarrierRank
open PopularAuxiliary.Input

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Proxy gadgets whose represented limiting-ladder component is exposed by
one auxiliary path.  These gadgets are not contained in the ordinary full
ladder trace, so they must be added explicitly to the avoidance carrier. -/
def exposedProxyGadgets (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) : Set L.LV :=
  {z | ∃ i : I, z = .proxy i ∧ L.proxyPath i ∈ exposedLadderPaths L q}

theorem exposedProxyGadgets_finite
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (q : FinitePath L.lambda.graph) :
    (exposedProxyGadgets L q).Finite := by
  let badI : Set I := {i | L.proxyPath i ∈ exposedLadderPaths L q}
  have hbadI : badI.Finite :=
    Set.Finite.preimage hfaith.2.injOn (exposedLadderPaths_finite L q)
  apply (hbadI.image fun i => (LambdaVertex.proxy i : L.LV)).subset
  rintro z ⟨i, rfl, hi⟩
  exact ⟨i, hi, rfl⟩

/-- The complete auxiliary carrier which a later selected path must avoid.
It contains the earlier literal support, all old/edge gadgets on exposed
ladder components, and the otherwise hidden proxy gadgets naming those
components. -/
def collisionCarrier (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) : Set L.LV :=
  q.support ∪ metLadderTrace L q ∪ exposedProxyGadgets L q

theorem collisionCarrier_countable
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (q : FinitePath L.lambda.graph) :
    (collisionCarrier L q).Countable := by
  exact (q.support_finite.countable.union (metLadderTrace_countable L q)).union
    (exposedProxyGadgets_finite L hfaith q).countable

/-- Any overlap of decoded original-vertex carriers is visible in the later
path's auxiliary support against the fixed countable collision carrier of
the earlier path.  The proxy case uses faithfulness to turn an invisible
proxy-support contact into membership in the finite exposed-proxy set. -/
theorem support_meets_collisionCarrier_of_decodedCarrier_overlap
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (p q : FinitePath L.lambda.graph)
    (hpstart : p.start ∈ L.lambda.source)
    (hqstart : q.start ∈ L.lambda.source)
    (hoverlap : (L.decodedVertexCarrier p ∩
      L.decodedVertexCarrier q).Nonempty) :
    (p.support ∩ collisionCarrier L q).Nonempty := by
  obtain ⟨x, hxp, hxq⟩ := hoverlap
  simp only [decodedVertexCarrier, Set.mem_iUnion] at hxp
  obtain ⟨a, ha, hxa⟩ := hxp
  refine ⟨a, ha, ?_⟩
  cases a with
  | old y =>
      have hnonproxy : ∀ i : I,
          (LambdaVertex.old y : L.LV) ≠ LambdaVertex.proxy i :=
        fun _ h => by cases h
      rcases nonproxy_mem_support_or_metLadderTrace_of_carrier_overlap
          hfaith q p hqstart hpstart ha hnonproxy hxa hxq with hq | htrace
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr htrace)
  | edge y z =>
      have hnonproxy : ∀ i : I,
          (LambdaVertex.edge y z : L.LV) ≠ LambdaVertex.proxy i :=
        fun _ h => by cases h
      rcases nonproxy_mem_support_or_metLadderTrace_of_carrier_overlap
          hfaith q p hqstart hpstart ha hnonproxy hxa hxq with hq | htrace
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr htrace)
  | proxy i =>
      apply Or.inr
      refine ⟨i, rfl, ?_⟩
      apply L.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
        hfaith q hqstart (hfaith.1 i) hxq
      simpa [gadgetCarrier] using hxa

/-- Avoiding the complete auxiliary collision carrier of `q` prevents the
decoded original carrier from meeting any limiting-ladder component exposed
by `q`.  This includes the hidden starting-proxy case. -/
theorem decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (p q : FinitePath L.lambda.graph)
    (hpstart : p.start ∈ L.lambda.source)
    {Y : Gamma.DPath} (hY : Y ∈ exposedLadderPaths L q)
    (hdisj : Disjoint p.support (collisionCarrier L q)) :
    Disjoint (L.decodedVertexCarrier p) Y.support := by
  have hYL : Y ∈ L.ladder.paths := by
    rcases hY with hY | hY
    · exact hY.1
    · cases hstart : q.start with
      | old v => simp [exposedLadderPaths, hstart] at hY
      | edge u v => simp [exposedLadderPaths, hstart] at hY
      | proxy i =>
          have hEq : Y = L.proxyPath i := by
            simpa [exposedLadderPaths, hstart] using hY
          exact hEq.symm ▸ hfaith.1 i
  rw [Set.disjoint_left]
  intro x hxp hxY
  simp only [decodedVertexCarrier, Set.mem_iUnion] at hxp
  obtain ⟨a, ha, hxa⟩ := hxp
  rcases L.gadget_mem_ladderTrace_or_proxy_eq_of_mem_carrier_of_mem_support
      hfaith p hpstart ha hYL hxa hxY with haTrace | ⟨i, rfl, hiY⟩
  · exact Set.disjoint_left.1 hdisj ha (Or.inl (Or.inr
      ((mem_metLadderTrace_iff L q a).2 ⟨Y, hY, haTrace⟩)))
  · exact Set.disjoint_left.1 hdisj ha (Or.inr ⟨i, rfl, by
      simpa [hiY] using hY⟩)

/-- Members of an auxiliary warp whose decoded carrier meets that of one
fixed member. -/
def decodedCarrierCollisions
    (L : PopularAuxiliary.Input Gamma I) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S)
    (q : FinitePath L.lambda.graph) : Set (FinitePath L.lambda.graph) :=
  {p | p ∈ P.paths ∧
    (L.decodedVertexCarrier p ∩ L.decodedVertexCarrier q).Nonempty}

/-- Fixed-route decoded collisions remove only a nonstationary collection
of source indices from a stationary auxiliary warp. -/
theorem decodedCarrierCollisionIndices_nonstationary
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S)
    (q : FinitePath L.lambda.graph) (hqstart : q.start ∈ L.lambda.source) :
    ¬ Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U
        (decodedCarrierCollisions L P q)
        (fun {_p} hp => P.starts_in_source hp.1)) := by
  let meeting : Set (FinitePath L.lambda.graph) :=
    {p | p ∈ P.paths ∧ (p.support ∩ collisionCarrier L q).Nonempty}
  have hmeeting := P.initialIndices_meeting_nonstationary U
    (collisionCarrier_countable L hfaith q)
  intro hstationary
  apply hmeeting
  apply hstationary.mono
  rintro a ⟨p, hp, hpa⟩
  have hpstart : p.start ∈ L.lambda.source := P.starts_in_source hp.1
  have hpmeet : (p.support ∩ collisionCarrier L q).Nonempty :=
    support_meets_collisionCarrier_of_decodedCarrier_overlap
      L hfaith p q hpstart hqstart hp.2
  exact ⟨p, ⟨hp.1, hpmeet⟩, hpa⟩

/-! ## Route-level consequence of decoded-carrier disjointness -/

/-- The initial vertex chosen by the genuine lossless decoder is represented
by the source gadget of the auxiliary path, including the proxy-source case. -/
theorem decodeFinitePath_initial_mem_decodedVertexCarrier
    (L : PopularAuxiliary.Input Gamma I)
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (hfinish : p.finish ∈ L.lambda.target) :
    (L.decodeFinitePath p hstart hfinish).initial ∈
      L.decodedVertexCarrier p := by
  classical
  cases hchoice : L.chooseSourceEndpoint p hstart with
  | inl x =>
    rw [show L.decodeFinitePath p hstart hfinish =
        L.decodeFinitePathFromFinite p hstart x
          (L.chooseTargetEndpoint p hfinish) by
      simp [PopularAuxiliary.Input.decodeFinitePath, hchoice]]
    apply L.gadgetCarrier_subset_decodedVertexCarrier p p.start_mem_support
    rw [x.2.2]
    simp [PopularAuxiliary.Input.decodeFinitePathFromFinite,
      PopularAuxiliary.Input.gadgetCarrier]
  | inr i =>
    rw [show L.decodeFinitePath p hstart hfinish =
        L.decodeFinitePathFromProxy p hstart i
          (L.chooseTargetEndpoint p hfinish) by
      simp [PopularAuxiliary.Input.decodeFinitePath, hchoice]]
    apply L.gadgetCarrier_subset_decodedVertexCarrier p p.start_mem_support
    rw [i.2]
    let H : ∃ x, x ∈ (L.proxyPath i.1).support ∧
        PopularAuxiliary.Input.RunsFromTo x
          (L.chooseTargetEndpoint p hfinish).1
          (L.decodeWalkSteps p.walk) := by
      exact L.decodeWalkSteps_runs_from_eq_proxy p.walk i.2
        ((L.finish_old_gadget p
          (L.chooseTargetEndpoint p hfinish).2.2).2)
    change (Classical.choose H) ∈ L.gadgetCarrier (.proxy i.1)
    simpa [PopularAuxiliary.Input.gadgetCarrier] using
      (Classical.choose_spec H).1

/-- Every original vertex used by the canonical loop-erased compression of
a genuine decoded auxiliary path lies in that path's decoded carrier. -/
theorem decodeFinitePath_erasedCompression_vertexSet_subset
    (L : PopularAuxiliary.Input Gamma I)
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (hfinish : p.finish ∈ L.lambda.target) :
    (L.decodeFinitePath p hstart hfinish).erasedCompression.path.vertexSet ⊆
      L.decodedVertexCarrier p := by
  let T := L.decodeFinitePath p hstart hfinish
  let E := T.erasedCompression
  intro x hx
  change x ∈ E.path.vertexSet at hx
  cases hpath : E.path with
  | trivial v =>
      have hxv : x = v := by simpa [hpath] using hx
      have hv : v = T.initial := by
        have hi := E.initial_eq
        rw [hpath] at hi
        simpa using hi
      rw [hxv, hv]
      exact decodeFinitePath_initial_mem_decodedVertexCarrier
        L p hstart hfinish
  | finite Q =>
      rw [hpath] at hx
      change x ∈ Q.vertexSet at hx
      simp only [Alternating.FiniteTrace.vertexSet, Set.mem_iUnion] at hx
      obtain ⟨j, hxj⟩ := hx
      by_cases hxfinish : x = (Q.link j).path.finish
      · have hxstart : x ≠ (Q.link j).path.start := by
          rw [hxfinish]
          exact (Q.link j).nontrivial.symm
        obtain ⟨y, hyx⟩ :=
          Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
            (Q.link j).path hxj hxstart
        have hyxE : (y, x) ∈ E.path.edgeSet := by
          rw [hpath]
          exact Set.mem_iUnion.2 ⟨j, hyx⟩
        exact (L.decodedRouteEdge_endpoints_mem_decodedVertexCarrier p
          (PopularAuxiliary.Input.MicroTrace.erasedCompression_edgeSet_subset
            L T hyxE)).2
      · obtain ⟨y, hxy⟩ :=
          Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            (Q.link j).path hxj hxfinish
        have hxyE : (x, y) ∈ E.path.edgeSet := by
          rw [hpath]
          exact Set.mem_iUnion.2 ⟨j, hxy⟩
        exact (L.decodedRouteEdge_endpoints_mem_decodedVertexCarrier p
          (PopularAuxiliary.Input.MicroTrace.erasedCompression_edgeSet_subset
            L T hxyE)).1
  | infinite Q =>
      have hterminal := E.terminal_eq
      rw [hpath] at hterminal
      simp at hterminal

/-! ## The stationary greedy thinning -/

/-- A member of an auxiliary warp, with its membership proof retained so
that its inherited source index is available definitionally. -/
abbrev WarpPath
    {L : PopularAuxiliary.Input Gamma I} {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) :=
  {p : FinitePath L.lambda.graph // p ∈ P.paths}

/-- The canonical loop-erased original-web route belonging to one member of
a target warp. -/
noncomputable def canonicalErasedRoute
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target)
    (p : WarpPath P) : Alternating.AltPath Gamma.graph :=
  (L.decodeFinitePath p.1 (P.starts_in_source p.2)
    (P.ends_in_target p.2)).erasedCompression.path

theorem canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target)
    (p : WarpPath P) :
    (canonicalErasedRoute L P p).vertexSet ⊆
      L.decodedVertexCarrier p.1 := by
  exact decodeFinitePath_erasedCompression_vertexSet_subset L p.1
    (P.starts_in_source p.2) (P.ends_in_target p.2)

/-- Pairwise-disjoint decoded carriers give pairwise vertex-disjoint
canonical erased routes.  This is the exact route-level repair of the raw
all-seeds collision counterexample. -/
theorem canonicalErasedRoutes_pairwiseDisjoint
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target)
    (hP : P.paths.PairwiseDisjoint L.decodedVertexCarrier) :
    Set.PairwiseDisjoint Set.univ
      (fun p : WarpPath P => (canonicalErasedRoute L P p).vertexSet) := by
  intro p _hp q _hq hpq
  have hpqPath : p.1 ≠ q.1 := by
    intro h
    exact hpq (Subtype.ext h)
  exact (hP p.2 q.2 hpqPath).mono
    (canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier L P p)
    (canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier L P q)

/-- The forward edge union of the canonical erased routes. -/
def canonicalErasedForwardEdges
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target) : Set (V × V) :=
  ⋃ p : WarpPath P,
    (canonicalErasedRoute L P p).directionEdges .forward

theorem AltPath.directionEdge_endpoints_mem_vertexSet
    {D : Digraph V} (Q : Alternating.AltPath D)
    {d : Alternating.Direction} {e : V × V}
    (he : e ∈ Q.directionEdges d) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hlQ, _hld, hel⟩ := he
  have hend := l.path.edgeSet_subset_support_prod hel
  cases Q with
  | trivial v => simp [Alternating.AltPath.links] at hlQ
  | finite T =>
      obtain ⟨j, rfl⟩ := hlQ
      exact ⟨Set.mem_iUnion.2 ⟨j, hend.1⟩,
        Set.mem_iUnion.2 ⟨j, hend.2⟩⟩
  | infinite T =>
      obtain ⟨j, rfl⟩ := hlQ
      exact ⟨Set.mem_iUnion.2 ⟨j, hend.1⟩,
        Set.mem_iUnion.2 ⟨j, hend.2⟩⟩

/-- A pairwise vertex-disjoint route family has a bi-unique simultaneous
forward relation.  This is the local relation theorem needed before mixing
the routes with the residual ladder edges. -/
theorem canonicalErasedForwardEdges_biUnique
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target)
    (hroute : Set.PairwiseDisjoint Set.univ
      (fun p : WarpPath P => (canonicalErasedRoute L P p).vertexSet)) :
    Relator.BiUnique
      (fun x y => (x, y) ∈ canonicalErasedForwardEdges L P) := by
  constructor
  · intro x y z hxz hyz
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hxz hyz
    obtain ⟨p, hp⟩ := hxz
    obtain ⟨q, hq⟩ := hyz
    by_cases hpq : p = q
    · subst q
      exact (Alternating.AltPath.forwardEdges_biUnique
        (canonicalErasedRoute L P p)).1 hp hq
    · exfalso
      have hzp :=
        (AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute L P p) hp).2
      have hzq :=
        (AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute L P q) hq).2
      exact Set.disjoint_left.1 (hroute trivial trivial hpq) hzp hzq
  · intro x y z hxy hxz
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hxy hxz
    obtain ⟨p, hp⟩ := hxy
    obtain ⟨q, hq⟩ := hxz
    by_cases hpq : p = q
    · subst q
      exact (Alternating.AltPath.forwardEdges_biUnique
        (canonicalErasedRoute L P p)).2 hp hq
    · exfalso
      have hxp :=
        (AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute L P p) hp).1
      have hxq :=
        (AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute L P q) hq).1
      exact Set.disjoint_left.1 (hroute trivial trivial hpq) hxp hxq

theorem canonicalErasedForwardEdges_biUnique_of_decodedCarrierDisjoint
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target)
    (hP : P.paths.PairwiseDisjoint L.decodedVertexCarrier) :
    Relator.BiUnique
      (fun x y => (x, y) ∈ canonicalErasedForwardEdges L P) := by
  exact canonicalErasedForwardEdges_biUnique L P
    (canonicalErasedRoutes_pairwiseDisjoint L P hP)

/-- If every selected decoded carrier avoids a protected set, then both
endpoints of every inserted canonical forward edge avoid that set. -/
theorem canonicalErasedForwardEdges_endpoints_not_mem
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target)
    {R : Set V}
    (havoid : ∀ p ∈ P.paths,
      Disjoint (L.decodedVertexCarrier p) R)
    {e : V × V} (he : e ∈ canonicalErasedForwardEdges L P) :
    e.1 ∉ R ∧ e.2 ∉ R := by
  simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at he
  obtain ⟨p, he⟩ := he
  have hends := AltPath.directionEdge_endpoints_mem_vertexSet
    (canonicalErasedRoute L P p) he
  have hcarrier := canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
    L P p
  exact ⟨fun hR => Set.disjoint_left.1 (havoid p.1 p.2)
      (hcarrier hends.1) hR,
    fun hR => Set.disjoint_left.1 (havoid p.1 p.2)
      (hcarrier hends.2) hR⟩

/-! ## A collision-repaired equal-family relation -/

/-- Backward edges traversed by the canonical erased routes. -/
def canonicalErasedBackwardEdges
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target) : Set (V × V) :=
  ⋃ p : WarpPath P,
    (canonicalErasedRoute L P p).directionEdges .backward

/-- Every retained backward edge really belongs to the limiting ladder
warp. -/
theorem canonicalErasedRoute_backwardEdges_subset_familyEdges
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target)
    (p : WarpPath P) :
    (canonicalErasedRoute L P p).directionEdges .backward ⊆
      L.familyEdges := by
  let T := L.decodeFinitePath p.1 (P.starts_in_source p.2)
    (P.ends_in_target p.2)
  let E := T.runs.erasedSignedRoute
  intro e he
  have he' : e ∈
      (E.compressionOfValid
        (fun {_s} hs => T.valid _ (E.steps_sublist.subset hs))).path.directionEdges
          .backward := by
    simpa [canonicalErasedRoute, T, E,
      PopularAuxiliary.Input.MicroTrace.erasedCompression] using he
  have hsigned :=
    E.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      (fun {_s} hs => T.valid _ (E.steps_sublist.subset hs)) .backward he'
  obtain ⟨s, hsE, hsback, rfl⟩ := hsigned
  exact T.backward_on_ladder s (E.steps_sublist.subset hsE) hsback

theorem canonicalErasedBackwardEdges_subset_familyEdges
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target) :
    canonicalErasedBackwardEdges L P ⊆ L.familyEdges := by
  intro e he
  simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at he
  obtain ⟨p, he⟩ := he
  exact canonicalErasedRoute_backwardEdges_subset_familyEdges L P p he

/-- The base ladder relation after all selected backward edges are toggled
off. -/
def canonicalErasedResidualEdges
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target) : Set (V × V) :=
  L.familyEdges \ canonicalErasedBackwardEdges L P

/-- Residual edges which would share a tail or a head with an inserted
forward edge.  Deleting them is the same local collision repair used by the
sound Section 8 decoder. -/
def canonicalErasedForwardConflictEdges
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target) : Set (V × V) :=
  {e | ∃ f ∈ canonicalErasedForwardEdges L P,
    e.1 = f.1 ∨ e.2 = f.2}

/-- The collision-repaired equal-family relation. -/
def canonicalErasedRepairedEdges
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target) : Set (V × V) :=
  (canonicalErasedResidualEdges L P \
      canonicalErasedForwardConflictEdges L P) ∪
    canonicalErasedForwardEdges L P

theorem canonicalErasedForwardEdges_subset_adj
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target) :
    canonicalErasedForwardEdges L P ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at he
  obtain ⟨p, he⟩ := he
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, _hl, _hforward, hel⟩ := he
  exact l.path.edgeSet_subset_adj hel

theorem canonicalErasedRepairedEdges_subset_adj
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target) :
    canonicalErasedRepairedEdges L P ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact Alternating.familyEdges_subset_adj L.ladder.paths (by
      simpa [PopularAuxiliary.Input.familyEdges,
        Alternating.familyEdges] using he.1.1)
  · exact canonicalErasedForwardEdges_subset_adj L P he

/-- Once the thinned decoded carriers are disjoint, the complete repaired
equal-family relation has indegree and outdegree at most one. -/
theorem canonicalErasedRepairedEdges_biUnique
    (L : PopularAuxiliary.Input Gamma I)
    (P : Popular.XSWarp L.lambda L.lambda.target)
    (hP : P.paths.PairwiseDisjoint L.decodedVertexCarrier) :
    Relator.BiUnique
      (fun x y => (x, y) ∈ canonicalErasedRepairedEdges L P) := by
  have hbase : Relator.BiUnique
      (fun x y => (x, y) ∈ canonicalErasedResidualEdges L P \
        canonicalErasedForwardConflictEdges L P) := by
    have hfull := Alternating.IsWarp.familyEdges_biUnique L.ladder.disjoint
    constructor
    · intro x y z hxz hyz
      apply hfull.1
      · simpa [PopularAuxiliary.Input.familyEdges,
          Alternating.familyEdges] using hxz.1.1
      · simpa [PopularAuxiliary.Input.familyEdges,
          Alternating.familyEdges] using hyz.1.1
    · intro x y z hxy hxz
      apply hfull.2
      · simpa [PopularAuxiliary.Input.familyEdges,
          Alternating.familyEdges] using hxy.1.1
      · simpa [PopularAuxiliary.Input.familyEdges,
          Alternating.familyEdges] using hxz.1.1
  have hforward :=
    canonicalErasedForwardEdges_biUnique_of_decodedCarrierDisjoint L P hP
  constructor
  · intro x y z hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hbase.1 hxz hyz
    · exfalso
      exact hxz.2 ⟨(y, z), hyz, Or.inr rfl⟩
    · exfalso
      exact hyz.2 ⟨(x, z), hxz, Or.inr rfl⟩
    · exact hforward.1 hxz hyz
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hbase.2 hxy hxz
    · exfalso
      exact hxy.2 ⟨(x, z), hxz, Or.inl rfl⟩
    · exfalso
      exact hxz.2 ⟨(x, y), hxy, Or.inl rfl⟩
    · exact hforward.2 hxy hxz

/-- The source ordinal of a member of an auxiliary warp. -/
def warpPathIndex
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) (p : WarpPath P) : Below kappa :=
  U.f ⟨p.1.start, P.starts_in_source p.2⟩

/-- Source injectivity and warp disjointness make a warp path uniquely
determined by its inherited source ordinal. -/
theorem warpPath_eq_of_index_eq
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa) (hU : U.SourceIndexed)
    {S : Set L.LV} (P : Popular.XSWarp L.lambda S)
    {p q : WarpPath P}
    (hpq : warpPathIndex U P p = warpPathIndex U P q) : p = q := by
  apply Subtype.ext
  apply P.eq_of_start_eq p.2 q.2
  have hs :
      (⟨p.1.start, P.starts_in_source p.2⟩ : L.lambda.source) =
        ⟨q.1.start, P.starts_in_source q.2⟩ := hU hpq
  exact congrArg Subtype.val hs

/-- Greedy activity along source ordinals.  A path is active exactly when
its decoded original carrier avoids every earlier active decoded carrier. -/
noncomputable def IsActiveWarpPath
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) : WarpPath P → Prop :=
  WellFounded.fix
    (InvImage.wf (warpPathIndex U P) wellFounded_lt)
    (fun p previous ↦
      ∀ q (hq : warpPathIndex U P q < warpPathIndex U P p),
        previous q hq →
          Disjoint (L.decodedVertexCarrier p.1)
            (L.decodedVertexCarrier q.1))

theorem isActiveWarpPath_iff
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) (p : WarpPath P) :
    IsActiveWarpPath L U P p ↔
      ∀ q (_hq : warpPathIndex U P q < warpPathIndex U P p),
        IsActiveWarpPath L U P q →
          Disjoint (L.decodedVertexCarrier p.1)
            (L.decodedVertexCarrier q.1) := by
  unfold IsActiveWarpPath
  rw [WellFounded.fix_eq
    (InvImage.wf (warpPathIndex U P) wellFounded_lt)
    (fun p previous ↦
      ∀ q (hq : warpPathIndex U P q < warpPathIndex U P p),
        previous q hq →
          Disjoint (L.decodedVertexCarrier p.1)
            (L.decodedVertexCarrier q.1)) p]

/-- Every rejected path has an earlier active collision owner. -/
theorem exists_active_earlier_collision_of_not_active
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) (p : WarpPath P)
    (hp : ¬ IsActiveWarpPath L U P p) :
    ∃ q : WarpPath P,
      warpPathIndex U P q < warpPathIndex U P p ∧
      IsActiveWarpPath L U P q ∧
      (L.decodedVertexCarrier p.1 ∩
        L.decodedVertexCarrier q.1).Nonempty := by
  rw [isActiveWarpPath_iff] at hp
  push Not at hp
  obtain ⟨q, hqp, hactive, hnotdisjoint⟩ := hp
  rw [Set.not_disjoint_iff] at hnotdisjoint
  exact ⟨q, hqp, hactive, hnotdisjoint⟩

/-- The raw path set retained by the greedy activity predicate. -/
def activeWarpPaths
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) : Set (FinitePath L.lambda.graph) :=
  {p | ∃ hp : p ∈ P.paths, IsActiveWarpPath L U P ⟨p, hp⟩}

theorem activeWarpPaths_starts_in_source
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) :
    ∀ {p}, p ∈ activeWarpPaths L U P → p.start ∈ L.lambda.source := by
  rintro p ⟨hp, _⟩
  exact P.starts_in_source hp

/-- The source indices retained by the greedy decoded-carrier thinning. -/
def activeWarpIndices
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) : Set (Below kappa) :=
  Popular.initialIndicesOf U (activeWarpPaths L U P)
    (activeWarpPaths_starts_in_source L U P)

/-- Rank-ordered active paths have disjoint decoded carriers by construction. -/
theorem activeWarpPath_decodedCarriers_disjoint_of_index_lt
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) {p q : WarpPath P}
    (hp : IsActiveWarpPath L U P p) (hq : IsActiveWarpPath L U P q)
    (hqp : warpPathIndex U P q < warpPathIndex U P p) :
    Disjoint (L.decodedVertexCarrier p.1)
      (L.decodedVertexCarrier q.1) :=
  (isActiveWarpPath_iff L U P p).1 hp q hqp hq

theorem warpPathIndex_mem_activeWarpIndices
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) (p : WarpPath P)
    (hp : IsActiveWarpPath L U P p) :
    warpPathIndex U P p ∈ activeWarpIndices L U P := by
  let hpA : p.1 ∈ activeWarpPaths L U P := ⟨p.2, hp⟩
  refine ⟨p.1, hpA, ?_⟩
  apply congrArg U.f
  exact Subtype.ext rfl

/-- The greedy decoded-carrier selector retains stationarily many source
indices.  If its complement inside the original stationary family were
stationary, every rejected path would choose an earlier active collision
owner.  Fodor makes one owner constant on a stationary subfamily, contrary
to the fixed-route collision nonstationarity theorem above. -/
theorem activeWarpIndices_isStationary
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (U : Popular.KappaIndexed L.lambda kappa) (hU : U.SourceIndexed)
    {S : Set L.LV} (P : Popular.XSWarp L.lambda S)
    (hP : IsStationaryBelow kappa
      (Popular.initialIndicesOf U P.paths P.starts_in_source)) :
    IsStationaryBelow kappa (activeWarpIndices L U P) := by
  classical
  let allIndices : Set (Below kappa) :=
    Popular.initialIndicesOf U P.paths P.starts_in_source
  let selectedIndices : Set (Below kappa) := activeWarpIndices L U P
  let rejectedIndices : Set (Below kappa) := allIndices \ selectedIndices
  by_contra hselected
  have hrejected : IsStationaryBelow kappa rejectedIndices := by
    exact PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      U.regular U.uncountable hP hselected
  let chosenPath : (a : Below kappa) → a ∈ allIndices →
      FinitePath L.lambda.graph :=
    fun a ha ↦ Classical.choose ha
  have chosenPath_mem (a : Below kappa) (ha : a ∈ allIndices) :
      chosenPath a ha ∈ P.paths :=
    Classical.choose (Classical.choose_spec ha)
  have chosenPath_index (a : Below kappa) (ha : a ∈ allIndices) :
      U.f ⟨(chosenPath a ha).start,
        P.starts_in_source (chosenPath_mem a ha)⟩ = a :=
    Classical.choose_spec (Classical.choose_spec ha)
  let chosenWarpPath (a : Below kappa) (ha : a ∈ allIndices) : WarpPath P :=
    ⟨chosenPath a ha, chosenPath_mem a ha⟩
  have chosenWarpPath_inactive (a : Below kappa)
      (ha : a ∈ rejectedIndices) :
      ¬ IsActiveWarpPath L U P (chosenWarpPath a ha.1) := by
    intro hactive
    apply ha.2
    have hmem := warpPathIndex_mem_activeWarpIndices L U P
      (chosenWarpPath a ha.1) hactive
    have hindex : warpPathIndex U P (chosenWarpPath a ha.1) = a := by
      exact chosenPath_index a ha.1
    exact hindex ▸ hmem
  let ownerPath (a : Below kappa) (ha : a ∈ rejectedIndices) : WarpPath P :=
    Classical.choose (exists_active_earlier_collision_of_not_active
      L U P (chosenWarpPath a ha.1) (chosenWarpPath_inactive a ha))
  have ownerPath_earlier (a : Below kappa) (ha : a ∈ rejectedIndices) :
      warpPathIndex U P (ownerPath a ha) <
        warpPathIndex U P (chosenWarpPath a ha.1) :=
    (Classical.choose_spec (exists_active_earlier_collision_of_not_active
      L U P (chosenWarpPath a ha.1) (chosenWarpPath_inactive a ha))).1
  have ownerPath_active (a : Below kappa) (ha : a ∈ rejectedIndices) :
      IsActiveWarpPath L U P (ownerPath a ha) :=
    (Classical.choose_spec (exists_active_earlier_collision_of_not_active
      L U P (chosenWarpPath a ha.1) (chosenWarpPath_inactive a ha))).2.1
  have ownerPath_collision (a : Below kappa) (ha : a ∈ rejectedIndices) :
      (L.decodedVertexCarrier (chosenWarpPath a ha.1).1 ∩
        L.decodedVertexCarrier (ownerPath a ha).1).Nonempty :=
    (Classical.choose_spec (exists_active_earlier_collision_of_not_active
      L U P (chosenWarpPath a ha.1) (chosenWarpPath_inactive a ha))).2.2
  let ownerIndex : Below kappa → Below kappa := fun a ↦
    if ha : a ∈ rejectedIndices then warpPathIndex U P (ownerPath a ha) else a
  have hregressive : IsRegressiveOn rejectedIndices ownerIndex := by
    intro a ha
    have howner : ownerIndex a = warpPathIndex U P (ownerPath a ha) := by
      simp [ownerIndex, ha]
    rw [howner]
    exact lt_of_lt_of_eq (ownerPath_earlier a ha)
      (chosenPath_index a ha.1)
  obtain ⟨i, hi⟩ := pressingDown U.uncountable U.regular
    hrejected hregressive
  obtain ⟨a, haRejected, hai⟩ := hi.nonempty
  let q : WarpPath P := ownerPath a haRejected
  have hqindex : warpPathIndex U P q = i := by
    have howner : ownerIndex a = warpPathIndex U P (ownerPath a haRejected) := by
      simp [ownerIndex, haRejected]
    exact howner.symm.trans hai
  have hcollisionStationary : IsStationaryBelow kappa
      (Popular.initialIndicesOf U
        (decodedCarrierCollisions L P q.1)
        (fun {_p} hp ↦ P.starts_in_source hp.1)) := by
    apply hi.mono
    rintro b ⟨hbRejected, hbi⟩
    let r : WarpPath P := ownerPath b hbRejected
    have hrindex : warpPathIndex U P r = i := by
      have howner : ownerIndex b = warpPathIndex U P (ownerPath b hbRejected) := by
        simp [ownerIndex, hbRejected]
      exact howner.symm.trans hbi
    have hrq : r = q :=
      warpPath_eq_of_index_eq U hU P (hrindex.trans hqindex.symm)
    let p : WarpPath P := chosenWarpPath b hbRejected.1
    have hpcollision :
        (L.decodedVertexCarrier p.1 ∩
          L.decodedVertexCarrier q.1).Nonempty := by
      simpa [p, r, hrq] using ownerPath_collision b hbRejected
    let hpC : p.1 ∈ decodedCarrierCollisions L P q.1 :=
      ⟨p.2, hpcollision⟩
    refine ⟨p.1, hpC, ?_⟩
    have hs :
        (⟨p.1.start, P.starts_in_source hpC.1⟩ : L.lambda.source) =
          ⟨p.1.start, P.starts_in_source p.2⟩ := Subtype.ext rfl
    exact (congrArg U.f hs).trans (chosenPath_index b hbRejected.1)
  exact (decodedCarrierCollisionIndices_nonstationary
    L hfaith U P q.1 (P.starts_in_source q.2)) hcollisionStationary

/-- The active members, regarded as an auxiliary subwarp. -/
def activeSubwarp
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) : Popular.XSWarp L.lambda S where
  paths := activeWarpPaths L U P
  disjoint := by
    rintro p ⟨hp, _⟩ q ⟨hq, _⟩ hpq
    exact P.disjoint hp hq hpq
  starts_in_source := activeWarpPaths_starts_in_source L U P
  ends_in_target := by
    rintro p ⟨hp, _⟩
    exact P.ends_in_target hp

theorem activeSubwarp_paths_subset
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {S : Set L.LV}
    (P : Popular.XSWarp L.lambda S) :
    (activeSubwarp L U P).paths ⊆ P.paths := by
  rintro p ⟨hp, _⟩
  exact hp

/-- Distinct paths in the active subwarp have genuinely disjoint decoded
original-vertex carriers. -/
theorem activeSubwarp_decodedCarriers_pairwiseDisjoint
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) (hU : U.SourceIndexed)
    {S : Set L.LV} (P : Popular.XSWarp L.lambda S) :
    (activeSubwarp L U P).paths.PairwiseDisjoint L.decodedVertexCarrier := by
  rintro p ⟨hpP, hpA⟩ q ⟨hqP, hqA⟩ hpq
  have hindex_ne :
      warpPathIndex U P (⟨p, hpP⟩ : WarpPath P) ≠
        warpPathIndex U P (⟨q, hqP⟩ : WarpPath P) := by
    intro heq
    have hppeq : (⟨p, hpP⟩ : WarpPath P) = ⟨q, hqP⟩ :=
      warpPath_eq_of_index_eq U hU P heq
    exact hpq (congrArg Subtype.val hppeq)
  rcases lt_or_gt_of_ne hindex_ne with hpqlt | hqplt
  · have hd := activeWarpPath_decodedCarriers_disjoint_of_index_lt
      (p := (⟨q, hqP⟩ : WarpPath P)) (q := (⟨p, hpP⟩ : WarpPath P))
      L U P hqA hpA hpqlt
    exact hd.symm
  · exact activeWarpPath_decodedCarriers_disjoint_of_index_lt
      (p := (⟨p, hpP⟩ : WarpPath P)) (q := (⟨q, hqP⟩ : WarpPath P))
      L U P hpA hqA hqplt

/-- Stationarity of the active subwarp, stated using its own source proof. -/
theorem activeSubwarp_initialIndices_isStationary
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (U : Popular.KappaIndexed L.lambda kappa) (hU : U.SourceIndexed)
    {S : Set L.LV} (P : Popular.XSWarp L.lambda S)
    (hP : IsStationaryBelow kappa
      (Popular.initialIndicesOf U P.paths P.starts_in_source)) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf U (activeSubwarp L U P).paths
        (activeSubwarp L U P).starts_in_source) := by
  have hactive := activeWarpIndices_isStationary L hfaith U hU P hP
  apply hactive.mono
  rintro a ⟨p, hp, hpa⟩
  refine ⟨p, hp, ?_⟩
  have hs :
      (⟨p.start, (activeSubwarp L U P).starts_in_source hp⟩ : L.lambda.source) =
        ⟨p.start, activeWarpPaths_starts_in_source L U P hp⟩ :=
    Subtype.ext rfl
  exact (congrArg U.f hs).trans hpa

/-- A stationary auxiliary warp admits a stationary subwarp whose decoded
original carriers are pairwise disjoint.  This is the collision-safe
replacement for the false all-seeds simultaneous switch. -/
theorem exists_stationary_decodedCarrierDisjoint_subwarp
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (U : Popular.KappaIndexed L.lambda kappa) (hU : U.SourceIndexed)
    {S : Set L.LV} (P : Popular.XSWarp L.lambda S)
    (hP : IsStationaryBelow kappa
      (Popular.initialIndicesOf U P.paths P.starts_in_source)) :
    ∃ Q : Popular.XSWarp L.lambda S,
      Q.paths ⊆ P.paths ∧
      IsStationaryBelow kappa
        (Popular.initialIndicesOf U Q.paths Q.starts_in_source) ∧
      Q.paths.PairwiseDisjoint L.decodedVertexCarrier := by
  refine ⟨activeSubwarp L U P, activeSubwarp_paths_subset L U P,
    activeSubwarp_initialIndices_isStationary L hfaith U hU P hP, ?_⟩
  exact activeSubwarp_decodedCarriers_pairwiseDisjoint L U hU P

/-- Reserve the complete collision carrier of one prescribed auxiliary
path, and keep a stationary subwarp avoiding it.  This is the form needed
to leave one grounded inessential parent completely untouched by the equal
switch. -/
theorem exists_stationary_decodedCarrierDisjoint_subwarp_avoiding
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I) (hfaith : ProxyPathsFaithful L)
    (U : Popular.KappaIndexed L.lambda kappa) (hU : U.SourceIndexed)
    {S : Set L.LV} (P : Popular.XSWarp L.lambda S)
    (hP : IsStationaryBelow kappa
      (Popular.initialIndicesOf U P.paths P.starts_in_source))
    (q : FinitePath L.lambda.graph) :
    ∃ Q : Popular.XSWarp L.lambda S,
      Q.paths ⊆ P.paths ∧
      IsStationaryBelow kappa
        (Popular.initialIndicesOf U Q.paths Q.starts_in_source) ∧
      Q.paths.PairwiseDisjoint L.decodedVertexCarrier ∧
      ∀ p ∈ Q.paths, Disjoint p.support (collisionCarrier L q) := by
  let badPaths : Set (FinitePath L.lambda.graph) :=
    {p | p ∈ P.paths ∧
      (p.support ∩ collisionCarrier L q).Nonempty}
  let badStarts : ∀ {p}, p ∈ badPaths → p.start ∈ L.lambda.source :=
    fun {_p} hp => P.starts_in_source hp.1
  let badIndices : Set (Below kappa) :=
    Popular.initialIndicesOf U badPaths badStarts
  have hbad : ¬ IsStationaryBelow kappa badIndices := by
    exact P.initialIndices_meeting_nonstationary U
      (collisionCarrier_countable L hfaith q)
  have hgoodIndices : IsStationaryBelow kappa
      (Popular.initialIndicesOf U P.paths P.starts_in_source \ badIndices) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      U.regular U.uncountable hP hbad
  let goodPaths : Set (FinitePath L.lambda.graph) :=
    {p | p ∈ P.paths ∧ Disjoint p.support (collisionCarrier L q)}
  let R : Popular.XSWarp L.lambda S :=
    Popular.KappaIndexed.subwarp P goodPaths (by
      intro p hp
      exact hp.1)
  have hR : IsStationaryBelow kappa
      (Popular.initialIndicesOf U R.paths R.starts_in_source) := by
    apply hgoodIndices.mono
    rintro a ⟨⟨p, hpP, hpa⟩, haBad⟩
    have hpDisjoint : Disjoint p.support (collisionCarrier L q) := by
      rw [Set.disjoint_left]
      intro x hxp hxCarrier
      apply haBad
      let hpBad : p ∈ badPaths :=
        ⟨hpP, ⟨x, hxp, hxCarrier⟩⟩
      refine ⟨p, hpBad, ?_⟩
      have hs :
          (⟨p.start, badStarts hpBad⟩ :
              L.lambda.source) =
            ⟨p.start, P.starts_in_source hpP⟩ := Subtype.ext rfl
      exact (congrArg U.f hs).trans hpa
    let hpR : p ∈ R.paths := ⟨hpP, hpDisjoint⟩
    refine ⟨p, hpR, ?_⟩
    have hs :
        (⟨p.start, R.starts_in_source hpR⟩ : L.lambda.source) =
          ⟨p.start, P.starts_in_source hpP⟩ := Subtype.ext rfl
    exact (congrArg U.f hs).trans hpa
  obtain ⟨Q, hQR, hQstat, hQdisjoint⟩ :=
    exists_stationary_decodedCarrierDisjoint_subwarp
      L hfaith U hU R hR
  refine ⟨Q, fun p hp => (hQR hp).1, hQstat, hQdisjoint, ?_⟩
  intro p hp
  exact (hQR hp).2

/-- A subwarp consisting entirely of same-index members is fixed by taking
the same-index subwarp once more. -/
theorem equalSubwarp_paths_eq_of_subset_equalSubwarp
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (P Q : Popular.XSWarp L.lambda L.lambda.target)
    (hQP : Q.paths ⊆ (U.equalSubwarp P).paths) :
    (U.equalSubwarp Q).paths = Q.paths := by
  ext p
  constructor
  · change p ∈ U.equalPaths Q → p ∈ Q.paths
    intro hp
    exact U.equalPaths_subset Q hp
  · intro hpQ
    obtain ⟨hpP, heq⟩ := hQP hpQ
    change ∃ hp : p ∈ Q.paths,
      U.g ⟨p.finish, Q.ends_in_target hp⟩ =
        U.f ⟨p.start, Q.starts_in_source hp⟩
    refine ⟨hpQ, ?_⟩
    have ht :
        (⟨p.finish, Q.ends_in_target hpQ⟩ : L.lambda.target) =
          ⟨p.finish, P.ends_in_target hpP⟩ := Subtype.ext rfl
    have hs :
        (⟨p.start, P.starts_in_source hpP⟩ : L.lambda.source) =
          ⟨p.start, Q.starts_in_source hpQ⟩ := Subtype.ext rfl
    exact (congrArg U.g ht).trans (heq.trans (congrArg U.f hs))

/-- Stationarity transfers from a same-index subwarp to its idempotent
same-index presentation, including the dependent source-membership proof. -/
theorem equalSubwarp_initialIndices_isStationary_of_subset
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (P Q : Popular.XSWarp L.lambda L.lambda.target)
    (hQP : Q.paths ⊆ (U.equalSubwarp P).paths)
    (hQ : IsStationaryBelow kappa
      (Popular.initialIndicesOf U Q.paths Q.starts_in_source)) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf U (U.equalSubwarp Q).paths
        (U.equalSubwarp Q).starts_in_source) := by
  have hpaths := equalSubwarp_paths_eq_of_subset_equalSubwarp U P Q hQP
  apply hQ.mono
  rintro a ⟨p, hpQ, hpa⟩
  have hpE : p ∈ (U.equalSubwarp Q).paths := by
    rw [hpaths]
    exact hpQ
  refine ⟨p, hpE, ?_⟩
  have hs :
      (⟨p.start, (U.equalSubwarp Q).starts_in_source hpE⟩ : L.lambda.source) =
        ⟨p.start, Q.starts_in_source hpQ⟩ := Subtype.ext rfl
  exact (congrArg U.f hs).trans hpa

end GroundingEqualActiveSelection

namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath Stationary

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Concrete equal-branch specialization.  From the exact stationary
equal-subwarp witness retained by the target-pure dichotomy, select a
stationary collision-safe subwarp without discarding its geometry. -/
theorem exists_stationary_decodedCarrierDisjoint_equalSubwarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    ∃ Q : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      Q.paths ⊆ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths ∧
      IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          Q.paths Q.starts_in_source) ∧
      Q.paths.PairwiseDisjoint
        (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier := by
  apply GroundingEqualActiveSelection.exists_stationary_decodedCarrierDisjoint_subwarp
    (L.popularAuxiliaryInput hL.legal)
    (L.popularAuxiliary_proxyPathsFaithful hL)
    (L.popularAuxiliaryIndexed hL)
    (L.popularAuxiliaryIndexed_sourceIndexed hL)
    ((L.popularAuxiliaryIndexed hL).equalSubwarp P)
    hstat

/-- The exact equal-branch witness needed downstream: after collision-safe
thinning, target purity is retained and the resulting warp remains a
stationary fixed point of the same-index operation. -/
theorem exists_targetPure_stationary_decodedCarrierDisjoint_equalSubwarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    ∃ Q : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      Q.paths ⊆ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths ∧
      (∀ p ∈ Q.paths,
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) ∧
      IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source) ∧
      Q.paths.PairwiseDisjoint
        (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier := by
  obtain ⟨Q, hQP, hQstat, hQdisj⟩ :=
    L.exists_stationary_decodedCarrierDisjoint_equalSubwarp hL P hstat
  refine ⟨Q, hQP, ?_, ?_, hQdisj⟩
  · intro p hpQ
    apply hpure p
    exact (L.popularAuxiliaryIndexed hL).equalPaths_subset P (hQP hpQ)
  · exact
      GroundingEqualActiveSelection.equalSubwarp_initialIndices_isStationary_of_subset
        (L.popularAuxiliaryIndexed hL) P Q hQP hQstat

/-- Reserve one concrete member of the stationary equal family before the
collision-safe thinning.  Every selected path avoids the reserved member's
complete auxiliary collision carrier, while stationarity, target purity,
same-index membership, and decoded-carrier disjointness are all retained. -/
theorem exists_reserved_targetPure_stationary_equalSubwarp
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    ∃ q ∈ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths,
      ∃ Q : Popular.XSWarp
          (L.popularAuxiliaryInput hL.legal).lambda
          (L.popularAuxiliaryInput hL.legal).lambda.target,
        Q.paths ⊆ ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths ∧
        (∀ p ∈ Q.paths,
          (L.popularAuxiliaryInput hL.legal).IsTargetPure p) ∧
        IsStationaryBelow kappa
          (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp Q).starts_in_source) ∧
        Q.paths.PairwiseDisjoint
          (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier ∧
        (∀ p ∈ Q.paths,
          Disjoint p.support
            (GroundingEqualActiveSelection.collisionCarrier
              (L.popularAuxiliaryInput hL.legal) q)) := by
  let R := (L.popularAuxiliaryIndexed hL).equalSubwarp P
  obtain ⟨a, q, hqR, _hqa⟩ := hstat.nonempty
  obtain ⟨Q, hQR, hQstat, hQdisjoint, hQavoid⟩ :=
    GroundingEqualActiveSelection.exists_stationary_decodedCarrierDisjoint_subwarp_avoiding
      (L.popularAuxiliaryInput hL.legal)
      (L.popularAuxiliary_proxyPathsFaithful hL)
      (L.popularAuxiliaryIndexed hL)
      (L.popularAuxiliaryIndexed_sourceIndexed hL)
      R hstat q
  refine ⟨q, hqR, Q, hQR, ?_, ?_, hQdisjoint, hQavoid⟩
  · intro p hpQ
    apply hpure p
    exact (L.popularAuxiliaryIndexed hL).equalPaths_subset P (hQR hpQ)
  · exact
      GroundingEqualActiveSelection.equalSubwarp_initialIndices_isStationary_of_subset
        (L.popularAuxiliaryIndexed hL) P Q hQR hQstat

end DWeb.KappaLadder
end Erdos599
