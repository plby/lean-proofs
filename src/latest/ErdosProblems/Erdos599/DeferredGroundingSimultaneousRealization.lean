/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedAssembly
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Ray-compatible realization of the simultaneous Section 8 switch

The final Section 8 warp is not known to have finite character before its
essential part is taken: unused recorded rays are deliberately retained as
inessential components.  The finite realization theorem in
`SafeSwitchingAssembly` is consequently too strong for this step.

This file supplies the corresponding ray-compatible relation theorem.  A
locally bi-unique directed relation with no directed cycle and no reverse
directed ray has a canonical decomposition into finite paths and forward
rays.  Prescribed isolated vertices can be added provided that they are not
incident with the relation.  The result is stated directly as an exact
`SwitchData.RealizedBy` certificate, which is the decomposition needed by
the simultaneous grounding switch.
-/

noncomputable section

namespace Erdos599
namespace Alternating
namespace RelationDecomposition

open Set DirectedPath

universe u

variable {V : Type u}

namespace DWeb

variable (G : Erdos599.DWeb V)

/-- Add prescribed singleton components to a forward-orbit decomposition.
Unlike `exists_finiteWarp_realizing_orientation_with_isolated`, this theorem
allows nonterminating forward orbits, hence ray components. -/
theorem exists_warp_realizing_orientation_with_isolated
    (E : Set (V × V)) (I : Set V)
    (O : ForwardOrientation G.graph)
    (hOE : O.edge = E)
    (hcarrier : O.carrier = IncidentVertices O.edge)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ W : Set G.DPath,
      G.IsWarp W ∧ familyEdges W = E ∧ isolatedVertices W = I := by
  let P : Set G.DPath := O.rootPaths
  let T : Set G.DPath := isolatedPaths G I
  have hPwarp : G.IsWarp P := O.rootPaths_pairwiseDisjoint
  have hPE : familyEdges P = E := by
    change O.rootPathEdges = E
    rw [O.rootPathEdges_eq, hOE]
  have hcross : ∀ p ∈ P, ∀ q ∈ T, Disjoint p.support q.support := by
    intro p hp q hq
    rcases hp with ⟨r, rfl⟩
    rcases hq with ⟨x, hxI, rfl⟩
    rw [G.support_trivialPath, Set.disjoint_singleton_right]
    intro hxr
    have hxcarrier : x ∈ O.carrier := O.rootPath_support_subset_carrier r hxr
    rw [hcarrier] at hxcarrier
    rcases hxcarrier with ⟨y, hxy | hyx⟩
    · exact (hI x hxI y).1 (hOE ▸ hxy)
    · exact (hI x hxI y).2 (hOE ▸ hyx)
  refine ⟨P ∪ T, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact hPwarp hp hq hpq
    · exact hcross p hp q hq
    · exact (hcross q hq p hp).symm
    · exact isolatedPaths_isWarp G I hp hq hpq
  · rw [familyEdges_union_local, hPE, familyEdges_isolatedPaths G I,
      Set.union_empty]
  · ext x
    simp only [isolatedVertices, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hx
      rcases hx with hx | hx
      · have hnone : x ∈ (∅ : Set V) := by
          rw [← rootPaths_no_isolated G O hcarrier]
          exact hx
        exact hnone.elim
      · exact (Set.ext_iff.mp (isolatedVertices_isolatedPaths G I) x).mp hx
    · intro hx
      exact Or.inr
        ((Set.ext_iff.mp (isolatedVertices_isolatedPaths G I) x).mpr hx)

/-- A locally bi-unique acyclic relation with no reverse-directed ray is the
edge relation of a genuine warp.  Forward rays are allowed, as required for
the unused-record components of Assertion 8.22. -/
theorem exists_warp_realizing_biUnique
    (E : Set (V × V)) (I : Set V)
    (hgraph : E ⊆ {e | G.graph.Adj e.1 e.2})
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hcycle : ¬ ContainsDirectedCycle E)
    (hReverseRay : ¬ ContainsReverseDirectedRay E)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ W : Set G.DPath,
      G.IsWarp W ∧ familyEdges W = E ∧ isolatedVertices W = I := by
  let carrier := IncidentVertices E
  have hendpoints : ∀ e ∈ E, e.1 ∈ carrier ∧ e.2 ∈ carrier := by
    rintro ⟨x, y⟩ hxy
    exact ⟨incident_of_edge_left hxy, incident_of_edge_right hxy⟩
  let hwf : WellFounded (fun x y ↦ (x, y) ∈ E) :=
    ForwardOrientation.predecessor_wellFounded E hcycle hReverseRay
  let O : ForwardOrientation G.graph :=
    { edge := E
      carrier := carrier
      depth := ForwardOrientation.wellFoundedDepth E hwf
      component := ForwardOrientation.wellFoundedRoot E hwf
      edge_in_graph := hgraph
      endpoints_mem := hendpoints
      out_unique := fun hxy hxz ↦ hunique.2 hxy hxz
      in_unique := fun hxz hyz ↦ hunique.1 hxz hyz
      depth_step := fun hxy ↦
        ForwardOrientation.wellFoundedDepth_step E hunique hwf hxy
      component_step := fun hxy ↦
        ForwardOrientation.wellFoundedRoot_step E hunique hwf hxy
      root_label := fun _hx hdepth ↦
        ForwardOrientation.wellFoundedRoot_eq_self_of_depth_eq_zero E hwf hdepth
      predecessor := by
        intro x _hx hpos
        have hne : ForwardOrientation.wellFoundedDepth E hwf x ≠ 0 :=
          Nat.ne_of_gt hpos
        exact Classical.byContradiction fun hnot ↦
          hne ((ForwardOrientation.wellFoundedDepth_eq_zero_iff E hwf x).mpr hnot) }
  exact exists_warp_realizing_orientation_with_isolated G E I O rfl rfl hI

/-- Switch-data form of the ray-compatible decomposition. -/
theorem exists_realizedBy_of_biUnique
    (S : SwitchData G)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ S.edges))
    (hcycle : ¬ ContainsDirectedCycle S.edges)
    (hReverseRay : ¬ ContainsReverseDirectedRay S.edges)
    (hI : ∀ x ∈ S.isolated, ∀ y,
      (x, y) ∉ S.edges ∧ (y, x) ∉ S.edges) :
    ∃ W : Set G.DPath, S.RealizedBy W := by
  obtain ⟨W, hW, hWE, hWI⟩ := exists_warp_realizing_biUnique G
    S.edges S.isolated S.edges_in_graph hunique hcycle hReverseRay hI
  exact ⟨W, hW, hWE, hWI⟩

end DWeb
end RelationDecomposition

/-! ## Boundary recovery in the presence of rays -/

namespace RayCompatibleBoundary

open Set DirectedPath

variable {V : Type u} {G : Erdos599.DWeb V}

theorem Ray.no_incoming_at_initial (r : Ray G.graph) (y : V) :
    (y, r.initial) ∉ r.edgeSet := by
  rintro ⟨n, hn⟩
  have htarget : r (n + 1) = r 0 := by
    exact (congrArg Prod.snd hn).symm
  have : n + 1 = 0 := r.injective htarget
  omega

theorem Ray.exists_incoming_of_mem_support_of_ne_initial
    (r : Ray G.graph) {x : V} (hx : x ∈ r.support)
    (hne : x ≠ r.initial) : ∃ y, (y, x) ∈ r.edgeSet := by
  obtain ⟨n, rfl⟩ := hx
  have hn : n ≠ 0 := by
    intro hn
    subst n
    exact hne rfl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact ⟨r m, m, by simp⟩

theorem Ray.exists_outgoing_of_mem_support
    (r : Ray G.graph) {x : V} (hx : x ∈ r.support) :
    ∃ y, (x, y) ∈ r.edgeSet := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨r (n + 1), n, rfl⟩

private theorem Path.no_incoming_at_initial (p : G.DPath) (y : V) :
    (y, p.initial) ∉ p.edgeSet := by
  rcases p with p | r
  · exact FinitePath.no_incoming_edge_at_start p y
  · exact RayCompatibleBoundary.Ray.no_incoming_at_initial r y

private theorem Path.exists_incoming_of_mem_support_of_ne_initial
    (p : G.DPath) {x : V} (hx : x ∈ p.support)
    (hne : x ≠ p.initial) : ∃ y, (y, x) ∈ p.edgeSet := by
  rcases p with p | r
  · exact FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p hx hne
  · exact RayCompatibleBoundary.Ray.exists_incoming_of_mem_support_of_ne_initial
      r hx hne

private theorem Path.exists_outgoing_of_mem_support_of_ray
    (r : Ray G.graph) {x : V}
    (hx : x ∈ DirectedPath.Path.support (Sum.inr r : G.DPath)) :
    ∃ y, (x, y) ∈ DirectedPath.Path.edgeSet (Sum.inr r : G.DPath) :=
  RayCompatibleBoundary.Ray.exists_outgoing_of_mem_support r hx

private theorem Walk.eq_nil_of_isPath {D : Digraph V} {x : V}
    (p : Walk D x x) (hp : p.IsPath) : p = .nil := by
  cases p with
  | nil => rfl
  | @cons _ y _ _ q =>
      exact False.elim ((List.nodup_cons.mp hp).1 q.end_mem_support)

private theorem FinitePath.eq_trivial_of_start_eq_finish
    {D : Digraph V} (p : FinitePath D) (h : p.start = p.finish) :
    p = FinitePath.trivial D p.start := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := Walk.eq_nil_of_isPath walk isPath
  subst walk
  rfl

/-- Initial vertices are determined by edges and explicit singleton
components even when the warp contains rays. -/
theorem initialSet_eq_isolated_union_outgoing_boundary
    {W : Set G.DPath} (hW : G.IsWarp W) :
    G.initialSet W = isolatedVertices W ∪
      {x | HasOutgoing (familyEdges W) x ∧
        ¬ HasIncoming (familyEdges W) x} := by
  ext x
  constructor
  · rintro ⟨p, hpW, rfl⟩
    have hnin : ¬ HasIncoming (familyEdges W) p.initial := by
      rintro ⟨y, hy⟩
      simp only [familyEdges, Set.mem_iUnion] at hy
      obtain ⟨q, hqW, hyq⟩ := hy
      have hpq : p = q :=
        DWeb.IsWarp.eq_of_mem_support hW hpW hqW
          p.initial_mem_support (q.edgeSet_subset_support_prod hyq).2
      subst q
      exact Path.no_incoming_at_initial p y hyq
    rcases p with p | r
    · by_cases hends : p.start = p.finish
      · left
        have hp0 := RayCompatibleBoundary.FinitePath.eq_trivial_of_start_eq_finish
          p hends
        have hp0' : (Sum.inl p : G.DPath) = G.trivialPath p.start := by
          rw [hp0]
          rfl
        change G.trivialPath p.start ∈ W
        exact hp0' ▸ hpW
      · right
        refine ⟨?_, hnin⟩
        obtain ⟨y, hy⟩ :=
          FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            p p.start_mem_support hends
        refine ⟨y, ?_⟩
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inl p, hpW, hy⟩
    · right
      refine ⟨?_, hnin⟩
      refine ⟨r 1, ?_⟩
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨Sum.inr r, hpW, ⟨0, rfl⟩⟩
  · rintro (hxiso | ⟨⟨y, hxy⟩, hnin⟩)
    · exact ⟨G.trivialPath x, hxiso, by simp⟩
    · simp only [familyEdges, Set.mem_iUnion] at hxy
      obtain ⟨p, hpW, hxyp⟩ := hxy
      have hxp : x ∈ p.support := (p.edgeSet_subset_support_prod hxyp).1
      have hinitial : x = p.initial := by
        by_contra hne
        obtain ⟨z, hzx⟩ :=
          Path.exists_incoming_of_mem_support_of_ne_initial p hxp hne
        apply hnin
        refine ⟨z, ?_⟩
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨p, hpW, hzx⟩
      exact ⟨p, hpW, hinitial.symm⟩

/-- Finite terminals are likewise determined by incoming-only incidence;
ray components contribute no terminal. -/
theorem terminalFrontier_eq_isolated_union_incoming_boundary
    {W : Set G.DPath} (hW : G.IsWarp W) :
    G.terminalFrontier W = isolatedVertices W ∪
      {x | HasIncoming (familyEdges W) x ∧
        ¬ HasOutgoing (familyEdges W) x} := by
  ext x
  constructor
  · rintro ⟨p, hpW, hpx⟩
    rcases p with p | r
    · simp only [Erdos599.DWeb.terminal?_finite, Option.some.injEq] at hpx
      subst x
      by_cases hends : p.start = p.finish
      · left
        have hp0 := RayCompatibleBoundary.FinitePath.eq_trivial_of_start_eq_finish
          p hends
        have hp0' : (Sum.inl p : G.DPath) = G.trivialPath p.finish := by
          rw [hp0, hends]
          rfl
        change G.trivialPath p.finish ∈ W
        exact hp0' ▸ hpW
      · right
        constructor
        · obtain ⟨y, hy⟩ :=
            FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
              p p.finish_mem_support (fun h ↦ hends h.symm)
          refine ⟨y, ?_⟩
          simp only [familyEdges, Set.mem_iUnion]
          exact ⟨Sum.inl p, hpW, hy⟩
        · rintro ⟨y, hy⟩
          simp only [familyEdges, Set.mem_iUnion] at hy
          obtain ⟨q, hqW, hqy⟩ := hy
          have hpq : (Sum.inl p : G.DPath) = q :=
            DWeb.IsWarp.eq_of_mem_support hW hpW hqW
              p.finish_mem_support (q.edgeSet_subset_support_prod hqy).1
          subst q
          exact FinitePath.no_outgoing_edge_at_finish p y hqy
    · simp at hpx
  · rintro (hxiso | ⟨⟨y, hyx⟩, hnout⟩)
    · exact ⟨G.trivialPath x, hxiso, by simp⟩
    · simp only [familyEdges, Set.mem_iUnion] at hyx
      obtain ⟨p, hpW, hyxp⟩ := hyx
      have hxp : x ∈ p.support := (p.edgeSet_subset_support_prod hyxp).2
      rcases p with p | r
      · have hfinish : x = p.finish := by
          by_contra hne
          obtain ⟨z, hxz⟩ :=
            FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
              p hxp hne
          apply hnout
          refine ⟨z, ?_⟩
          simp only [familyEdges, Set.mem_iUnion]
          exact ⟨Sum.inl p, hpW, hxz⟩
        exact ⟨Sum.inl p, hpW, by simpa using hfinish.symm⟩
      · obtain ⟨z, hxz⟩ :=
          RayCompatibleBoundary.Path.exists_outgoing_of_mem_support_of_ray r hxp
        apply False.elim
        apply hnout
        refine ⟨z, ?_⟩
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inr r, hpW, hxz⟩

/-- Boundary transport across an exact realization, with rays allowed. -/
theorem realizedBy_boundaries
    {S : SwitchData G} {W : Set G.DPath} (hW : S.RealizedBy W) :
    G.initialSet W = S.isolated ∪
        {x | HasOutgoing S.edges x ∧ ¬ HasIncoming S.edges x} ∧
      G.terminalFrontier W = S.isolated ∪
        {x | HasIncoming S.edges x ∧ ¬ HasOutgoing S.edges x} := by
  constructor
  · rw [initialSet_eq_isolated_union_outgoing_boundary hW.1,
      hW.2.1, hW.2.2]
  · rw [terminalFrontier_eq_isolated_union_incoming_boundary hW.1,
      hW.2.1, hW.2.2]

end RayCompatibleBoundary
end Alternating
end Erdos599

/-! ## Original-vertex footprints of auxiliary paths -/

namespace Erdos599
namespace PopularAuxiliary
namespace Input

open Set DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

/-- Every original vertex which can occur while decoding one auxiliary
gadget.  A proxy deliberately contributes its whole represented path: the
chosen first connector may leave from any of its vertices. -/
def gadgetFootprint (L : Input Gamma I) : L.LV → Set V
  | .old x => {x}
  | .edge x y => {x, y}
  | .proxy i => (L.proxyPath i).support

/-- The original-vertex footprint of a finite auxiliary path. -/
def pathFootprint (L : Input Gamma I)
    (p : FinitePath L.lambda.graph) : Set V :=
  ⋃ a ∈ p.support, L.gadgetFootprint a

theorem gadgetFootprint_countable (L : Input Gamma I) (a : L.LV) :
    (L.gadgetFootprint a).Countable := by
  cases a with
  | old x => exact Set.countable_singleton x
  | edge x y => exact (Set.countable_singleton y).insert x
  | proxy i => exact (L.proxyPath i).support_countable

theorem pathFootprint_countable (L : Input Gamma I)
    (p : FinitePath L.lambda.graph) :
    (L.pathFootprint p).Countable := by
  exact p.support_finite.countable.biUnion fun a _ ↦
    L.gadgetFootprint_countable a

theorem mem_pathFootprint_of_mem_support
    (L : Input Gamma I) (p : FinitePath L.lambda.graph)
    {a : L.LV} (ha : a ∈ p.support) {x : V}
    (hx : x ∈ L.gadgetFootprint a) :
    x ∈ L.pathFootprint p := by
  simp only [pathFootprint, Set.mem_iUnion]
  exact ⟨a, ha, hx⟩

theorem gadgetExit_mem_gadgetFootprint
    (L : Input Gamma I) {a : L.LV} {x : V}
    (h : L.gadgetExit a = some x) :
    x ∈ L.gadgetFootprint a := by
  cases a with
  | old y => simpa [gadgetFootprint] using (Option.some.inj h).symm
  | edge y z =>
      simp only [gadgetFootprint, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact Or.inl (Option.some.inj h).symm
  | proxy i => simp at h

theorem gadgetEntry_mem_gadgetFootprint
    (L : Input Gamma I) {a : L.LV} {x : V}
    (h : L.gadgetEntry a = some x) :
    x ∈ L.gadgetFootprint a := by
  cases a with
  | old y => simpa [gadgetFootprint] using (Option.some.inj h).symm
  | edge y z =>
      simp only [gadgetFootprint, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact Or.inr (Option.some.inj h).symm
  | proxy i => simp at h

/-- Every endpoint of every selected decoded edge lies in the explicit
original footprint of the auxiliary path.  This is the bridge needed to
replace mere Lambda-support disjointness by the source's stronger
grounded-component avoidance invariant. -/
theorem decodedRouteEdges_endpoints_mem_pathFootprint
    (L : Input Gamma I) (p : FinitePath L.lambda.graph)
    {e : V × V} (he : e ∈ L.decodedRouteEdges p) :
    e.1 ∈ L.pathFootprint p ∧ e.2 ∈ L.pathFootprint p := by
  rcases he with he | he
  · have hnode : LambdaVertex.edge e.1 e.2 ∈ p.support := he.1
    constructor
    · apply L.mem_pathFootprint_of_mem_support p hnode
      simp [gadgetFootprint]
    · apply L.mem_pathFootprint_of_mem_support p hnode
      simp [gadgetFootprint]
  · rcases he with ⟨a, b, hab, hchosen⟩
    have hsupp := p.edgeSet_subset_support_prod hab
    have hconnector := L.chosenConnector?_eq_some hchosen
    constructor
    · rcases hconnector.1 with hexit | ⟨i, rfl, hx⟩
      · exact L.mem_pathFootprint_of_mem_support p hsupp.1
          (L.gadgetExit_mem_gadgetFootprint hexit)
      · exact L.mem_pathFootprint_of_mem_support p hsupp.1 hx
    · exact L.mem_pathFootprint_of_mem_support p hsupp.2
        (L.gadgetEntry_mem_gadgetFootprint hconnector.2.1)

theorem decodedRouteEdges_incidentVertices_subset_pathFootprint
    (L : Input Gamma I) (p : FinitePath L.lambda.graph) :
    Alternating.RelationDecomposition.IncidentVertices
        (L.decodedRouteEdges p) ⊆
      L.pathFootprint p := by
  rintro x ⟨y, hxy | hyx⟩
  · exact (L.decodedRouteEdges_endpoints_mem_pathFootprint p hxy).1
  · exact (L.decodedRouteEdges_endpoints_mem_pathFootprint p hyx).2

/-- Footprint-disjoint auxiliary routes have completely disjoint decoded
incidence in the original graph. -/
theorem decodedRouteEdges_incidentVertices_disjoint
    (L : Input Gamma I) (p q : FinitePath L.lambda.graph)
    (h : Disjoint (L.pathFootprint p) (L.pathFootprint q)) :
    Disjoint
      (Alternating.RelationDecomposition.IncidentVertices
        (L.decodedRouteEdges p))
      (Alternating.RelationDecomposition.IncidentVertices
        (L.decodedRouteEdges q)) :=
  h.mono (L.decodedRouteEdges_incidentVertices_subset_pathFootprint p)
    (L.decodedRouteEdges_incidentVertices_subset_pathFootprint q)

/-- Meeting the auxiliary trace of a reference path is witnessed by an
actual original-vertex contact with that path inside `pathFootprint`. -/
theorem pathFootprint_meets_of_support_meets_ladderTrace
    (L : Input Gamma I) (q : FinitePath L.lambda.graph)
    (p : Gamma.DPath)
    (h : (q.support ∩ PopularSwitching.ladderTrace L p).Nonempty) :
    (L.pathFootprint q ∩ p.support).Nonempty := by
  obtain ⟨a, haq, ha⟩ := h
  rcases ha with ha | ha
  · obtain ⟨x, hxp, rfl⟩ := ha
    refine ⟨x, ?_, hxp⟩
    apply L.mem_pathFootprint_of_mem_support q haq
    simp [gadgetFootprint]
  · obtain ⟨e, hep, rfl⟩ := ha
    refine ⟨e.1, ?_, (p.edgeSet_subset_support_prod hep).1⟩
    apply L.mem_pathFootprint_of_mem_support q haq
    simp [gadgetFootprint]

end Input
end PopularAuxiliary
end Erdos599
