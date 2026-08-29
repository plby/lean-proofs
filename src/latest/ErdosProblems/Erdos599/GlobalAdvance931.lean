/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalBlueprintRequestGeometry
import ErdosProblems.Erdos599.Blueprint930
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Continuation-aware global compilation of Assertion 9.31

`GlobalBlueprintReplacement` compiles the whole-family splice used in
Assertion 9.31 directly to the stable successor required by Assertion 9.34.
The source proof also uses a more precise factorization through Assertion
9.30.  In that factorization the 9.31 construction must remember two facts
which are not part of a standalone stable successor:

* every edge and vertex of the 9.30 continuation is retained, and
* terminals inherited simultaneously from the 9.30 ancestor and its
  continuation are retained, except for the scheduled endpoint.

This file states those facts at the source-level splice relation and proves
that the root-orbit construction supplies the exact `Advance931Compiler`.
Thus the remaining Section 9 geometry has a low-level target: construct one
bi-unique, acyclic, reverse-ray-free relation with the displayed boundary
properties.  No proposed result warp is accepted as input.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A forward-only real extension: later real edges never acquire a new
predecessor at a vertex which was already present.  This is the local
successor invariant which rules out reverse rays in a transfinite union. -/
def NoNewRealPredecessorsTo
    (W U : LinkageBlueprint Gamma Y kappa) : Prop :=
  ∀ {x y : V}, x ∈ W.realPart.vertices →
    (y, x) ∈ U.realPart.edges → (y, x) ∈ W.realPart.edges

theorem NoNewRealPredecessorsTo.trans
    {W U R : LinkageBlueprint Gamma Y kappa}
    (hWU : W.NoNewRealPredecessorsTo U)
    (hUR : U.NoNewRealPredecessorsTo R)
    (hvertices : W.realPart.vertices ⊆ U.realPart.vertices) :
    W.NoNewRealPredecessorsTo R := by
  intro x y hxW hyxR
  exact hWU hxW (hUR (hvertices hxW) hyxR)

@[refl] theorem NoNewRealPredecessorsTo.refl
    (W : LinkageBlueprint Gamma Y kappa) :
    W.NoNewRealPredecessorsTo W := by
  intro x y _ hxy
  exact hxy

/-- The full-edge forward-only invariant required before all imaginary edges
have disappeared.  It is stronger than `NoNewRealPredecessorsTo`: no later
blueprint edge, real or imaginary, may enter an old vertex unless that exact
edge was already present. -/
def NoNewPredecessorsTo
    (W U : LinkageBlueprint Gamma Y kappa) : Prop :=
  ∀ {x y : V}, x ∈ W.vertexSet →
    (y, x) ∈ U.edgeSet → (y, x) ∈ W.edgeSet

theorem NoNewPredecessorsTo.trans
    {W U R : LinkageBlueprint Gamma Y kappa}
    (hWU : W.NoNewPredecessorsTo U)
    (hUR : U.NoNewPredecessorsTo R)
    (hvertices : W.vertexSet ⊆ U.vertexSet) :
    W.NoNewPredecessorsTo R := by
  intro x y hxW hyxR
  exact hWU hxW (hUR (hvertices hxW) hyxR)

@[refl] theorem NoNewPredecessorsTo.refl
    (W : LinkageBlueprint Gamma Y kappa) :
    W.NoNewPredecessorsTo W := by
  intro x y _ hxy
  exact hxy

/-- The root-level part of predecessor preservation.  This is the honest
successor invariant needed to keep old blueprint initials as roots even when
the transition is not known to preserve predecessors at every old vertex. -/
def NoNewPredecessorsToInitials
    (W U : LinkageBlueprint Gamma Y kappa) : Prop :=
  ∀ {x y : V}, x ∈ W.initialSet →
    (y, x) ∈ U.edgeSet → (y, x) ∈ W.edgeSet

theorem NoNewPredecessorsToInitials.trans
    {W U R : LinkageBlueprint Gamma Y kappa}
    (hWU : W.NoNewPredecessorsToInitials U)
    (hUR : U.NoNewPredecessorsToInitials R)
    (hinitials : W.initialSet ⊆ U.initialSet) :
    W.NoNewPredecessorsToInitials R := by
  intro x y hxW hyxR
  exact hWU hxW (hUR (hinitials hxW) hyxR)

@[refl] theorem NoNewPredecessorsToInitials.refl
    (W : LinkageBlueprint Gamma Y kappa) :
    W.NoNewPredecessorsToInitials W := by
  intro x y _ hxy
  exact hxy

/-- Full predecessor preservation specializes to preservation at old
initials. -/
theorem NoNewPredecessorsTo.toInitials
    {W U : LinkageBlueprint Gamma Y kappa}
    (h : W.NoNewPredecessorsTo U) :
    W.NoNewPredecessorsToInitials U := by
  intro x y hx hxy
  obtain ⟨p, hpW, hpinitial⟩ := hx
  exact h ⟨p, hpW, hpinitial.symm ▸ p.initial_mem_support⟩ hxy

private theorem noIncoming_of_mem_initialSet
    (W : LinkageBlueprint Gamma Y kappa) {x : V}
    (hx : x ∈ W.initialSet) : ¬ ∃ y, (y, x) ∈ W.edgeSet := by
  rintro ⟨y, hyx⟩
  obtain ⟨p, hpW, hpinitial⟩ := hx
  simp only [edgeSet, Set.mem_iUnion] at hyx
  obtain ⟨q, hqW, hyxq⟩ := hyx
  have hxp : x ∈ p.support := hpinitial.symm ▸ p.initial_mem_support
  have hxq : x ∈ q.support :=
    (q.edgeSet_subset_support_prod hyxq).2
  have hpq : p = q := W.path_eq_of_mem_support hpW hqW hxp hxq
  subst q
  rcases p with p | r
  · have hpstart : p.start = x := by
      simpa [DirectedPath.Path.initial] using hpinitial
    exact Alternating.FinitePath.no_incoming_edge_at_start p y
      (hpstart ▸ hyxq)
  · obtain ⟨n, hn⟩ := hyxq
    have hzero : n + 1 = 0 := by
      apply r.injective
      calc
        r (n + 1) = x := (congrArg Prod.snd hn).symm
        _ = r.initial := hpinitial.symm
        _ = r 0 := rfl
    omega

private theorem mem_initialSet_of_mem_vertexSet_of_noIncoming
    (W : LinkageBlueprint Gamma Y kappa) {x : V}
    (hx : x ∈ W.vertexSet) (hno : ¬ ∃ y, (y, x) ∈ W.edgeSet) :
    x ∈ W.initialSet := by
  obtain ⟨p, hpW, hxp⟩ := hx
  refine ⟨p, hpW, ?_⟩
  by_contra hpinitial
  have hne : x ≠ p.initial := fun h ↦ hpinitial h.symm
  rcases p with p | r
  · obtain ⟨y, hy⟩ :=
      Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        p hxp hne
    exact hno ⟨y, Set.mem_iUnion.2 ⟨Sum.inl p,
      Set.mem_iUnion.2 ⟨hpW, hy⟩⟩⟩
  · obtain ⟨n, hn⟩ := hxp
    have hnpos : 0 < n := by
      by_contra hnzero
      have : n = 0 := Nat.eq_zero_of_not_pos hnzero
      exact hne (by simpa [DirectedPath.Path.initial, Ray.initial, this]
        using hn.symm)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    exact hno ⟨r m, Set.mem_iUnion.2 ⟨Sum.inr r,
      Set.mem_iUnion.2 ⟨hpW, ⟨m, by exact Prod.ext rfl hn.symm⟩⟩⟩⟩

/-- Root-level predecessor preservation plus inclusion of the old carrier
keeps every old initial vertex initial. -/
theorem NoNewPredecessorsToInitials.initialSet_mono
    {W U : LinkageBlueprint Gamma Y kappa}
    (h : W.NoNewPredecessorsToInitials U)
    (hvertices : W.vertexSet ⊆ U.vertexSet) :
    W.initialSet ⊆ U.initialSet := by
  intro x hx
  apply mem_initialSet_of_mem_vertexSet_of_noIncoming U
  · obtain ⟨p, hpW, hpinitial⟩ := hx
    exact hvertices ⟨p, hpW, hpinitial.symm ▸ p.initial_mem_support⟩
  · rintro ⟨y, hyx⟩
    exact noIncoming_of_mem_initialSet W hx ⟨y, h hx hyx⟩

/-- Forgetting imaginary edges turns full predecessor preservation into the
real-edge invariant used by the earlier relation-limit API. -/
theorem NoNewPredecessorsTo.toReal
    {W U : LinkageBlueprint Gamma Y kappa}
    (h : W.NoNewPredecessorsTo U) :
    W.NoNewRealPredecessorsTo U := by
  intro x y hx hxy
  exact ⟨h (by simpa only [realPart_vertices] using hx) hxy.1, hxy.2⟩

/-- The exact relation-level output consumed by Assertion 9.31.

Unlike `WholeFamilySpliceRelation`, this record contains no bookkeeping for
how the relation was discovered.  In particular, it does not demand a
universally supplied fractured request or remember finite assignment edges
after Claim 2 has already converted them to edges of the imaginary graph.
The direct sink boundary is precisely the conclusion used to establish
blueprint condition (6). -/
structure AdvanceSpliceRelation
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    (z : V) (T Z persistent B : Set V) where
  edge : Set (V × V)
  carrier : Set V
  edge_in_graph : edge ⊆
    {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2}
  endpoints_mem : ∀ e ∈ edge, e.1 ∈ carrier ∧ e.2 ∈ carrier
  biunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ edge)
  no_directed_cycle : ¬ ContainsDirectedCycle edge
  no_reverse_ray : ¬ ContainsReverseDirectedRay edge
  sink_boundary : {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge} ⊆
    {x | IsPopular Gamma Y persistent kappa x} ∪ T
  vertices_roofed : carrier ⊆ Gamma.roof T
  covers_source : Gamma.source ⊆
    {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ edge} ∪
      Gamma.initialSet
        (referencePathsMeeting Y T \ referencePathsMeeting Y carrier)
  vertices_closed : carrier ⊆ Z
  card_carrier : #carrier ≤ kappa
  every_relation_ray_strong :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ edge → (strongEdgeIndices r).Infinite
  stable_boundary :
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge} ∩ T ⊆ persistent
  old_vertices : current.vertexSet ⊆ carrier
  old_edges : current.edgeSet ⊆ edge
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = z
  target_path_finish : target_path.finish ∈ B
  target_path_vertices : target_path.support ⊆ carrier
  target_path_edges : target_path.edgeSet ⊆
    relationRealEdges (Gamma := Gamma) edge
  preserves_other_real_terminals :
    current.realPart.terminals \ {z} ⊆
      relationRealTerminals (Gamma := Gamma) edge carrier
  persistent_boundary : current.terminalSet ∩ persistent ⊆
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge} ∪ {z}
  inherited_boundary :
    ∀ x, x ∈ ancestor.terminalSet → x ∈ current.terminalSet → x ≠ z →
      x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge
  no_new_real_predecessors : ∀ {x y : V},
    x ∈ current.realPart.vertices →
      (y, x) ∈ relationRealEdges (Gamma := Gamma) edge →
        (y, x) ∈ current.realPart.edges

/-! ## Attaching fresh 9.31 geometry to the current blueprint -/

/-- Source-facing form of the 9.31 relation.

The final relation is definitionally the union of all current blueprint
edges with a genuinely fresh relation.  The two-colour no-sandwich
condition is the exact local hypothesis needed by the existing union
lemmas to rule out a directed cycle or a reverse ray.  In particular, those
two global properties and the forward-only real-predecessor condition are
conclusions of the attachment compiler, not unexplained fields supplied by
the provider. -/
structure FreshAdvanceSpliceRelation
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    (z : V) (T Z persistent B : Set V) where
  fresh : Set (V × V)
  carrier : Set V
  current_vertices : current.vertexSet ⊆ carrier
  fresh_edge_in_graph : fresh ⊆
    {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2}
  fresh_endpoints_mem : ∀ e ∈ fresh, e.1 ∈ carrier ∧ e.2 ∈ carrier
  fresh_disjoint : Disjoint current.edgeSet fresh
  union_biunique : Relator.BiUnique
    (fun x y ↦ (x, y) ∈ current.edgeSet ∪ fresh)
  no_forward_sandwich : Alternating.SwitchingCore.NoForwardSandwich
    (D := imaginaryGraph Gamma Y kappa) current.edgeSet fresh
  fresh_no_directed_cycle : ¬ ContainsDirectedCycle fresh
  fresh_no_reverse_ray : ¬ ContainsReverseDirectedRay fresh
  fresh_no_incoming_old_real : ∀ {x y : V},
    x ∈ current.realPart.vertices → (y, x) ∈ fresh → False
  sink_boundary :
    {x | x ∈ carrier ∧
      ¬ ∃ y, (x, y) ∈ current.edgeSet ∪ fresh} ⊆
      {x | IsPopular Gamma Y persistent kappa x} ∪ T
  vertices_roofed : carrier ⊆ Gamma.roof T
  covers_source : Gamma.source ⊆
    {x | x ∈ carrier ∧
      ¬ ∃ y, (y, x) ∈ current.edgeSet ∪ fresh} ∪
      Gamma.initialSet
        (referencePathsMeeting Y T \ referencePathsMeeting Y carrier)
  vertices_closed : carrier ⊆ Z
  card_carrier : #carrier ≤ kappa
  every_relation_ray_strong :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ current.edgeSet ∪ fresh →
        (strongEdgeIndices r).Infinite
  stable_boundary :
    {x | x ∈ carrier ∧
      ¬ ∃ y, (x, y) ∈ current.edgeSet ∪ fresh} ∩ T ⊆ persistent
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = z
  target_path_finish : target_path.finish ∈ B
  target_path_vertices : target_path.support ⊆ carrier
  target_path_edges : target_path.edgeSet ⊆
    relationRealEdges (Gamma := Gamma) (current.edgeSet ∪ fresh)
  preserves_other_real_terminals :
    current.realPart.terminals \ {z} ⊆
      relationRealTerminals (Gamma := Gamma)
        (current.edgeSet ∪ fresh) carrier
  persistent_boundary : current.terminalSet ∩ persistent ⊆
    {x | x ∈ carrier ∧
      ¬ ∃ y, (x, y) ∈ current.edgeSet ∪ fresh} ∪ {z}
  inherited_boundary :
    ∀ x, x ∈ ancestor.terminalSet → x ∈ current.terminalSet → x ≠ z →
      x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ current.edgeSet ∪ fresh

/-- The union of a current blueprint with compatible fresh geometry is the
minimal relation consumed by Assertion 9.31.  Old vertices and edges, both
global infinitary obstructions, and the no-new-real-predecessor invariant
are discharged here. -/
def FreshAdvanceSpliceRelation.toAdvanceSpliceRelation
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (S : FreshAdvanceSpliceRelation
      ancestor current z T Z persistent B) :
    AdvanceSpliceRelation ancestor current z T Z persistent B where
  edge := current.edgeSet ∪ S.fresh
  carrier := S.carrier
  edge_in_graph := by
    rintro e (he | he)
    · rcases Set.mem_iUnion.1 he with ⟨p, he⟩
      rcases Set.mem_iUnion.1 he with ⟨hp, hep⟩
      exact p.edgeSet_subset_adj hep
    · exact S.fresh_edge_in_graph he
  endpoints_mem := by
    rintro e (he | he)
    · rcases Set.mem_iUnion.1 he with ⟨p, he⟩
      rcases Set.mem_iUnion.1 he with ⟨hp, hep⟩
      exact ⟨S.current_vertices ⟨p, hp,
          (p.edgeSet_subset_support_prod hep).1⟩,
        S.current_vertices ⟨p, hp,
          (p.edgeSet_subset_support_prod hep).2⟩⟩
    · exact S.fresh_endpoints_mem e he
  biunique := S.union_biunique
  no_directed_cycle := by
    apply Alternating.SwitchingCore.union_not_containsDirectedCycle
      current.edgeSet S.fresh
    · rintro e (he | he)
      · rcases Set.mem_iUnion.1 he with ⟨p, he⟩
        rcases Set.mem_iUnion.1 he with ⟨hp, hep⟩
        exact p.edgeSet_subset_adj hep
      · exact S.fresh_edge_in_graph he
    · exact S.fresh_disjoint
    · exact S.no_forward_sandwich
    · exact blueprint_edgeSet_not_containsDirectedCycle current
    · exact S.fresh_no_directed_cycle
  no_reverse_ray := by
    apply Alternating.SwitchingCore.union_not_containsReverseDirectedRay
      current.edgeSet S.fresh
    · rintro e (he | he)
      · rcases Set.mem_iUnion.1 he with ⟨p, he⟩
        rcases Set.mem_iUnion.1 he with ⟨hp, hep⟩
        exact p.edgeSet_subset_adj hep
      · exact S.fresh_edge_in_graph he
    · exact S.no_forward_sandwich
    · exact blueprint_edgeSet_not_containsReverseDirectedRay current
    · exact S.fresh_no_reverse_ray
  sink_boundary := S.sink_boundary
  vertices_roofed := S.vertices_roofed
  covers_source := S.covers_source
  vertices_closed := S.vertices_closed
  card_carrier := S.card_carrier
  every_relation_ray_strong := S.every_relation_ray_strong
  stable_boundary := S.stable_boundary
  old_vertices := S.current_vertices
  old_edges := fun _ he ↦ Or.inl he
  target_path := S.target_path
  target_path_start := S.target_path_start
  target_path_finish := S.target_path_finish
  target_path_vertices := S.target_path_vertices
  target_path_edges := S.target_path_edges
  preserves_other_real_terminals := S.preserves_other_real_terminals
  persistent_boundary := S.persistent_boundary
  inherited_boundary := S.inherited_boundary
  no_new_real_predecessors := by
    intro x y hx hxy
    rcases hxy.1 with hxyOld | hxyFresh
    · exact ⟨hxyOld, hxy.2⟩
    · exact False.elim (S.fresh_no_incoming_old_real hx hxyFresh)

/-- Continuation-indexed compiler for compatible fresh 9.31 geometry. -/
def FreshAdvanceSpliceRelationCompiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        Nonempty (FreshAdvanceSpliceRelation W V' z T Z persistent B)

/-- A fresh attachment which explicitly consumes the endpoint summary of an
occurrence-aware fractured assignment.  The attachment remains the object
which proves full predecessor preservation; the last two fields retain the
finite-edge and infinite-source provenance required by the source
whole-family transaction. -/
structure CompressedFreshAdvanceSpliceRelation
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (assignment : CompressedFracturedAssignment Zf Y)
    (z : V) (T Z persistent B : Set V) where
  attachment : FreshAdvanceSpliceRelation ancestor current z T Z persistent B
  assigned_edges : assignment.finiteEdges ⊆
    current.edgeSet ∪ attachment.fresh
  infinite_sources_sink : assignment.infiniteSources ⊆
    {x | x ∈ attachment.carrier ∧
      ¬ ∃ y, (x, y) ∈ current.edgeSet ∪ attachment.fresh}

/-- Forget endpoint provenance and retain the fresh attachment used by the
full-predecessor compiler. -/
abbrev CompressedFreshAdvanceSpliceRelation.toFresh
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : CompressedFracturedAssignment Zf Y}
    {z : V} {T Z persistent B : Set V}
    (S : CompressedFreshAdvanceSpliceRelation
      ancestor current A z T Z persistent B) :
    FreshAdvanceSpliceRelation ancestor current z T Z persistent B :=
  S.attachment

/-- The continuation-aware relation produced by Assertion 9.31.

The inherited `splice` contains all global fractured-assignment and real
extension data.  The last four fields are exactly the extra facts needed by
the 9.30/9.31 factorization: ordinary extension of the continuation and
preservation of persistent and ancestor terminals at the relation sinks. -/
structure WholeFamilyAdvanceSpliceRelation
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (assignment : SimultaneousAssignment Zf.paths Y)
    (z : V) (T Z persistent B : Set V) where
  splice : WholeFamilySpliceRelation current assignment z T Z persistent B
  old_vertices : current.vertexSet ⊆ splice.carrier
  old_edges : current.edgeSet ⊆ splice.edge
  persistent_boundary : current.terminalSet ∩ persistent ⊆
    {x | x ∈ splice.carrier ∧ ¬ ∃ y, (x, y) ∈ splice.edge} ∪ {z}
  inherited_boundary :
    ∀ x, x ∈ ancestor.terminalSet → x ∈ current.terminalSet → x ≠ z →
      x ∈ splice.carrier ∧ ¬ ∃ y, (x, y) ∈ splice.edge
  no_new_real_predecessors : ∀ {x y : V},
    x ∈ current.realPart.vertices →
      (y, x) ∈ relationRealEdges (Gamma := Gamma) splice.edge →
        (y, x) ∈ current.realPart.edges

/-- Forget construction bookkeeping after Claim 2 and retain exactly the
relation consumed by the root-orbit compilation. -/
def WholeFamilyAdvanceSpliceRelation.toAdvanceSpliceRelation
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {z : V} {T Z persistent B : Set V}
    (C : WholeFamilyAdvanceSpliceRelation
      ancestor current A z T Z persistent B)
    (hinfinite : ∀ s, (A.assigned s).IsInfinite →
      IsPopular Gamma Y persistent kappa s.1) :
    AdvanceSpliceRelation ancestor current z T Z persistent B where
  edge := C.splice.edge
  carrier := C.splice.carrier
  edge_in_graph := C.splice.edge_in_graph
  endpoints_mem := C.splice.endpoints_mem
  biunique := C.splice.biunique
  no_directed_cycle := C.splice.no_directed_cycle
  no_reverse_ray := C.splice.no_reverse_ray
  sink_boundary := by
    intro x hx
    rcases C.splice.sink_boundary hx with hxinf | hxT
    · exact Or.inl (assignedInfiniteSources_popular A hinfinite hxinf)
    · exact Or.inr hxT
  vertices_roofed := C.splice.vertices_roofed
  covers_source := C.splice.covers_source
  vertices_closed := C.splice.vertices_closed
  card_carrier := C.splice.card_carrier
  every_relation_ray_strong := C.splice.every_relation_ray_strong
  stable_boundary := C.splice.stable_boundary
  old_vertices := C.old_vertices
  old_edges := C.old_edges
  target_path := C.splice.target_path
  target_path_start := C.splice.target_path_start
  target_path_finish := C.splice.target_path_finish
  target_path_vertices := C.splice.target_path_vertices
  target_path_edges := C.splice.target_path_edges
  preserves_other_real_terminals := C.splice.preserves_other_real_terminals
  persistent_boundary := C.persistent_boundary
  inherited_boundary := C.inherited_boundary
  no_new_real_predecessors := C.no_new_real_predecessors

/-- Occurrence-aware continuation splice retaining only the endpoint summary
of the fractured assignment.  This is the sound 9.31 relation interface for
Remark 4.20: no split-web alternating path is projected to the original web.
-/
structure CompressedWholeFamilyAdvanceSpliceRelation
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (assignment : CompressedFracturedAssignment Zf Y)
    (z : V) (T Z persistent B : Set V) where
  splice : CompressedWholeFamilySpliceRelation current assignment z T Z
    persistent B
  old_vertices : current.vertexSet ⊆ splice.carrier
  old_edges : current.edgeSet ⊆ splice.edge
  persistent_boundary : current.terminalSet ∩ persistent ⊆
    {x | x ∈ splice.carrier ∧ ¬ ∃ y, (x, y) ∈ splice.edge} ∪ {z}
  inherited_boundary :
    ∀ x, x ∈ ancestor.terminalSet → x ∈ current.terminalSet → x ≠ z →
      x ∈ splice.carrier ∧ ¬ ∃ y, (x, y) ∈ splice.edge
  no_new_real_predecessors : ∀ {x y : V},
    x ∈ current.realPart.vertices →
      (y, x) ∈ relationRealEdges (Gamma := Gamma) splice.edge →
        (y, x) ∈ current.realPart.edges

/-- Classifying the endpoint summary turns the occurrence-aware whole-family
splice into the minimal relation consumed by the root-orbit compiler. -/
def CompressedWholeFamilyAdvanceSpliceRelation.toAdvanceSpliceRelation
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : CompressedFracturedAssignment Zf Y}
    {z : V} {T Z persistent B : Set V}
    (C : CompressedWholeFamilyAdvanceSpliceRelation
      ancestor current A z T Z persistent B)
    (hinfinite : ∀ s, A.outcome s = none →
      IsPopular Gamma Y persistent kappa s.1) :
    AdvanceSpliceRelation ancestor current z T Z persistent B where
  edge := C.splice.edge
  carrier := C.splice.carrier
  edge_in_graph := C.splice.edge_in_graph
  endpoints_mem := C.splice.endpoints_mem
  biunique := C.splice.biunique
  no_directed_cycle := C.splice.no_directed_cycle
  no_reverse_ray := C.splice.no_reverse_ray
  sink_boundary := by
    intro x hx
    rcases C.splice.sink_boundary hx with hxinf | hxT
    · exact Or.inl (A.infiniteSources_popular hinfinite hxinf)
    · exact Or.inr hxT
  vertices_roofed := C.splice.vertices_roofed
  covers_source := C.splice.covers_source
  vertices_closed := C.splice.vertices_closed
  card_carrier := C.splice.card_carrier
  every_relation_ray_strong := C.splice.every_relation_ray_strong
  stable_boundary := C.splice.stable_boundary
  old_vertices := C.old_vertices
  old_edges := C.old_edges
  target_path := C.splice.target_path
  target_path_start := C.splice.target_path_start
  target_path_finish := C.splice.target_path_finish
  target_path_vertices := C.splice.target_path_vertices
  target_path_edges := C.splice.target_path_edges
  preserves_other_real_terminals := C.splice.preserves_other_real_terminals
  persistent_boundary := C.persistent_boundary
  inherited_boundary := C.inherited_boundary
  no_new_real_predecessors := C.no_new_real_predecessors

/-- Assertion 9.31 together with the forward-only successor invariant used
at limit stages. -/
structure PredecessorPreservingAdvance931
    (ancestor current result : LinkageBlueprint Gamma Y kappa)
    (z : V) (T Z persistent B : Set V) : Prop where
  advance : Advance931 ancestor current result z T Z persistent B
  no_new_real_predecessors : current.NoNewRealPredecessorsTo result

/-- Assertion 9.31 with the full-edge predecessor invariant needed while
imaginary edges are still present in intermediate scheduler stages. -/
structure FullyPredecessorPreservingAdvance931
    (ancestor current result : LinkageBlueprint Gamma Y kappa)
    (z : V) (T Z persistent B : Set V) : Prop where
  advance : Advance931 ancestor current result z T Z persistent B
  no_new_predecessors : current.NoNewPredecessorsTo result

/-- Full predecessor preservation implies the earlier real-edge package. -/
theorem FullyPredecessorPreservingAdvance931.toPredecessorPreserving
    {ancestor current result : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (h : FullyPredecessorPreservingAdvance931
      ancestor current result z T Z persistent B) :
    PredecessorPreservingAdvance931
      ancestor current result z T Z persistent B where
  advance := h.advance
  no_new_real_predecessors :=
    NoNewPredecessorsTo.toReal h.no_new_predecessors

/-- A continuation-aware provider for the closed fractured request used in
Assertion 9.31.  Unlike the older provider, the request is allowed to depend
on the concrete 9.30 continuation and its endpoint. -/
def ContinuationClosedFracturedReplacementRequestProvider
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        Nonempty (ClosedFracturedReplacementRequest
          (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent)

/-- The construction-specific, source-level target for Assertion 9.31.
All paths in the output blueprint are constructed later as root orbits of
the returned relation. -/
def WholeFamilyAdvanceSpliceRelationCompiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
      ∀ (R : ClosedFracturedReplacementRequest
          (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent)
        (A : SimultaneousAssignment R.fractured.paths Y),
        (∀ s v, (A.assigned s).terminal? = some v →
          IsImaginaryEdge Gamma Y kappa s.1 v) →
        (∀ s, (A.assigned s).IsInfinite →
          IsPopular Gamma Y persistent kappa s.1) →
        Nonempty (WholeFamilyAdvanceSpliceRelation
          W V' A z T Z persistent B)

/-- Minimal continuation-aware relation compiler.  This is the genuine
geometric target of Assertion 9.31 after the simultaneous assignment and
Claim 2 have been carried out. -/
def AdvanceSpliceRelationCompiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        Nonempty (AdvanceSpliceRelation W V' z T Z persistent B)

/-- Compatible fresh geometry supplies the exact minimal relation compiler;
all retention and infinitary relation checks were discharged by
`FreshAdvanceSpliceRelation.toAdvanceSpliceRelation`. -/
theorem advanceSpliceRelationCompiler_of_fresh
    {T Z persistent B : Set V}
    (hfresh : FreshAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    AdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  exact ⟨(hfresh W cut V' u z hW hcontinuation).some
    |>.toAdvanceSpliceRelation⟩

/-- The actual source transaction in Assertion 9.31 chooses the fractured
family, its simultaneous assignment, and the spliced relation together.

This is strictly more source-faithful than
`WholeFamilyAdvanceSpliceRelationCompiler`: that older interface asks the
geometry to splice *every* closed request and every assignment handed to it,
including the canonical empty request.  The printed proof only constructs
one request adapted to the continuation.  Classification is stored here at
the point where it is used, so no endpoint-purity assumptions irrelevant to
the already chosen assignment remain in the compiler interface. -/
structure ClassifiedWholeFamilyAdvanceSplice
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    (z : V) (T Z persistent B : Set V) where
  fractured : FracturedWarp Gamma
  assignment : SimultaneousAssignment fractured.paths Y
  finite_endpoints : ∀ s v, (assignment.assigned s).terminal? = some v →
    IsImaginaryEdge Gamma Y kappa s.1 v
  infinite_sources : ∀ s, (assignment.assigned s).IsInfinite →
    IsPopular Gamma Y persistent kappa s.1
  relation : WholeFamilyAdvanceSpliceRelation
    ancestor current assignment z T Z persistent B

/-- Minimal post-assignment compiler for Assertion 9.31.  It asserts exactly
that the continuation-adapted global transaction exists; the request and
the assignment are outputs rather than universally quantified inputs. -/
def ClassifiedWholeFamilyAdvanceSpliceCompiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        Nonempty (ClassifiedWholeFamilyAdvanceSplice
          W V' z T Z persistent B)

/-- The honest induction request behind Assertion 9.31.

The linkage used by the source proof lives in an auxiliary slice/quotient
web, not in the ambient web with source set `Gamma.source`.  The request
therefore names that web, proves the two hypotheses needed to link its whole
source by the simultaneous cardinal induction, and records how the resulting
linkage is converted into the classified whole-family transaction.  This
avoids the false requirement that the internal slice endpoint itself belong
to `Gamma.source`. -/
structure Advance931AuxiliaryLinkageRequest
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    (z : V) (T Z persistent B : Set V) where
  auxiliary : DWeb V
  auxiliary_unhindered : auxiliary.IsUnhindered
  source_card : #auxiliary.source ≤ kappa
  compile : ∀ L : Set auxiliary.DPath,
    CardinalInduction.IsLinkageBetween
      auxiliary auxiliary.source auxiliary.target L →
      Nonempty (AdvanceSpliceRelation ancestor current z T Z persistent B)

/-- Continuation-indexed provider of the actual auxiliary linkage problem
used in Assertion 9.31. -/
def Advance931AuxiliaryLinkageRequestProvider
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        Nonempty (Advance931AuxiliaryLinkageRequest
          W V' z T Z persistent B)

/-! ## Scheduled-closure construction of the auxiliary request -/

/-- The source-level data from which the honest auxiliary-linkage request is
constructed.

The closure and fractured outside family are outputs for this one concrete
9.30 continuation.  The auxiliary linkage and the simultaneous assignment
are then compiled together with the distinguished closed `z`--`B` path.  A
`FreshAdvanceSpliceRelation` is required at this last boundary: consequently
the absence of new incoming real edges at old vertices is part of the local
geometry and becomes `AdvanceSpliceRelation.no_new_real_predecessors` by the
proved attachment compiler.

In particular, this record does not universally quantify over scheduled
closed requests and never claims that the internal endpoint `z` is an
ambient source. -/
structure ClosureAdaptedAdvance931AuxiliaryLinkageRequest
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    (z : V) (T Z persistent B : Set V) where
  before : Set V
  innerRoof : Set V
  outerRoof : Set V
  seed : Set V
  Preserves : FinitePath Gamma.graph → Prop
  closure : ScheduledClosureRequest Gamma Y kappa z before innerRoof
    outerRoof T B seed Preserves
  outside : ScheduledClosureFracturedOutsideFamily closure
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = z
  target_path_finish : target_path.finish ∈ B
  target_path_closed : target_path.support ⊆ closure.closureSet
  target_path_preserves : Preserves target_path
  auxiliary : DWeb V
  auxiliary_unhindered : auxiliary.IsUnhindered
  source_card : #auxiliary.source ≤ kappa
  compile : ∀ L : Set auxiliary.DPath,
    CardinalInduction.IsLinkageBetween
      auxiliary auxiliary.source auxiliary.target L →
      ∀ (A : SimultaneousAssignment outside.fractured.paths Y),
        (∀ s v, (A.assigned s).terminal? = some v →
          IsImaginaryEdge Gamma Y kappa s.1 v) →
        (∀ s, (A.assigned s).IsInfinite →
          IsPopular Gamma Y persistent kappa s.1) →
        Nonempty {S : FreshAdvanceSpliceRelation
            ancestor current z T Z persistent B //
          S.target_path = target_path}

/-- Construct the closure-adapted request while choosing its distinguished
path from Assertion 9.23.  The remaining compiler is allowed to inspect that
particular path, but must return a fresh splice whose real target path is
definitionally identified with it. -/
noncomputable def
    ClosureAdaptedAdvance931AuxiliaryLinkageRequest.ofScheduledClosure
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    {before innerRoof outerRoof seed : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequest Gamma Y kappa z before innerRoof outerRoof
      T B seed Preserves)
    (hzT : z ∈ T)
    (outside : ScheduledClosureFracturedOutsideFamily C)
    (auxiliary : DWeb V)
    (auxiliary_unhindered : auxiliary.IsUnhindered)
    (source_card : #auxiliary.source ≤ kappa)
    (compile : ∀ (p : FinitePath Gamma.graph),
      p.start = z → p.finish ∈ B → p.support ⊆ C.closureSet →
      Preserves p →
      ∀ L : Set auxiliary.DPath,
        CardinalInduction.IsLinkageBetween
          auxiliary auxiliary.source auxiliary.target L →
        ∀ (A : SimultaneousAssignment outside.fractured.paths Y),
          (∀ s v, (A.assigned s).terminal? = some v →
            IsImaginaryEdge Gamma Y kappa s.1 v) →
          (∀ s, (A.assigned s).IsInfinite →
            IsPopular Gamma Y persistent kappa s.1) →
          Nonempty {S : FreshAdvanceSpliceRelation
              ancestor current z T Z persistent B //
            S.target_path = p}) :
    ClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B := by
  let hp := C.exists_scheduled_target_path hzT
  let p := hp.choose
  exact {
    before := before
    innerRoof := innerRoof
    outerRoof := outerRoof
    seed := seed
    Preserves := Preserves
    closure := C
    outside := outside
    target_path := p
    target_path_start := hp.choose_spec.1
    target_path_finish := hp.choose_spec.2.1
    target_path_closed := hp.choose_spec.2.2.1
    target_path_preserves := hp.choose_spec.2.2.2
    auxiliary := auxiliary
    auxiliary_unhindered := auxiliary_unhindered
    source_card := source_card
    compile := compile p hp.choose_spec.1 hp.choose_spec.2.1
      hp.choose_spec.2.2.1 hp.choose_spec.2.2.2 }

/-- Reference-warp specialization of `ofScheduledClosure`.  It constructs
the only outside-family instance that follows from the current ambient-web
assignment API without any fragment hypotheses.  The simultaneous assignment
for this family is empty; all non-vacuous continuation geometry therefore
remains, correctly, in the compiler for the chosen closed `z`--`B` path. -/
noncomputable def
    ClosureAdaptedAdvance931AuxiliaryLinkageRequest.ofScheduledClosureReferenceWarp
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    {before innerRoof outerRoof seed : Set V}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequest Gamma Y kappa z before innerRoof outerRoof
      T B seed Preserves)
    (hzT : z ∈ T)
    (hYwarp : Gamma.IsWarp Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (auxiliary : DWeb V)
    (auxiliary_unhindered : auxiliary.IsUnhindered)
    (source_card : #auxiliary.source ≤ kappa)
    (compile : ∀ (p : FinitePath Gamma.graph),
      p.start = z → p.finish ∈ B → p.support ⊆ C.closureSet →
      Preserves p →
      ∀ L : Set auxiliary.DPath,
        CardinalInduction.IsLinkageBetween
          auxiliary auxiliary.source auxiliary.target L →
        ∀ (A : SimultaneousAssignment Y Y),
          (∀ s v, (A.assigned s).terminal? = some v →
            IsImaginaryEdge Gamma Y kappa s.1 v) →
          (∀ s, (A.assigned s).IsInfinite →
            IsPopular Gamma Y persistent kappa s.1) →
          Nonempty {S : FreshAdvanceSpliceRelation
              ancestor current z T Z persistent B //
            S.target_path = p}) :
    ClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B :=
  ClosureAdaptedAdvance931AuxiliaryLinkageRequest.ofScheduledClosure
    C hzT
    (ScheduledClosureFracturedOutsideFamily.ofReferenceWarp
      C hYwarp hYsource hYtarget hYfinite)
    auxiliary auxiliary_unhindered source_card (by
      simpa [ScheduledClosureFracturedOutsideFamily.ofReferenceWarp] using
        compile)

/-- Continuation-indexed provider of the closure, its fractured outside
family, and the auxiliary linkage problem.  Existential output at the
continuation is essential: a fixed or universally supplied scheduled request
would reintroduce the ambient-source error. -/
def ClosureAdaptedAdvance931AuxiliaryLinkageRequestProvider
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        Nonempty (ClosureAdaptedAdvance931AuxiliaryLinkageRequest
          W V' z T Z persistent B)

/-- Sound occurrence-aware scheduled request for Assertion 9.31.

The fractured assignment remains in the duplicated web.  Its compressed
endpoint summary is derived by `ofDuplicated`; the two Claim 2
classifications are explicit outputs of the concrete split-occurrence
compiler, not consequences of a projected original-web path.  Closure under
the additional slice-difference family is also retained in the request. -/
structure OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    (z : V) (T Z persistent B : Set V) where
  before : Set V
  innerRoof : Set V
  outerRoof : Set V
  seed : Set V
  extraPaths : Set Gamma.DPath
  Preserves : FinitePath Gamma.graph → Prop
  closure : ScheduledClosureRequestWithExtraPaths Gamma Y extraPaths kappa z
    before innerRoof outerRoof T B seed Preserves
  fractured : FracturedWarp Gamma
  reference_finite : Gamma.HasFiniteCharacter Y
  duplicated : FracturedDuplication.DuplicatedFracturedAssignment fractured Y
  finite_endpoints : ∀ s v,
    (CompressedFracturedAssignment.ofDuplicated duplicated
      reference_finite).outcome s = some v →
      IsImaginaryEdge Gamma Y kappa s.1 v
  infinite_sources : ∀ s,
    (CompressedFracturedAssignment.ofDuplicated duplicated
      reference_finite).outcome s = none →
      IsPopular Gamma Y persistent kappa s.1
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = z
  target_path_finish : target_path.finish ∈ B
  target_path_closed : target_path.support ⊆ closure.closureSet
  target_path_preserves : Preserves target_path
  auxiliary : DWeb V
  auxiliary_unhindered : auxiliary.IsUnhindered
  source_card : #auxiliary.source ≤ kappa
  compile : ∀ L : Set auxiliary.DPath,
    CardinalInduction.IsLinkageBetween
      auxiliary auxiliary.source auxiliary.target L →
      Nonempty {S : CompressedFreshAdvanceSpliceRelation ancestor current
          (CompressedFracturedAssignment.ofDuplicated duplicated
            reference_finite) z T Z persistent B //
        S.attachment.target_path = target_path}

/-- Choose the distinguished closed `z`--`B` path while retaining the
duplicated assignment and its concrete classification. -/
noncomputable def
    OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest.ofScheduledClosure
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    {before innerRoof outerRoof seed : Set V}
    {extraPaths : Set Gamma.DPath}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequestWithExtraPaths Gamma Y extraPaths kappa z
      before innerRoof outerRoof T B seed Preserves)
    (hzT : z ∈ T)
    (fractured : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (duplicated :
      FracturedDuplication.DuplicatedFracturedAssignment fractured Y)
    (finite_endpoints : ∀ s v,
      (CompressedFracturedAssignment.ofDuplicated duplicated
        hYfinite).outcome s = some v →
        IsImaginaryEdge Gamma Y kappa s.1 v)
    (infinite_sources : ∀ s,
      (CompressedFracturedAssignment.ofDuplicated duplicated
        hYfinite).outcome s = none →
        IsPopular Gamma Y persistent kappa s.1)
    (auxiliary : DWeb V)
    (auxiliary_unhindered : auxiliary.IsUnhindered)
    (source_card : #auxiliary.source ≤ kappa)
    (compile : ∀ (p : FinitePath Gamma.graph),
      p.start = z → p.finish ∈ B → p.support ⊆ C.closureSet →
      Preserves p →
      ∀ L : Set auxiliary.DPath,
        CardinalInduction.IsLinkageBetween
          auxiliary auxiliary.source auxiliary.target L →
        Nonempty {S : CompressedFreshAdvanceSpliceRelation ancestor current
            (CompressedFracturedAssignment.ofDuplicated duplicated
              hYfinite) z T Z persistent B //
          S.attachment.target_path = p}) :
    OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B := by
  let hp := C.toScheduledClosureRequest.exists_scheduled_target_path hzT
  let p := hp.choose
  exact {
    before := before
    innerRoof := innerRoof
    outerRoof := outerRoof
    seed := seed
    extraPaths := extraPaths
    Preserves := Preserves
    closure := C
    fractured := fractured
    reference_finite := hYfinite
    duplicated := duplicated
    finite_endpoints := finite_endpoints
    infinite_sources := infinite_sources
    target_path := p
    target_path_start := hp.choose_spec.1
    target_path_finish := hp.choose_spec.2.1
    target_path_closed := hp.choose_spec.2.2.1
    target_path_preserves := hp.choose_spec.2.2.2
    auxiliary := auxiliary
    auxiliary_unhindered := auxiliary_unhindered
    source_card := source_card
    compile := compile p hp.choose_spec.1 hp.choose_spec.2.1
      hp.choose_spec.2.2.1 hp.choose_spec.2.2.2 }

/-- Construct the occurrence-aware request from the genuine one-linkage
projection geometry.  Claim 2 is discharged here from the safe projected
paths; callers do not supply the imaginary-edge or popularity conclusions. -/
noncomputable def
    OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest.ofScheduledClosureProjection
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    {before innerRoof outerRoof seed : Set V}
    {extraPaths : Set Gamma.DPath}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequestWithExtraPaths Gamma Y extraPaths kappa z
      before innerRoof outerRoof T B seed Preserves)
    (hzT : z ∈ T)
    (fractured : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (duplicated :
      FracturedDuplication.DuplicatedFracturedAssignment fractured Y)
    (projection : CompressedFracturedAssignment.ProjectionClosureContext
      duplicated hYfinite C.closureSet before innerRoof outerRoof)
    (auxiliary : DWeb V)
    (auxiliary_unhindered : auxiliary.IsUnhindered)
    (source_card : #auxiliary.source ≤ kappa)
    (compile : ∀ (p : FinitePath Gamma.graph),
      p.start = z → p.finish ∈ B → p.support ⊆ C.closureSet →
      Preserves p →
      ∀ L : Set auxiliary.DPath,
        CardinalInduction.IsLinkageBetween
          auxiliary auxiliary.source auxiliary.target L →
        Nonempty {S : CompressedFreshAdvanceSpliceRelation ancestor current
            (CompressedFracturedAssignment.ofDuplicated duplicated
              hYfinite) z T Z persistent B //
          S.attachment.target_path = p}) :
    OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B := by
  let hclassified :=
    CompressedFracturedAssignment.classify_of_projectionClosureContext
      (persistent := persistent) duplicated hYfinite C.hammock_closed
        projection
  exact OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest.ofScheduledClosure
    C hzT fractured hYfinite duplicated hclassified.1 hclassified.2
      auxiliary auxiliary_unhindered source_card compile

/-- Continuation-indexed occurrence-aware request provider. -/
def OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequestProvider
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        Nonempty (OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
          W V' z T Z persistent B)

/-- Forget the occurrence bookkeeping after constructing the classified
fresh relation. -/
def OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest.toAuxiliaryLinkageRequest
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (R : OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B) :
    Advance931AuxiliaryLinkageRequest ancestor current z T Z persistent B where
  auxiliary := R.auxiliary
  auxiliary_unhindered := R.auxiliary_unhindered
  source_card := R.source_card
  compile := by
    intro L hL
    exact (R.compile L hL).map
      (fun S ↦ S.1.attachment.toAdvanceSpliceRelation)

/-- The occurrence-aware provider supplies the scheduler-facing auxiliary
request without an ambient normalization or fractured path-projection
hypothesis. -/
theorem advance931AuxiliaryLinkageRequestProvider_of_occurrenceClosure
    {T Z persistent B : Set V}
    (hrequests :
      OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequestProvider
        (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Advance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  exact (hrequests W cut V' u z hW hcontinuation).map
    OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest.toAuxiliaryLinkageRequest

/-- A closure-adapted request uses exactly the target path selected at the
scheduled closure stage. -/
theorem ClosureAdaptedAdvance931AuxiliaryLinkageRequest.compiled_target_path
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (R : ClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B)
    {L : Set R.auxiliary.DPath}
    (hL : CardinalInduction.IsLinkageBetween
      R.auxiliary R.auxiliary.source R.auxiliary.target L)
    (A : SimultaneousAssignment R.outside.fractured.paths Y)
    (hfinite : ∀ s v, (A.assigned s).terminal? = some v →
      IsImaginaryEdge Gamma Y kappa s.1 v)
    (hinfinite : ∀ s, (A.assigned s).IsInfinite →
      IsPopular Gamma Y persistent kappa s.1) :
    (R.compile L hL A hfinite hinfinite).some.1.target_path =
      R.target_path :=
  (R.compile L hL A hfinite hinfinite).some.2

/-- The fresh-attachment output of a closure-adapted request has the exact
forward-only real-predecessor property needed by the scheduler. -/
theorem ClosureAdaptedAdvance931AuxiliaryLinkageRequest.compiled_noNewRealPredecessors
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (R : ClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B)
    {L : Set R.auxiliary.DPath}
    (hL : CardinalInduction.IsLinkageBetween
      R.auxiliary R.auxiliary.source R.auxiliary.target L)
    (A : SimultaneousAssignment R.outside.fractured.paths Y)
    (hfinite : ∀ s v, (A.assigned s).terminal? = some v →
      IsImaginaryEdge Gamma Y kappa s.1 v)
    (hinfinite : ∀ s, (A.assigned s).IsInfinite →
      IsPopular Gamma Y persistent kappa s.1) :
    ∀ {x y : V}, x ∈ current.realPart.vertices →
      (y, x) ∈ relationRealEdges (Gamma := Gamma)
        ((R.compile L hL A hfinite hinfinite).some.1
          |>.toAdvanceSpliceRelation).edge →
      (y, x) ∈ current.realPart.edges :=
  (R.compile L hL A hfinite hinfinite).some.1
    |>.toAdvanceSpliceRelation
    |>.no_new_real_predecessors

/-- Apply the fractured simultaneous-assignment theorem and Claim 2 inside a
single closure-adapted auxiliary request.  The resulting request is exactly
the minimal `Advance931AuxiliaryLinkageRequest` consumed by the two cardinal
induction hypotheses. -/
def ClosureAdaptedAdvance931AuxiliaryLinkageRequest.toAuxiliaryLinkageRequest
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (R : ClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B) :
    Advance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B where
  auxiliary := R.auxiliary
  auxiliary_unhindered := R.auxiliary_unhindered
  source_card := R.source_card
  compile := by
    intro L hL
    let A : SimultaneousAssignment R.outside.fractured.paths Y :=
      (hassignment hGamma R.outside.fractured Y R.outside.source_side
        R.outside.target_side hYwarp R.outside.finite_character hYfinite
        R.outside.reference_initials).some
    have hclassified :=
      classify_simultaneousAssignment_of_closed (persistent := persistent)
        R.closure.hammock_closed A
        (R.outside.assignmentClosureContext A)
    exact (R.compile L hL A hclassified.1 hclassified.2).map
      (fun S ↦ S.1.toAdvanceSpliceRelation)

/-- A continuation-indexed scheduled-closure construction supplies the
honest auxiliary-linkage provider.  This is the provider seam for Assertion
9.31; it does not pass through the false assignment-domain scheduled-request
API. -/
theorem advance931AuxiliaryLinkageRequestProvider_of_scheduledClosure
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {T Z persistent B : Set V}
    (hrequests : ClosureAdaptedAdvance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Advance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  exact (hrequests W cut V' u z hW hcontinuation).map
    (ClosureAdaptedAdvance931AuxiliaryLinkageRequest.toAuxiliaryLinkageRequest
      hGamma hYwarp hYfinite hassignment)

/-- The lower-cardinal half-way hypothesis and the current-cardinal
extension hypothesis solve every honest auxiliary request.  This is the
precise point at which the two simultaneous induction hypotheses enter
Assertion 9.31. -/
theorem advanceSpliceRelationCompiler_of_auxiliaryLinkage
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {T Z persistent B : Set V}
    (hrequests : Advance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    AdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  let R := (hrequests W cut V' u z hW hcontinuation).some
  obtain ⟨L, hL⟩ := CardinalInduction.isLinkable_of_source_mk_le_current
    hlower hext R.auxiliary R.auxiliary_unhindered R.source_card
  exact R.compile L hL

/-- End-to-end 9.31 relation compiler from the scheduled closure, its
fractured outside family, and the auxiliary linkage problem.  The two
induction hypotheses solve only the named auxiliary web; the assignment and
Claim 2 classification are performed inside the closure-adapted request. -/
theorem advanceSpliceRelationCompiler_of_scheduledClosureAuxiliaryLinkage
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {T Z persistent B : Set V}
    (hrequests : ClosureAdaptedAdvance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    AdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  advanceSpliceRelationCompiler_of_auxiliaryLinkage hlower hext
    (advance931AuxiliaryLinkageRequestProvider_of_scheduledClosure
      hGamma hYwarp hYfinite hassignment hrequests)

/-- Compatibility alias for the earlier name of the auxiliary-linkage
compiler.  Its conclusion is now the exact minimal relation compiler. -/
theorem classifiedWholeFamilyAdvanceSpliceCompiler_of_auxiliaryLinkage
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {T Z persistent B : Set V}
    (hrequests : Advance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    AdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  advanceSpliceRelationCompiler_of_auxiliaryLinkage hlower hext hrequests

/-- Bundled Assertion 9.31 compiler retaining the local forward-only
predecessor invariant needed by the relation-limit scheduler. -/
def PredecessorPreservingAdvance931Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        ∃ U : LinkageBlueprint Gamma Y kappa,
          PredecessorPreservingAdvance931 W V' U z T Z persistent B

/-- Continuation-indexed 9.31 compiler retaining predecessor preservation
for the complete imaginary-graph edge relation. -/
def FullyPredecessorPreservingAdvance931Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W cut V' : LinkageBlueprint Gamma Y kappa) (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut V' u z T B →
        ∃ U : LinkageBlueprint Gamma Y kappa,
          FullyPredecessorPreservingAdvance931
            W V' U z T Z persistent B

/-- The root-orbit decomposition of a continuation-aware splice relation
is the exact Assertion 9.31 advance object.

The proof performs all representation changes explicitly: relation roots
become blueprint initials, relation sinks become blueprint terminals, and
real relation sinks become terminals of the real part. -/
theorem AdvanceSpliceRelation.exists_predecessorPreservingAdvance931_with_edgeSet
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (S : AdvanceSpliceRelation
      ancestor current z T Z persistent B)
    (hzT : z ∈ T) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      PredecessorPreservingAdvance931
        ancestor current U z T Z persistent B ∧ U.edgeSet = S.edge := by
  obtain ⟨O, hOE, hOC⟩ := exists_forwardOrientation_exact
    S.edge S.carrier S.edge_in_graph S.endpoints_mem S.biunique
      S.no_directed_cycle S.no_reverse_ray
  have hsink_terminal :
      {x | x ∈ S.carrier ∧ ¬ ∃ y, (x, y) ∈ S.edge} =
        (orientationBlueprint O).terminalSet := by
    rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
  have hreal_sink_terminal :
      relationRealTerminals (Gamma := Gamma) S.edge S.carrier =
        (orientationBlueprint O).realPart.terminals := by
    simp only [FamilyGraph.terminals, FamilyGraph.tails, realPart_vertices,
      realPart_edges, orientationBlueprint_vertexSet,
      orientationBlueprint_edgeSet, hOC, hOE, relationRealTerminals,
      relationRealEdges]
  have hpopular : (orientationBlueprint O).terminalSet ⊆
      {x | IsPopular Gamma Y persistent kappa x} ∪ T := by
    rw [← hsink_terminal]
    exact S.sink_boundary
  have hcard : #(orientationBlueprint O).paths ≤ kappa := by
    change #(Set.range O.rootPath) ≤ kappa
    refine Cardinal.mk_range_le.trans ?_
    refine (Cardinal.mk_subtype_mono (fun x hx ↦ hx.1)).trans ?_
    simpa only [hOC] using S.card_carrier
  have hstrong : (orientationBlueprint O).InfinitelyManyStrongEdges := by
    intro r hr
    apply S.every_relation_ray_strong r
    intro e he
    rw [← hOE, ← orientationBlueprint_edgeSet O]
    exact Set.mem_iUnion.2 ⟨(Sum.inr r :
      DirectedPath.Path (imaginaryGraph Gamma Y kappa)),
        Set.mem_iUnion.2 ⟨hr, he⟩⟩
  have hrealTerminals : current.realPart.terminals ⊆
      (orientationBlueprint O).realPart.terminals ∪ T := by
    intro x hx
    by_cases hxz : x = z
    · exact Or.inr (hxz ▸ hzT)
    · exact Or.inl <| hreal_sink_terminal ▸
        S.preserves_other_real_terminals ⟨hx, hxz⟩
  have hpersistent : current.terminalSet ∩ persistent ⊆
      (orientationBlueprint O).terminalSet ∪ {z} := by
    rw [← hsink_terminal]
    exact S.persistent_boundary
  have hpreserves : current.realPart.terminals \ {z} ⊆
      (orientationBlueprint O).realPart.terminals := by
    rw [← hreal_sink_terminal]
    exact S.preserves_other_real_terminals
  have hinherited : ∀ x, x ∈ ancestor.terminalSet →
      x ∈ current.terminalSet → x ≠ z →
        x ∈ (orientationBlueprint O).terminalSet := by
    intro x hxA hxcurrent hxz
    rw [← hsink_terminal]
    exact S.inherited_boundary x hxA hxcurrent hxz
  let U := orientationBlueprint O
  have hUblueprint : U.IsLinkageBlueprint T Z persistent := by
    refine {
      vertices_roofed := ?_
      covers_source := ?_
      vertices_closed := ?_
      card_paths := hcard
      infinitely_many_strong := hstrong
      terminals_popular := hpopular }
    · simpa only [U, orientationBlueprint_vertexSet, hOC] using
        S.vertices_roofed
    · simpa only [U, orientationBlueprint_initialSet_eq_no_incoming,
        retainedReferenceInitials, orientationBlueprint_vertexSet,
        hOC, hOE] using S.covers_source
    · simpa only [U, orientationBlueprint_vertexSet, hOC] using
        S.vertices_closed
  have hstable : U.Stable T persistent := by
    change (orientationBlueprint O).terminalSet ∩ T ⊆ persistent
    rw [← hsink_terminal]
    exact S.stable_boundary
  have hordinary : current.OrdinaryExtends U := by
    constructor
    · simpa only [familyGraph, U, orientationBlueprint_vertexSet, hOC]
        using S.old_vertices
    · simpa only [familyGraph, U, orientationBlueprint_edgeSet, hOE]
        using S.old_edges
  have hlinks : U.RealLinksTo z B := by
    refine ⟨S.target_path, S.target_path_start, S.target_path_finish, ?_, ?_⟩
    · simpa only [U, realPart_vertices, orientationBlueprint_vertexSet, hOC]
        using S.target_path_vertices
    · simpa only [U, realPart_edges, orientationBlueprint_edgeSet, hOE,
        relationRealEdges] using S.target_path_edges
  have hadvance : Advance931 ancestor current U z T Z persistent B := by
    exact {
      conclusion := ⟨hordinary, hlinks, hrealTerminals, hpersistent⟩
      isBlueprint := hUblueprint
      stable := hstable
      family_extends := hordinary
      real_extends := hordinary.realPart_extends
      preserves_except := hpreserves
      preserves_inherited_full_terminals := hinherited }
  have hnoNew : current.NoNewRealPredecessorsTo U := by
    intro x y hx hnew
    apply S.no_new_real_predecessors hx
    simpa only [U, realPart_edges, orientationBlueprint_edgeSet, hOE,
      relationRealEdges] using hnew
  refine ⟨U, ⟨hadvance, hnoNew⟩, ?_⟩
  simpa only [U, orientationBlueprint_edgeSet] using hOE

/-- Forget the exact edge-set identity after compiling the relation. -/
theorem AdvanceSpliceRelation.exists_predecessorPreservingAdvance931
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (S : AdvanceSpliceRelation
      ancestor current z T Z persistent B)
    (hzT : z ∈ T) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      PredecessorPreservingAdvance931
        ancestor current U z T Z persistent B := by
  obtain ⟨U, hU, _hedge⟩ :=
    S.exists_predecessorPreservingAdvance931_with_edgeSet hzT
  exact ⟨U, hU⟩

/-- Fresh attachment geometry preserves predecessors for the complete edge
relation.  This is stronger than the real-only field retained by
`AdvanceSpliceRelation`: a fresh edge is forbidden from entering *any* old
blueprint vertex, independently of whether it is original or imaginary. -/
theorem FreshAdvanceSpliceRelation.exists_fullyPredecessorPreservingAdvance931
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (S : FreshAdvanceSpliceRelation
      ancestor current z T Z persistent B)
    (hzT : z ∈ T) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      FullyPredecessorPreservingAdvance931
        ancestor current U z T Z persistent B := by
  let R := S.toAdvanceSpliceRelation
  obtain ⟨U, hU, hedge⟩ :=
    R.exists_predecessorPreservingAdvance931_with_edgeSet hzT
  refine ⟨U, hU.advance, ?_⟩
  intro x y hx hxy
  have hxy' : (y, x) ∈ current.edgeSet ∪ S.fresh := by
    rw [hedge] at hxy
    exact hxy
  rcases hxy' with hxyOld | hxyFresh
  · exact hxyOld
  · exact False.elim (S.fresh_no_incoming_old_real
      (by simpa only [realPart_vertices] using hx) hxyFresh)

/-- Solve one concrete closure-adapted 9.31 transaction.

This is deliberately a theorem about the request attached to the current
continuation, rather than a provider quantified over arbitrary blueprints.
It is therefore the appropriate geometry seam for a scheduler whose states
carry the certificate for their next reachable transition. -/
theorem ClosureAdaptedAdvance931AuxiliaryLinkageRequest.exists_fullyPredecessorPreservingAdvance931
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (R : ClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B)
    (hzT : z ∈ T) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      FullyPredecessorPreservingAdvance931
        ancestor current U z T Z persistent B := by
  obtain ⟨L, hL⟩ := CardinalInduction.isLinkable_of_source_mk_le_current
    hlower hext R.auxiliary R.auxiliary_unhindered R.source_card
  let A : SimultaneousAssignment R.outside.fractured.paths Y :=
    (hassignment hGamma R.outside.fractured Y R.outside.source_side
      R.outside.target_side hYwarp R.outside.finite_character hYfinite
      R.outside.reference_initials).some
  have hclassified :=
    classify_simultaneousAssignment_of_closed (persistent := persistent)
      R.closure.hammock_closed A
      (R.outside.assignmentClosureContext A)
  exact (R.compile L hL A hclassified.1 hclassified.2).some.1
    |>.exists_fullyPredecessorPreservingAdvance931 hzT

/-- Solve the occurrence-aware scheduled-closure transaction directly.

Unlike the legacy projected-assignment seam above, this theorem does not
reconstruct an alternating path in the unsplit web.  The request already
carries the endpoint summary and the two classifications proved by its
split-occurrence compiler, so cardinal induction is the only remaining
input. -/
theorem OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest.exists_fullyPredecessorPreservingAdvance931
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (R : OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
      ancestor current z T Z persistent B)
    (hzT : z ∈ T) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      FullyPredecessorPreservingAdvance931
        ancestor current U z T Z persistent B := by
  obtain ⟨L, hL⟩ := CardinalInduction.isLinkable_of_source_mk_le_current
    hlower hext R.auxiliary R.auxiliary_unhindered R.source_card
  exact (R.compile L hL).some.1.attachment
    |>.exists_fullyPredecessorPreservingAdvance931 hzT

/-- The original assignment-rich relation factors through the exact minimal
relation before root-orbit compilation. -/
theorem WholeFamilyAdvanceSpliceRelation.exists_predecessorPreservingAdvance931
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {z : V} {T Z persistent B : Set V}
    (C : WholeFamilyAdvanceSpliceRelation
      ancestor current A z T Z persistent B)
    (hzT : z ∈ T)
    (hinfinite : ∀ s, (A.assigned s).IsInfinite →
      IsPopular Gamma Y persistent kappa s.1) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      PredecessorPreservingAdvance931
        ancestor current U z T Z persistent B :=
  (C.toAdvanceSpliceRelation hinfinite)
    |>.exists_predecessorPreservingAdvance931 hzT

/-- Forget the forward-only successor witness and retain the ordinary
Assertion 9.31 object. -/
theorem WholeFamilyAdvanceSpliceRelation.exists_advance931
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {z : V} {T Z persistent B : Set V}
    (C : WholeFamilyAdvanceSpliceRelation
      ancestor current A z T Z persistent B)
    (hzT : z ∈ T)
    (hinfinite : ∀ s, (A.assigned s).IsInfinite →
      IsPopular Gamma Y persistent kappa s.1) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      Advance931 ancestor current U z T Z persistent B := by
  obtain ⟨U, hU⟩ :=
    C.exists_predecessorPreservingAdvance931 hzT hinfinite
  exact ⟨U, hU.advance⟩

/-- The exact minimal relation compiler gives strengthened Assertion 9.31. -/
theorem predecessorPreservingAdvance931Compiler_of_relation
    {T Z persistent B : Set V}
    (hrelation : AdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  exact (hrelation W cut V' u z hW hcontinuation).some
    |>.exists_predecessorPreservingAdvance931
      hcontinuation.endpoint_mem_slice

/-- Forgetful minimal-relation form of Assertion 9.31. -/
theorem advance931Compiler_of_relation
    {T Z persistent B : Set V}
    (hrelation : AdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    @Advance931Compiler V Gamma Y kappa T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  obtain ⟨U, hU⟩ :=
    predecessorPreservingAdvance931Compiler_of_relation hrelation
      W cut V' u z hW hcontinuation
  exact ⟨U, hU.advance⟩

/-- Strengthened Assertion 9.31 obtained from the fresh-attachment seam. -/
theorem predecessorPreservingAdvance931Compiler_of_fresh
    {T Z persistent B : Set V}
    (hfresh : FreshAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  predecessorPreservingAdvance931Compiler_of_relation
    (advanceSpliceRelationCompiler_of_fresh hfresh)

/-- Fresh attachment geometry retains the full-edge predecessor invariant
through the root-orbit compilation. -/
theorem fullyPredecessorPreservingAdvance931Compiler_of_fresh
    {T Z persistent B : Set V}
    (hfresh : FreshAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    FullyPredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  exact (hfresh W cut V' u z hW hcontinuation).some
    |>.exists_fullyPredecessorPreservingAdvance931
      hcontinuation.endpoint_mem_slice

/-- Weak Assertion 9.31 obtained from the fresh-attachment seam. -/
theorem advance931Compiler_of_fresh
    {T Z persistent B : Set V}
    (hfresh : FreshAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    @Advance931Compiler V Gamma Y kappa T Z persistent B :=
  advance931Compiler_of_relation
    (advanceSpliceRelationCompiler_of_fresh hfresh)

/-- A classified source transaction compiles directly to the strengthened
9.31 output. -/
theorem ClassifiedWholeFamilyAdvanceSplice.exists_predecessorPreservingAdvance931
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z persistent B : Set V}
    (C : ClassifiedWholeFamilyAdvanceSplice
      ancestor current z T Z persistent B)
    (hzT : z ∈ T) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      PredecessorPreservingAdvance931
        ancestor current U z T Z persistent B :=
  C.relation.exists_predecessorPreservingAdvance931 hzT C.infinite_sources

/-- The existential, continuation-adapted whole-family transaction is the
minimal source-facing input needed for the strengthened 9.31 compiler. -/
theorem predecessorPreservingAdvance931Compiler_of_classifiedSplice
    {T Z persistent B : Set V}
    (hsplice : ClassifiedWholeFamilyAdvanceSpliceCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  exact (hsplice W cut V' u z hW hcontinuation).some
    |>.exists_predecessorPreservingAdvance931
      hcontinuation.endpoint_mem_slice

/-- Forgetting the forward-only witness gives the original 9.31 compiler. -/
theorem advance931Compiler_of_classifiedSplice
    {T Z persistent B : Set V}
    (hsplice : ClassifiedWholeFamilyAdvanceSpliceCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    @Advance931Compiler V Gamma Y kappa T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  obtain ⟨U, hU⟩ :=
    predecessorPreservingAdvance931Compiler_of_classifiedSplice hsplice
      W cut V' u z hW hcontinuation
  exact ⟨U, hU.advance⟩

/-- Assertion 9.31 derived at the exact source seam from the lower-cardinal
half-way hypothesis, the current extension hypothesis, and the auxiliary
slice/linkage request. -/
theorem predecessorPreservingAdvance931Compiler_of_auxiliaryLinkage
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {T Z persistent B : Set V}
    (hrequests : Advance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  predecessorPreservingAdvance931Compiler_of_relation
    (advanceSpliceRelationCompiler_of_auxiliaryLinkage
      hlower hext hrequests)

/-- Weak form of the same exact lower/current-cardinal derivation. -/
theorem advance931Compiler_of_auxiliaryLinkage
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {T Z persistent B : Set V}
    (hrequests : Advance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    @Advance931Compiler V Gamma Y kappa T Z persistent B :=
  advance931Compiler_of_relation
    (advanceSpliceRelationCompiler_of_auxiliaryLinkage
      hlower hext hrequests)

/-- The global fractured assignment, Claim 2, and one continuation-aware
splice relation compile to Assertion 9.31 together with its forward-only
successor invariant. -/
theorem predecessorPreservingAdvance931Compiler_of_globalFracturedSplice
    {T Z persistent B : Set V}
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    (hrequests : ContinuationClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  let R := (hrequests W cut V' u z hW hcontinuation).some
  let A : SimultaneousAssignment R.fractured.paths Y :=
    (hassignment hGamma R.fractured Y R.source_side R.target_side hYwarp
      R.finite_character hYfinite R.reference_initials).some
  have hclassified :=
    classify_simultaneousAssignment_of_closed (persistent := persistent)
      R.closed A (R.closure_facts A)
  let C := (hsplice W cut V' u z hW hcontinuation R A
    hclassified.1 hclassified.2).some
  exact C.exists_predecessorPreservingAdvance931
    hcontinuation.endpoint_mem_slice hclassified.2

/-- Forgetting the forward-only witness recovers the scheduler's original
Assertion 9.31 compiler interface. -/
theorem advance931Compiler_of_globalFracturedSplice
    {T Z persistent B : Set V}
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    (hrequests : ContinuationClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    @Advance931Compiler V Gamma Y kappa T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  obtain ⟨U, hU⟩ :=
    predecessorPreservingAdvance931Compiler_of_globalFracturedSplice
      hGamma hYwarp hYfinite hassignment hrequests hsplice
      W cut V' u z hW hcontinuation
  exact ⟨U, hU.advance⟩

/-! ### Reference-warp specialization

The canonical honest-reference request has no uncovered assignment sources.
It is nevertheless useful as a bookkeeping specialization of the global
compiler: it removes the request-provider argument and leaves the actual
continuation geometry in the splice-relation compiler, where the scheduled
endpoint is available.  No claim is made that the empty request itself
resolves that endpoint. -/

/-- The reference warp discharges the closed-request bookkeeping in the
predecessor-preserving 9.31 compiler.  The continuation-aware splice compiler
still has to construct the real `z`--`B` path and all boundary invariants. -/
theorem predecessorPreservingAdvance931Compiler_of_referenceWarpSplice
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {T Z persistent B : Set V}
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  apply predecessorPreservingAdvance931Compiler_of_globalFracturedSplice
      hGamma hYwarp hYfinite hassignment
  · intro W cut V' u z hW hcontinuation
    exact ⟨canonicalClosedFracturedReplacementRequest
      hYwarp hYfinite hYsource hYtarget persistent⟩
  · exact hsplice

/-- Weak 9.31 form of the same reference-warp specialization. -/
theorem advance931Compiler_of_referenceWarpSplice
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {T Z persistent B : Set V}
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    @Advance931Compiler V Gamma Y kappa T Z persistent B := by
  intro W cut V' u z hW hcontinuation
  obtain ⟨U, hU⟩ :=
    predecessorPreservingAdvance931Compiler_of_referenceWarpSplice
      hGamma hYwarp hYfinite hYsource hYtarget hassignment hsplice
      W cut V' u z hW hcontinuation
  exact ⟨U, hU.advance⟩

/-- Assertion 9.30 with the same forward-only transition invariant. -/
def PredecessorPreservingContinuation930Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals → u ∈ T →
        ∃ (cut V' : LinkageBlueprint Gamma Y kappa) (z : V),
          Continuation930 W cut V' u z T B ∧
            W.NoNewRealPredecessorsTo V'

/-- The exact scheduled-slice 9.30 construction is forward-only at real
predecessors.  In the terminal case it is the identity.  In the other case
the continuation is the exact deletion of one imaginary edge, so every real
edge of the cut was already a real edge of the ancestor. -/
theorem predecessorPreservingContinuation930Compiler_of_scheduled_slice
    {T Z persistent B : Set V} :
    PredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W u _hW _hpersistent hureal huT
  obtain ⟨cut, hcontinuation, hedges⟩ :=
    exists_continuation930_of_real_terminal_mem_slice_with_realEdges_subset
      W u hureal huT
  refine ⟨cut, cut, u, hcontinuation, ?_⟩
  intro x y _ hxy
  exact hedges hxy

/-- Assertion 9.30 with predecessor preservation for the complete blueprint
edge relation. -/
def FullyPredecessorPreservingContinuation930Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals → u ∈ T →
        ∃ (cut V' : LinkageBlueprint Gamma Y kappa) (z : V),
          Continuation930 W cut V' u z T B ∧
            W.NoNewPredecessorsTo V'

/-- The scheduled 9.30 continuation is either the identity or the exact
deletion of one imaginary edge.  In both cases every edge of the continuation
was already an edge of its ancestor. -/
theorem fullyPredecessorPreservingContinuation930Compiler_of_scheduled_slice
    {T Z persistent B : Set V} :
    FullyPredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W u _hW _hpersistent hureal huT
  obtain ⟨cut, hcontinuation⟩ :=
    exists_continuation930_of_real_terminal_mem_slice W u hureal huT
  refine ⟨cut, cut, u, hcontinuation, ?_⟩
  intro x y _ hxy
  exact hcontinuation.conclusion.isCutAt.ordinaryExtends_original.2 hxy

/-- A stable 9.34 successor together with the transition invariant used at
relation-limit stages. -/
structure PredecessorPreservingStable934
    (W U : LinkageBlueprint Gamma Y kappa)
    (u : V) (T Z persistent B : Set V) : Prop where
  conclusion : StableExtensionConclusion W U u T Z persistent B
  no_new_real_predecessors : W.NoNewRealPredecessorsTo U

/-- A stable 9.34 successor with predecessor preservation for all blueprint
edges, including the imaginary edges present at intermediate stages. -/
structure FullyPredecessorPreservingStable934
    (W U : LinkageBlueprint Gamma Y kappa)
    (u : V) (T Z persistent B : Set V) : Prop where
  conclusion : StableExtensionConclusion W U u T Z persistent B
  no_new_predecessors : W.NoNewPredecessorsTo U

/-- The concrete geometry certificate for one reachable 9.34 transition.

It remembers the actual 9.30 continuation, its full-edge predecessor
invariant, and the scheduled-closure 9.31 request attached to that
continuation.  Unlike `Stable934Compiler`, this type has no quantification
over arbitrary linkage blueprints: a certified scheduler state carries one
such value only for an eligible transition out of that state. -/
structure CertifiedStable934Transition
    (W : LinkageBlueprint Gamma Y kappa)
    (u : V) (T Z persistent B : Set V) where
  cut : LinkageBlueprint Gamma Y kappa
  current : LinkageBlueprint Gamma Y kappa
  endpoint : V
  continuation : Continuation930 W cut current u endpoint T B
  no_new_predecessors : W.NoNewPredecessorsTo current
  request : ClosureAdaptedAdvance931AuxiliaryLinkageRequest
    W current endpoint T Z persistent B

/-- Occurrence-aware concrete geometry certificate for one reachable 9.34
transition.  Its 9.31 request remains in the duplicated web until the
endpoint summary is compiled, avoiding the false contraction of split
connector occurrences to a literal simultaneous assignment. -/
structure OccurrenceCertifiedStable934Transition
    (W : LinkageBlueprint Gamma Y kappa)
    (u : V) (T Z persistent B : Set V) where
  cut : LinkageBlueprint Gamma Y kappa
  current : LinkageBlueprint Gamma Y kappa
  endpoint : V
  continuation : Continuation930 W cut current u endpoint T B
  no_new_predecessors : W.NoNewPredecessorsTo current
  request : OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
    W current endpoint T Z persistent B

/-- Source-faithful occurrence transition without an artificial predecessor
claim on the 9.30 continuation.  The 9.31 request still compiles through a
fresh attachment and therefore retains its own full-predecessor theorem; only
the composite 9.34 output forgets that field. -/
structure SourceOccurrenceCertifiedStable934Transition
    (W : LinkageBlueprint Gamma Y kappa)
    (u : V) (T Z persistent B : Set V) where
  cut : LinkageBlueprint Gamma Y kappa
  current : LinkageBlueprint Gamma Y kappa
  endpoint : V
  continuation : Continuation930 W cut current u endpoint T B
  request : OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
    W current endpoint T Z persistent B

/-- Compile one certified reachable transition using the two cardinal
induction hypotheses.  The result retains predecessor preservation for the
complete blueprint edge relation, including imaginary edges. -/
theorem CertifiedStable934Transition.compile
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {W : LinkageBlueprint Gamma Y kappa}
    {u : V} {T Z persistent B : Set V}
    (C : CertifiedStable934Transition W u T Z persistent B) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      FullyPredecessorPreservingStable934 W U u T Z persistent B := by
  obtain ⟨U, hU⟩ := C.request.exists_fullyPredecessorPreservingAdvance931
    hlower hext hGamma hYwarp hYfinite hassignment
    C.continuation.endpoint_mem_slice
  refine ⟨U, assertion934_of_930_931 C.continuation hU.advance, ?_⟩
  exact NoNewPredecessorsTo.trans C.no_new_predecessors
    hU.no_new_predecessors (by
      simpa only [realPart_vertices] using
        C.continuation.real_extends_to_endpoint.1.1)

/-- Compile an occurrence-aware reachable transition.  No normalization or
projected simultaneous-assignment hypothesis is needed: all path-sensitive
classification happened in the duplicated web when the request was built. -/
theorem OccurrenceCertifiedStable934Transition.compile
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {W : LinkageBlueprint Gamma Y kappa}
    {u : V} {T Z persistent B : Set V}
    (C : OccurrenceCertifiedStable934Transition W u T Z persistent B) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      FullyPredecessorPreservingStable934 W U u T Z persistent B := by
  obtain ⟨U, hU⟩ := C.request.exists_fullyPredecessorPreservingAdvance931
    hlower hext C.continuation.endpoint_mem_slice
  refine ⟨U, assertion934_of_930_931 C.continuation hU.advance, ?_⟩
  exact NoNewPredecessorsTo.trans C.no_new_predecessors
    hU.no_new_predecessors (by
      simpa only [realPart_vertices] using
        C.continuation.real_extends_to_endpoint.1.1)

/-- Compile the source-faithful occurrence transition to the literal 9.34
conclusion.  No predecessor statement is manufactured for the composite
9.30/9.31 transition. -/
theorem SourceOccurrenceCertifiedStable934Transition.compile
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {W : LinkageBlueprint Gamma Y kappa}
    {u : V} {T Z persistent B : Set V}
    (C : SourceOccurrenceCertifiedStable934Transition
      W u T Z persistent B) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      StableExtensionConclusion W U u T Z persistent B := by
  obtain ⟨U, hU⟩ := C.request.exists_fullyPredecessorPreservingAdvance931
    hlower hext C.continuation.endpoint_mem_slice
  exact ⟨U, assertion934_of_930_931 C.continuation hU.advance⟩

/-- Compatibility projection to the earlier real-edge package. -/
theorem FullyPredecessorPreservingStable934.toPredecessorPreserving
    {W U : LinkageBlueprint Gamma Y kappa}
    {u : V} {T Z persistent B : Set V}
    (h : FullyPredecessorPreservingStable934 W U u T Z persistent B) :
    PredecessorPreservingStable934 W U u T Z persistent B where
  conclusion := h.conclusion
  no_new_real_predecessors :=
    NoNewPredecessorsTo.toReal h.no_new_predecessors

def PredecessorPreservingStable934Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals → u ∈ T →
        ∃ U : LinkageBlueprint Gamma Y kappa,
          PredecessorPreservingStable934 W U u T Z persistent B

/-- Scheduler-facing stable successor retaining the full-edge predecessor
invariant. -/
def FullyPredecessorPreservingStable934Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals → u ∈ T →
        ∃ U : LinkageBlueprint Gamma Y kappa,
          FullyPredecessorPreservingStable934 W U u T Z persistent B

/-- The forward-only invariants of 9.30 and 9.31 compose across the
intermediate continuation. -/
theorem predecessorPreservingStable934Compiler_of_930_931
    {T Z persistent B : Set V}
    (h30 : PredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (h31 : PredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W u hW hpersistent hu huT
  obtain ⟨cut, V', z, hcontinuation, hnoNew30⟩ :=
    h30 W u hW hpersistent hu huT
  obtain ⟨U, hadvance⟩ := h31 W cut V' u z hW hcontinuation
  refine ⟨U, assertion934_of_930_931 hcontinuation hadvance.advance, ?_⟩
  exact hnoNew30.trans hadvance.no_new_real_predecessors
    hcontinuation.real_extends_to_endpoint.1.1

/-- The full-edge invariants of the scheduled continuation and fresh 9.31
attachment compose across their intermediate blueprint. -/
theorem fullyPredecessorPreservingStable934Compiler_of_930_931
    {T Z persistent B : Set V}
    (h30 : FullyPredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (h31 : FullyPredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    FullyPredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W u hW hpersistent hu huT
  obtain ⟨cut, V', z, hcontinuation, hnoNew30⟩ :=
    h30 W u hW hpersistent hu huT
  obtain ⟨U, hadvance⟩ := h31 W cut V' u z hW hcontinuation
  refine ⟨U, assertion934_of_930_931 hcontinuation hadvance.advance, ?_⟩
  apply hnoNew30.trans hadvance.no_new_predecessors
  simpa only [realPart_vertices] using
    hcontinuation.real_extends_to_endpoint.1.1

/-- Forget full-edge information and recover the existing real-edge stable
compiler interface. -/
theorem predecessorPreservingStable934Compiler_of_fullyPredecessorPreserving
    {T Z persistent B : Set V}
    (hfull : FullyPredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B := by
  intro W u hW hpersistent hu huT
  obtain ⟨U, hU⟩ := hfull W u hW hpersistent hu huT
  exact ⟨U, hU.toPredecessorPreserving⟩

/-- Fully assembled strengthened 9.34 compiler from the exact existential
9.31 transaction.  The scheduled-slice 9.30 construction is internal. -/
theorem predecessorPreservingStable934Compiler_of_classifiedSplice
    {T Z persistent B : Set V}
    (hsplice : ClassifiedWholeFamilyAdvanceSpliceCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  predecessorPreservingStable934Compiler_of_930_931
    predecessorPreservingContinuation930Compiler_of_scheduled_slice
    (predecessorPreservingAdvance931Compiler_of_classifiedSplice hsplice)

/-- Fully assembled forward-only 9.34 successor from compatible fresh
9.31 geometry. -/
theorem predecessorPreservingStable934Compiler_of_fresh
    {T Z persistent B : Set V}
    (hfresh : FreshAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  predecessorPreservingStable934Compiler_of_930_931
    predecessorPreservingContinuation930Compiler_of_scheduled_slice
    (predecessorPreservingAdvance931Compiler_of_fresh hfresh)

/-- Scheduler-facing full-predecessor compiler from compatible fresh 9.31
geometry.  This is the version appropriate for intermediate liminf stages
where imaginary edges have not yet disappeared. -/
theorem fullyPredecessorPreservingStable934Compiler_of_fresh
    {T Z persistent B : Set V}
    (hfresh : FreshAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    FullyPredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  fullyPredecessorPreservingStable934Compiler_of_930_931
    fullyPredecessorPreservingContinuation930Compiler_of_scheduled_slice
    (fullyPredecessorPreservingAdvance931Compiler_of_fresh hfresh)

/-- Strengthened 9.34 compiler obtained from the two induction hypotheses
and the honest auxiliary-linkage request for 9.31. -/
theorem predecessorPreservingStable934Compiler_of_auxiliaryLinkage
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {T Z persistent B : Set V}
    (hrequests : Advance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  predecessorPreservingStable934Compiler_of_930_931
    predecessorPreservingContinuation930Compiler_of_scheduled_slice
    (predecessorPreservingAdvance931Compiler_of_relation
      (advanceSpliceRelationCompiler_of_auxiliaryLinkage
        hlower hext hrequests))

/-- Forget the transition invariant and retain the original stable compiler
consumed by finite scheduler steps. -/
theorem stable934Compiler_of_predecessorPreserving
    {T Z persistent B : Set V}
    (h : PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B := by
  intro W u hW hpersistent hu huT
  obtain ⟨U, hU⟩ := h W u hW hpersistent hu huT
  exact ⟨U, hU.conclusion⟩

/-- Weak scheduler interface obtained from the exact existential 9.31
transaction. -/
theorem stable934Compiler_of_classifiedSplice
    {T Z persistent B : Set V}
    (hsplice : ClassifiedWholeFamilyAdvanceSpliceCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B :=
  stable934Compiler_of_predecessorPreserving
    (predecessorPreservingStable934Compiler_of_classifiedSplice hsplice)

/-- Scheduler-facing stable successor from compatible fresh 9.31
geometry. -/
theorem stable934Compiler_of_fresh
    {T Z persistent B : Set V}
    (hfresh : FreshAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B :=
  stable934Compiler_of_predecessorPreserving
    (predecessorPreservingStable934Compiler_of_fresh hfresh)

/-- Weak scheduler interface at the exact lower/current-cardinal source
seam. -/
theorem stable934Compiler_of_auxiliaryLinkage
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {T Z persistent B : Set V}
    (hrequests : Advance931AuxiliaryLinkageRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B :=
  stable934Compiler_of_predecessorPreserving
    (predecessorPreservingStable934Compiler_of_auxiliaryLinkage
      hlower hext hrequests)

/-- Source-facing forward-only stable compiler from the two repaired
Assertion 9.30--9.31 construction interfaces. -/
theorem predecessorPreservingStable934Compiler_of_930_globalFracturedSplice
    {T Z persistent B : Set V}
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    (h30 : PredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hrequests : ContinuationClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  predecessorPreservingStable934Compiler_of_930_931 h30
    (predecessorPreservingAdvance931Compiler_of_globalFracturedSplice
      hGamma hYwarp hYfinite hassignment hrequests hsplice)

/-- Reference-warp specialization of the forward-only stable successor.
This is the shortest scheduler-facing interface once 9.30 and the actual
continuation-aware relation splice have been constructed. -/
theorem predecessorPreservingStable934Compiler_of_930_referenceWarpSplice
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {T Z persistent B : Set V}
    (h30 : PredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  predecessorPreservingStable934Compiler_of_930_931 h30
    (predecessorPreservingAdvance931Compiler_of_referenceWarpSplice
      hGamma hYwarp hYfinite hYsource hYtarget hassignment hsplice)

/-- Fully assembled forward-only stable successor from the scheduled-slice
9.30 construction and a continuation-aware 9.31 relation splice. -/
theorem predecessorPreservingStable934Compiler_of_referenceWarpSplice
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {T Z persistent B : Set V}
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B :=
  predecessorPreservingStable934Compiler_of_930_referenceWarpSplice
    hGamma hYwarp hYfinite hYsource hYtarget hassignment
    predecessorPreservingContinuation930Compiler_of_scheduled_slice hsplice

/-- Assertions 9.30 and the continuation-aware global splice give the exact
stable successor compiler consumed by the terminal scheduler. -/
theorem stable934Compiler_of_930_globalFracturedSplice
    {T Z persistent B : Set V}
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    (h30 : Continuation930Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B)
    (hrequests : ContinuationClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B :=
  stable934Compiler_of_930_931 h30
    (advance931Compiler_of_globalFracturedSplice hGamma hYwarp hYfinite
      hassignment hrequests hsplice)

/-- Weak stable-successor form of the reference-warp specialization. -/
theorem stable934Compiler_of_930_referenceWarpSplice
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {T Z persistent B : Set V}
    (h30 : Continuation930Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B)
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B :=
  stable934Compiler_of_930_931 h30
    (advance931Compiler_of_referenceWarpSplice
      hGamma hYwarp hYfinite hYsource hYtarget hassignment hsplice)

/-- Weak scheduler interface obtained by forgetting the forward-only witness
from `predecessorPreservingStable934Compiler_of_referenceWarpSplice`. -/
theorem stable934Compiler_of_referenceWarpAdvanceSplice
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYsource : Gamma.initialSet Y ⊆ Gamma.source)
    (hYtarget : Gamma.terminalFrontier Y ⊆ Gamma.target)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    {T Z persistent B : Set V}
    (hsplice : WholeFamilyAdvanceSpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B :=
  stable934Compiler_of_predecessorPreserving
    (predecessorPreservingStable934Compiler_of_referenceWarpSplice
      hGamma hYwarp hYfinite hYsource hYtarget hassignment hsplice)

end LinkageBlueprint
end Blueprint
end Erdos599
