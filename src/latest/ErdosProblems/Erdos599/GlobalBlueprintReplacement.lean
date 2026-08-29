/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayContinuationRepair
import ErdosProblems.Erdos599.SimultaneousAssignment

/-!
# A global replacement interface for Assertions 9.30--9.31

Literal safeness of one alternating path is not a certificate that switching
along that path preserves the warp condition.  In particular, the proof of
Assertions 9.30--9.31 cannot soundly pass from `IsSafe Y Q` to a one-path
switch of the current blueprint.

This file gives the corresponding whole-family interface.  The outside
fragments are first packaged as a `FracturedWarp`.  The fractured
simultaneous-assignment theorem chooses all alternating continuations at
once.  A construction then orients one relation containing every compressed
finite assignment; its root-orbit decomposition is an actual blueprint.
Assignments to infinity account for every new terminal outside the current
slice.  Thus Claim 2 proves blueprint condition (6) without treating a
literal safe path as switching-safe.

`WholeFamilyOrientedReplacement` records the remaining geometric facts of
the construction at their exact source boundaries: Definition 9.27,
stability, the real path to the target, Definition (9.32), and preservation
of all other real terminals.  The final theorem composes these facts into
the `Stable934Compiler` consumed by the half-way terminal scheduler.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace LinkageBlueprint

/-! ## Boundary of a root-orbit blueprint

The source construction of Assertion 9.31 is most naturally stated for the
spliced edge relation: its initials are precisely the vertices without an
incoming edge and its finite terminals are precisely the vertices without an
outgoing edge.  The following lemmas expose those two facts for the canonical
root-orbit decomposition.  In particular, a later construction never has to
postulate a terminal set for a proposed path family. -/

/-- A carrier vertex is a root exactly when the oriented relation has no edge
entering it. -/
theorem forwardOrientation_isRoot_iff_no_incoming
    {D : Digraph V} (O : ForwardOrientation D) {x : V} :
    O.IsRoot x ↔ x ∈ O.carrier ∧ ¬ ∃ y, (y, x) ∈ O.edge := by
  constructor
  · rintro hx
    refine ⟨hx.1, ?_⟩
    rintro ⟨y, hyx⟩
    have hstep := O.depth_step hyx
    rw [hx.2] at hstep
    omega
  · rintro ⟨hxcarrier, hnoin⟩
    refine ⟨hxcarrier, ?_⟩
    by_contra hdepth
    have hpos : 0 < O.depth x := Nat.pos_of_ne_zero hdepth
    exact hnoin (O.predecessor hxcarrier hpos)

/-- Initials of the root-orbit blueprint are exactly the roots of the
orientation. -/
theorem orientationBlueprint_initialSet
    (O : ForwardOrientation (imaginaryGraph Gamma Y kappa)) :
    (orientationBlueprint O).initialSet = {x | O.IsRoot x} := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    rcases hp with ⟨r, rfl⟩
    change O.IsRoot x
    have hinit : (O.rootPath r).initial = r.1 := O.rootPath_initial r
    exact hpx ▸ hinit ▸ r.2
  · intro hx
    let r : O.Root := ⟨x, hx⟩
    exact ⟨O.rootPath r, ⟨r, rfl⟩, O.rootPath_initial r⟩

/-- Initials of the root-orbit blueprint, expressed using only the carrier
and edge relation supplied to the orientation constructor. -/
theorem orientationBlueprint_initialSet_eq_no_incoming
    (O : ForwardOrientation (imaginaryGraph Gamma Y kappa)) :
    (orientationBlueprint O).initialSet =
      {x | x ∈ O.carrier ∧ ¬ ∃ y, (y, x) ∈ O.edge} := by
  rw [orientationBlueprint_initialSet]
  ext x
  exact forwardOrientation_isRoot_iff_no_incoming O

/-- Finite terminals of the root-orbit blueprint are exactly the carrier
vertices with no outgoing relation edge.  Infinite root orbits contribute no
terminal, as required by the definition of a warp frontier. -/
theorem orientationBlueprint_terminalSet_eq_no_outgoing
    (O : ForwardOrientation (imaginaryGraph Gamma Y kappa)) :
    (orientationBlueprint O).terminalSet =
      {x | x ∈ O.carrier ∧ ¬ ∃ y, (x, y) ∈ O.edge} := by
  ext x
  constructor
  · rintro ⟨p, hp, hterm⟩
    rcases hp with ⟨r, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← orientationBlueprint_vertexSet O]
      exact ⟨O.rootPath r, ⟨r, rfl⟩,
        (imaginaryWeb Gamma Y kappa).terminal_mem_support hterm⟩
    · simp only [ForwardOrientation.rootPath] at hterm
      split at hterm <;> rename_i hstop
      · exact nomatch hterm
      · simp only [DWeb.terminal?, DirectedPath.Path.terminal?,
          DirectedPath.Path.terminal?_finite, Option.some.injEq] at hterm
        subst x
        exact O.not_hasNext_stoppingIndex hstop
  · rintro ⟨hxcarrier, hnoout⟩
    by_contra hnotterminal
    obtain ⟨y, hy⟩ :=
      (orientationBlueprint O).exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
        (by rw [orientationBlueprint_vertexSet O]; exact hxcarrier)
        hnotterminal
    apply hnoout
    rw [orientationBlueprint_edgeSet O] at hy
    exact ⟨y, hy⟩

/-- Source-faithful input to the global assignment step of Assertion 9.31.

The four closure sets are the sets called `X`, the preceding closed set, the
inner roof, and the ambient roof in the closing-up construction.  Keeping
them in the request makes the two Claim 2 conclusions derivable rather than
postulated. -/
structure ClosedFracturedReplacementRequest (persistent : Set V) where
  fractured : FracturedWarp Gamma
  closureSet : Set V
  before : Set V
  innerRoof : Set V
  outerRoof : Set V
  source_side : Gamma.initialSet fractured.paths ⊆ Gamma.source
  target_side : Gamma.terminalFrontier fractured.paths ⊆ Gamma.target
  finite_character : Gamma.HasFiniteCharacter fractured.paths
  reference_initials : Gamma.initialSet Y ⊆
    Gamma.initialSet fractured.paths
  closed : HammockClosedUpTo Gamma Y closureSet before innerRoof outerRoof
    kappa
  closure_facts : ∀ A : SimultaneousAssignment fractured.paths Y,
    AssignmentClosureContext A closureSet before innerRoof outerRoof

/-- A provider for the closed fractured family attached to one scheduled
real terminal.  This is the geometric closing-up part of Assertions
9.22--9.31, before applying Theorem 4.12. -/
def ClosedFracturedReplacementRequestProvider
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        Nonempty (ClosedFracturedReplacementRequest
          (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent)

/-! ## The source-level splice relation

Assertion 9.31 first forms one relation from all inside linkage fragments and
all finite compressed assignments, and only then decomposes that relation
into paths.  The following definitions state the invariants of that relation
without presupposing the result warp. -/

/-- Real edges of a proposed whole-family relation. -/
def relationRealEdges (E : Set (V × V)) : Set (V × V) :=
  E ∩ {e | Gamma.graph.Adj e.1 e.2}

/-- Real terminals of a proposed whole-family relation with an explicit
carrier. -/
def relationRealTerminals (E : Set (V × V)) (carrier : Set V) : Set V :=
  carrier \ {x | ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) E}

/-- Vertices accounted for by a completed real path in a proposed relation;
this is the relation-level form of the last set in (9.32). -/
def relationCompletedRealVertices (E : Set (V × V))
    (carrier B : Set V) : Set V :=
  {x | ∃ p : FinitePath Gamma.graph,
    p.finish ∈ B ∧ p.support ⊆ carrier ∧
      p.edgeSet ⊆ relationRealEdges (Gamma := Gamma) E ∧ x ∈ p.support}

/-- Exact low-level output of the simultaneous splice in Assertion 9.31.

`edge` is the union of the inside-linkage fragments and all finite assigned
compressed edges.  The first five fields are precisely what is needed to
apply the relation-decomposition theorem.  All remaining fields are phrased
in terms of roots, sinks, and real edges of that single relation. -/
structure WholeFamilySpliceRelation
    (W : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (A : SimultaneousAssignment Zf.paths Y)
    (u : V) (T Z persistent B : Set V) where
  edge : Set (V × V)
  carrier : Set V
  edge_in_graph : edge ⊆
    {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2}
  endpoints_mem : ∀ e ∈ edge, e.1 ∈ carrier ∧ e.2 ∈ carrier
  biunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ edge)
  no_directed_cycle : ¬ ContainsDirectedCycle edge
  no_reverse_ray : ¬ ContainsReverseDirectedRay edge
  assigned_edges : assignedFiniteEdges A ⊆ edge
  infinite_sources_sink : assignedInfiniteSources A ⊆
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge}
  sink_boundary : {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge} ⊆
    assignedInfiniteSources A ∪ T
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
  old_real_vertices : W.realPart.vertices ⊆ carrier
  old_real_edges : W.realPart.edges ⊆
    relationRealEdges (Gamma := Gamma) edge
  old_vertices_accounted : W.vertexSet ⊆
    ({x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge} ∩ W.terminalSet) ∪
      {x | ∃ y, (x, y) ∈ W.familyGraph.edges ∩ edge} ∪
        relationCompletedRealVertices (Gamma := Gamma) edge carrier B
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = u
  target_path_finish : target_path.finish ∈ B
  target_path_vertices : target_path.support ⊆ carrier
  target_path_edges : target_path.edgeSet ⊆
    relationRealEdges (Gamma := Gamma) edge
  preserves_other_real_terminals :
    W.realPart.terminals \ {u} ⊆
      relationRealTerminals (Gamma := Gamma) edge carrier

/-- Endpoint-summary form of the low-level 9.31 splice relation.

This is the sound target of the occurrence-aware Remark 4.20 construction:
only compressed finite endpoint edges and infinite source markers occur in
the relation boundary.  No projection of a split-web alternating path to an
original-web safe path is asserted. -/
structure CompressedWholeFamilySpliceRelation
    (W : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (A : CompressedFracturedAssignment Zf Y)
    (u : V) (T Z persistent B : Set V) where
  edge : Set (V × V)
  carrier : Set V
  edge_in_graph : edge ⊆
    {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2}
  endpoints_mem : ∀ e ∈ edge, e.1 ∈ carrier ∧ e.2 ∈ carrier
  biunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ edge)
  no_directed_cycle : ¬ ContainsDirectedCycle edge
  no_reverse_ray : ¬ ContainsReverseDirectedRay edge
  assigned_edges : A.finiteEdges ⊆ edge
  infinite_sources_sink : A.infiniteSources ⊆
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge}
  sink_boundary : {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge} ⊆
    A.infiniteSources ∪ T
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
  old_real_vertices : W.realPart.vertices ⊆ carrier
  old_real_edges : W.realPart.edges ⊆
    relationRealEdges (Gamma := Gamma) edge
  old_vertices_accounted : W.vertexSet ⊆
    ({x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ edge} ∩ W.terminalSet) ∪
      {x | ∃ y, (x, y) ∈ W.familyGraph.edges ∩ edge} ∪
        relationCompletedRealVertices (Gamma := Gamma) edge carrier B
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = u
  target_path_finish : target_path.finish ∈ B
  target_path_vertices : target_path.support ⊆ carrier
  target_path_edges : target_path.edgeSet ⊆
    relationRealEdges (Gamma := Gamma) edge
  preserves_other_real_terminals :
    W.realPart.terminals \ {u} ⊆
      relationRealTerminals (Gamma := Gamma) edge carrier

/-- Every path-rich simultaneous splice has the endpoint-summary form.
This is a definitional forgetting map; it performs no path projection. -/
def WholeFamilySpliceRelation.toCompressed
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (S : WholeFamilySpliceRelation W A u T Z persistent B) :
    CompressedWholeFamilySpliceRelation W
      (CompressedFracturedAssignment.ofSimultaneous A)
      u T Z persistent B where
  edge := S.edge
  carrier := S.carrier
  edge_in_graph := S.edge_in_graph
  endpoints_mem := S.endpoints_mem
  biunique := S.biunique
  no_directed_cycle := S.no_directed_cycle
  no_reverse_ray := S.no_reverse_ray
  assigned_edges := by simpa using S.assigned_edges
  infinite_sources_sink := by simpa using S.infinite_sources_sink
  sink_boundary := by simpa using S.sink_boundary
  vertices_roofed := S.vertices_roofed
  covers_source := S.covers_source
  vertices_closed := S.vertices_closed
  card_carrier := S.card_carrier
  every_relation_ray_strong := S.every_relation_ray_strong
  stable_boundary := S.stable_boundary
  old_real_vertices := S.old_real_vertices
  old_real_edges := S.old_real_edges
  old_vertices_accounted := S.old_vertices_accounted
  target_path := S.target_path
  target_path_start := S.target_path_start
  target_path_finish := S.target_path_finish
  target_path_vertices := S.target_path_vertices
  target_path_edges := S.target_path_edges
  preserves_other_real_terminals := S.preserves_other_real_terminals

/-- The low-level output of one simultaneous, whole-family splice.

The result blueprint is not supplied independently.  It is definitionally
the root-orbit decomposition `orientationBlueprint orientation`, so the
warp condition is constructed by the relation-decomposition theorem.

`assigned_edges` and `infinite_sources_terminal` say that the construction
really consumes the whole simultaneous assignment.  `terminal_boundary`
is the exact boundary fact used to derive blueprint condition (6): every
terminal outside the current slice is the start of an infinite assigned
alternating path and hence is popular by Claim 2. -/
structure WholeFamilyOrientedReplacement
    (W : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (A : SimultaneousAssignment Zf.paths Y)
    (u : V) (T Z persistent B : Set V) where
  orientation : ForwardOrientation (imaginaryGraph Gamma Y kappa)
  assigned_edges : assignedFiniteEdges A ⊆ orientation.edge
  infinite_sources_terminal : assignedInfiniteSources A ⊆
    (orientationBlueprint orientation).terminalSet
  terminal_boundary : (orientationBlueprint orientation).terminalSet ⊆
    assignedInfiniteSources A ∪ T
  vertices_roofed : (orientationBlueprint orientation).vertexSet ⊆
    Gamma.roof T
  covers_source : Gamma.source ⊆
    (orientationBlueprint orientation).initialSet ∪
      (orientationBlueprint orientation).retainedReferenceInitials T
  vertices_closed : (orientationBlueprint orientation).vertexSet ⊆ Z
  card_paths : #(orientationBlueprint orientation).paths ≤ kappa
  infinitely_many_strong :
    (orientationBlueprint orientation).InfinitelyManyStrongEdges
  stable_boundary :
    (orientationBlueprint orientation).terminalSet ∩ T ⊆ persistent
  real_part_extends : W.realPart.Extends
    (orientationBlueprint orientation).realPart
  old_vertices_accounted : W.vertexSet ⊆
    ((orientationBlueprint orientation).terminalSet ∩ W.terminalSet) ∪
      {x | ∃ y,
        (x, y) ∈ W.familyGraph.edges ∩
          (orientationBlueprint orientation).familyGraph.edges} ∪
        (orientationBlueprint orientation).completedRealVertices B
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = u
  target_path_finish : target_path.finish ∈ B
  target_path_vertices : target_path.support ⊆
    (orientationBlueprint orientation).realPart.vertices
  target_path_edges : target_path.edgeSet ⊆
    (orientationBlueprint orientation).realPart.edges
  preserves_other_real_terminals :
    W.realPart.terminals \ {u} ⊆
      (orientationBlueprint orientation).realPart.terminals

/-- Compile the one source-level splice relation into the oriented
whole-family replacement.  Pairwise disjointness of the output paths is not
an assumption: it is supplied by `ForwardOrientation.rootPaths_pairwiseDisjoint`.
The root and sink boundary lemmas above translate every source invariant
without changing the successor slice or the persistent set. -/
theorem WholeFamilySpliceRelation.exists_orientedReplacement
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (S : WholeFamilySpliceRelation W A u T Z persistent B) :
    Nonempty (WholeFamilyOrientedReplacement W A u T Z persistent B) := by
  obtain ⟨O, hOE, hOC⟩ := exists_forwardOrientation_exact
    S.edge S.carrier S.edge_in_graph S.endpoints_mem S.biunique
      S.no_directed_cycle S.no_reverse_ray
  refine ⟨{
    orientation := O
    assigned_edges := ?_
    infinite_sources_terminal := ?_
    terminal_boundary := ?_
    vertices_roofed := ?_
    covers_source := ?_
    vertices_closed := ?_
    card_paths := ?_
    infinitely_many_strong := ?_
    stable_boundary := ?_
    real_part_extends := ?_
    old_vertices_accounted := ?_
    target_path := S.target_path
    target_path_start := S.target_path_start
    target_path_finish := S.target_path_finish
    target_path_vertices := ?_
    target_path_edges := ?_
    preserves_other_real_terminals := ?_ }⟩
  · rw [hOE]
    exact S.assigned_edges
  · intro x hx
    rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
    exact S.infinite_sources_sink hx
  · rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
    exact S.sink_boundary
  · rw [orientationBlueprint_vertexSet, hOC]
    exact S.vertices_roofed
  · rw [orientationBlueprint_initialSet_eq_no_incoming,
      retainedReferenceInitials, orientationBlueprint_vertexSet, hOC, hOE]
    exact S.covers_source
  · rw [orientationBlueprint_vertexSet, hOC]
    exact S.vertices_closed
  · change #(Set.range O.rootPath) ≤ kappa
    refine Cardinal.mk_range_le.trans ?_
    refine (Cardinal.mk_subtype_mono (fun x hx ↦ hx.1)).trans ?_
    simpa only [hOC] using S.card_carrier
  · intro r hr
    apply S.every_relation_ray_strong r
    intro e he
    rw [← hOE, ← orientationBlueprint_edgeSet O]
    exact Set.mem_iUnion.2 ⟨(Sum.inr r :
      DirectedPath.Path (imaginaryGraph Gamma Y kappa)),
        Set.mem_iUnion.2 ⟨hr, he⟩⟩
  · rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
    exact S.stable_boundary
  · constructor
    · simpa only [realPart_vertices, orientationBlueprint_vertexSet, hOC]
        using S.old_real_vertices
    · simpa only [realPart_edges, orientationBlueprint_edgeSet, hOE,
        relationRealEdges] using S.old_real_edges
  · intro x hx
    rcases S.old_vertices_accounted hx with
      (hterminal | hcommon) | hcompleted
    · apply Or.inl
      apply Or.inl
      refine ⟨?_, hterminal.2⟩
      rw [orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
      exact hterminal.1
    · apply Or.inl
      apply Or.inr
      rcases hcommon with ⟨y, hyW, hyS⟩
      refine ⟨y, hyW, ?_⟩
      change (x, y) ∈ (orientationBlueprint O).edgeSet
      rw [orientationBlueprint_edgeSet, hOE]
      exact hyS
    · apply Or.inr
      rcases hcompleted with ⟨p, hpB, hpvertex, hpedge, hxp⟩
      refine ⟨p, hpB, ?_, ?_, hxp⟩
      · simpa only [realPart_vertices, orientationBlueprint_vertexSet, hOC]
          using hpvertex
      · simpa only [realPart_edges, orientationBlueprint_edgeSet, hOE,
          relationRealEdges] using hpedge
  · simpa only [realPart_vertices, orientationBlueprint_vertexSet, hOC]
      using S.target_path_vertices
  · simpa only [realPart_edges, orientationBlueprint_edgeSet, hOE,
      relationRealEdges] using S.target_path_edges
  · simpa only [FamilyGraph.terminals, FamilyGraph.tails, realPart_vertices,
      realPart_edges, orientationBlueprint_vertexSet, orientationBlueprint_edgeSet,
      hOC, hOE, relationRealTerminals, relationRealEdges]
      using S.preserves_other_real_terminals

/-- The actual blueprint constructed by a whole-family replacement. -/
def WholeFamilyOrientedReplacement.result
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B) :
    LinkageBlueprint Gamma Y kappa :=
  orientationBlueprint R.orientation

@[simp] theorem WholeFamilyOrientedReplacement.result_eq
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B) :
    R.result = orientationBlueprint R.orientation :=
  rfl

/-- Every finite member of the simultaneous assignment is represented in
the edge relation of the actual result blueprint. -/
theorem WholeFamilyOrientedReplacement.assignedFiniteEdges_subset_result
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B) :
    assignedFiniteEdges A ⊆ R.result.edgeSet := by
  rw [result, orientationBlueprint_edgeSet]
  exact R.assigned_edges

/-- The carrier of the oriented splice is exactly the vertex set of its
root-orbit blueprint, including isolated depth-zero vertices. -/
theorem WholeFamilyOrientedReplacement.result_vertexSet
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B) :
    R.result.vertexSet = R.orientation.carrier := by
  exact orientationBlueprint_vertexSet R.orientation

/-- Outside the current slice, the terminals of the result are exactly the
sources which the simultaneous assignment sends to infinity.  This is the
boundary identity behind blueprint condition (6). -/
theorem WholeFamilyOrientedReplacement.terminalSet_sdiff_slice
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B) :
    R.result.terminalSet \ T = assignedInfiniteSources A \ T := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxterminal, hxT⟩
    rcases R.terminal_boundary hxterminal with hxinf | hxT'
    · exact ⟨hxinf, hxT⟩
    · exact (hxT hxT').elim
  · rintro x ⟨hxinf, hxT⟩
    exact ⟨R.infinite_sources_terminal hxinf, hxT⟩

/-- Claim 2 plus the terminal-boundary invariant proves blueprint condition
(6) for the globally oriented family. -/
theorem WholeFamilyOrientedReplacement.terminals_popular
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B)
    (hinfinite : ∀ s, (A.assigned s).IsInfinite →
      IsPopular Gamma Y persistent kappa s.1) :
    R.result.terminalSet ⊆
      {x | IsPopular Gamma Y persistent kappa x} ∪ T := by
  intro x hx
  rcases R.terminal_boundary hx with hxinf | hxT
  · exact Or.inl (assignedInfiniteSources_popular A hinfinite hxinf)
  · exact Or.inr hxT

/-- A whole-family oriented replacement has all six blueprint properties.
The only property not stored verbatim is condition (6), which is derived
from the simultaneous assignment and Claim 2. -/
theorem WholeFamilyOrientedReplacement.isLinkageBlueprint
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B)
    (hinfinite : ∀ s, (A.assigned s).IsInfinite →
      IsPopular Gamma Y persistent kappa s.1) :
    R.result.IsLinkageBlueprint T Z persistent := by
  exact {
    vertices_roofed := R.vertices_roofed
    covers_source := R.covers_source
    vertices_closed := R.vertices_closed
    card_paths := R.card_paths
    infinitely_many_strong := R.infinitely_many_strong
    terminals_popular := R.terminals_popular hinfinite }

/-- The stored boundary inclusion is precisely Definition 9.29. -/
theorem WholeFamilyOrientedReplacement.stable
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B) :
    R.result.Stable T persistent :=
  R.stable_boundary

/-- The whole-family accounting fields are exactly Definition (9.32). -/
theorem WholeFamilyOrientedReplacement.realExtends
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B) :
    W.RealExtends R.result B :=
  ⟨R.real_part_extends, R.old_vertices_accounted⟩

/-- The designated real path survives as a path from the scheduled terminal
to the target side. -/
theorem WholeFamilyOrientedReplacement.realLinksTo
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B) :
    R.result.RealLinksTo u B :=
  ⟨R.target_path, R.target_path_start, R.target_path_finish,
    R.target_path_vertices, R.target_path_edges⟩

/-- A classified whole-family replacement gives the exact stable successor
required by Assertion 9.34. -/
theorem WholeFamilyOrientedReplacement.stableExtensionConclusion
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma}
    {A : SimultaneousAssignment Zf.paths Y}
    {u : V} {T Z persistent B : Set V}
    (R : WholeFamilyOrientedReplacement W A u T Z persistent B)
    (hinfinite : ∀ s, (A.assigned s).IsInfinite →
      IsPopular Gamma Y persistent kappa s.1) :
    StableExtensionConclusion W R.result u T Z persistent B := by
  exact ⟨R.isLinkageBlueprint hinfinite, R.stable, R.realExtends,
    R.realLinksTo, R.preserves_other_real_terminals⟩

/-- The construction-specific compiler after the simultaneous assignment
has been chosen and classified by Claim 2.  It is intentionally a
whole-family interface: no individual assigned path is ever switched. -/
def WholeFamilyOrientedReplacementCompiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
      ∀ (R : ClosedFracturedReplacementRequest
          (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent)
        (A : SimultaneousAssignment R.fractured.paths Y),
        (∀ s v, (A.assigned s).terminal? = some v →
          IsImaginaryEdge Gamma Y kappa s.1 v) →
        (∀ s, (A.assigned s).IsInfinite →
          IsPopular Gamma Y persistent kappa s.1) →
        Nonempty (WholeFamilyOrientedReplacement W A u T Z persistent B)

/-- Construction compiler stated at the source-faithful relation level.
Unlike `WholeFamilyOrientedReplacementCompiler`, this interface asks for no
result blueprint and no orientation: the whole-family edge relation and its
geometric invariants are the output. -/
def WholeFamilySpliceRelationCompiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
      ∀ (R : ClosedFracturedReplacementRequest
          (Gamma := Gamma) (Y := Y) (kappa := kappa) persistent)
        (A : SimultaneousAssignment R.fractured.paths Y),
        (∀ s v, (A.assigned s).terminal? = some v →
          IsImaginaryEdge Gamma Y kappa s.1 v) →
        (∀ s, (A.assigned s).IsInfinite →
          IsPopular Gamma Y persistent kappa s.1) →
        Nonempty (WholeFamilySpliceRelation W A u T Z persistent B)

/-- Relation-level construction implies the oriented replacement compiler by
the root-orbit decomposition. -/
theorem wholeFamilyOrientedReplacementCompiler_of_spliceRelation
    {T Z persistent B : Set V}
    (hsplice : WholeFamilySpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    WholeFamilyOrientedReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B := by
  intro W u hW hpersistent hu R A hfinite hinfinite
  exact (hsplice W u hW hpersistent hu R A hfinite hinfinite).some
    |>.exists_orientedReplacement

/-- Sound global replacement for Assertions 9.30--9.31.

For each scheduled real terminal, the closing-up provider returns one
fractured family.  `FracturedSimultaneousAssignmentStatement` chooses all
continuations at once.  Claim 2 classifies their finite and infinite ends,
and the construction compiler orients the resulting whole-family relation.
The root-orbit blueprint is then an exact stable 9.34 successor.

There is no hypothesis, intermediate fact, or conclusion asserting
`IsSafe Y Q → IsSwitchingSafe Y Q`. -/
theorem stable934Compiler_of_globalFracturedReplacement
    {T Z persistent B : Set V}
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    (hrequests : ClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (hcompile : WholeFamilyOrientedReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B := by
  intro W u hW hpersistent hu _huT
  let R := (hrequests W u hW hpersistent hu).some
  let A : SimultaneousAssignment R.fractured.paths Y :=
    (hassignment hGamma R.fractured Y R.source_side R.target_side hYwarp
      R.finite_character hYfinite R.reference_initials).some
  have hclassified :=
    classify_simultaneousAssignment_of_closed (persistent := persistent)
      R.closed A (R.closure_facts A)
  let C := (hcompile W u hW hpersistent hu R A hclassified.1
    hclassified.2).some
  exact ⟨C.result, C.stableExtensionConclusion hclassified.2⟩

/-- Source-faithful variant of the global 9.31 compiler.  The caller builds
only the closed fractured family and its single splice relation; the result
warp, all its paths, and their disjointness are constructed internally. -/
theorem stable934Compiler_of_globalFracturedSplice
    {T Z persistent B : Set V}
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    (hrequests : ClosedFracturedReplacementRequestProvider
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (hsplice : WholeFamilySpliceRelationCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      T Z persistent B :=
  stable934Compiler_of_globalFracturedReplacement hGamma hYwarp hYfinite
    hassignment hrequests
      (wholeFamilyOrientedReplacementCompiler_of_spliceRelation hsplice)

end LinkageBlueprint
end Blueprint
end Erdos599
