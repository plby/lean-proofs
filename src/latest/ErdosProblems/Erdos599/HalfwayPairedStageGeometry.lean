/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClosedEndpointPairing
import ErdosProblems.Erdos599.HalfwayStageGeometry
import ErdosProblems.Erdos599.HalfwayScheduler

/-!
# Club-stage geometry for a closed endpoint pairing

`ClosedEndpointPairing` is the source-faithful output required at the cut in
Assertion 9.31.  The downstream relation construction uses only its finite
endpoint relation and its set of sources paired with infinity.  This file
provides the corresponding club-stage datum and a one-transaction compiler
to `RankedFairGlobalRelation`; it never reconstructs a stronger
`SimultaneousAssignment`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- The literal inside-fragment/finite-pair union at one club stage.

Every field is below the final orientation.  In particular, `inside` and
`carrier` are concrete relations and vertex sets, while the result warp will
be the canonical root-orbit decomposition constructed by the scheduler. -/
structure PairedClubStageUnionData
    (C : ClubStageGeometry Gamma Y kappa theta)
    (W : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma} {X before innerRoof outerRoof : Set V}
    (A : ClosedEndpointPairing (Gamma := Gamma) (Y := Y)
      Zf X before innerRoof outerRoof)
    (u : V) where
  inside : Set (V × V)
  carrier : Set V
  inside_in_graph : inside ⊆
    {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2}
  inside_endpoints : ∀ e ∈ inside,
    e.1 ∈ carrier ∧ e.2 ∈ carrier
  paired_endpoints : ∀ e ∈ A.finiteEdges,
    e.1 ∈ carrier ∧ e.2 ∈ carrier
  inside_biunique : Relator.BiUnique (fun x y => (x, y) ∈ inside)
  cross_in : ∀ {x y z}, (x, z) ∈ inside ->
    (y, z) ∈ A.finiteEdges -> x = y
  cross_out : ∀ {x y z}, (x, y) ∈ inside ->
    (x, z) ∈ A.finiteEdges -> y = z
  rank : V -> Nat
  inside_rank : ∀ {x y}, (x, y) ∈ inside -> rank x < rank y
  paired_rank : ∀ {x y}, (x, y) ∈ A.finiteEdges -> rank x < rank y
  infinite_sources_sink : A.infiniteSources ⊆
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ inside ∪ A.finiteEdges}
  sink_boundary :
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ inside ∪ A.finiteEdges} ⊆
      A.infiniteSources ∪ C.newSlice
  carrier_roofed : carrier ⊆ C.outerRoof
  covers_source : Gamma.source ⊆
    {x | x ∈ carrier ∧ ¬ ∃ y,
      (y, x) ∈ inside ∪ A.finiteEdges} ∪
      Gamma.initialSet
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y carrier)
  carrier_closed : carrier ⊆ C.closedSet
  card_carrier : #carrier ≤ kappa
  every_relation_ray_strong :
    ∀ r : Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ inside ∪ A.finiteEdges ->
        (strongEdgeIndices r).Infinite
  stable_boundary :
    {x | x ∈ carrier ∧ ¬ ∃ y,
      (x, y) ∈ inside ∪ A.finiteEdges} ∩ C.newSlice ⊆ C.persistent
  old_real_vertices : W.realPart.vertices ⊆ carrier
  old_real_edges : W.realPart.edges ⊆
    relationRealEdges (Gamma := Gamma) (inside ∪ A.finiteEdges)
  old_vertices_accounted : W.vertexSet ⊆
    ({x | x ∈ carrier ∧ ¬ ∃ y,
      (x, y) ∈ inside ∪ A.finiteEdges} ∩ W.terminalSet) ∪
      {x | ∃ y,
        (x, y) ∈ W.familyGraph.edges ∩ (inside ∪ A.finiteEdges)} ∪
        relationCompletedRealVertices (Gamma := Gamma)
          (inside ∪ A.finiteEdges) carrier Gamma.target
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = u
  target_path_finish : target_path.finish ∈ Gamma.target
  target_path_vertices : target_path.support ⊆ carrier
  target_path_edges : target_path.edgeSet ⊆
    relationRealEdges (Gamma := Gamma) (inside ∪ A.finiteEdges)
  preserves_other_real_terminals :
    W.realPart.terminals \ {u} ⊆
      relationRealTerminals (Gamma := Gamma)
        (inside ∪ A.finiteEdges) carrier

namespace PairedClubStageUnionData

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {W : LinkageBlueprint Gamma Y kappa}
variable {Zf : FracturedWarp Gamma} {X before innerRoof outerRoof : Set V}
variable {A : ClosedEndpointPairing (Gamma := Gamma) (Y := Y)
  Zf X before innerRoof outerRoof} {u : V}

/-- The full real/imaginary relation before taking its original-web part. -/
def fullEdge (D : PairedClubStageUnionData C W A u) : Set (V × V) :=
  D.inside ∪ A.finiteEdges

/-- The surviving original-web relation used by the final scheduler. -/
def realEdge (D : PairedClubStageUnionData C W A u) : Set (V × V) :=
  relationRealEdges (Gamma := Gamma) D.fullEdge

theorem fullEdge_biunique (D : PairedClubStageUnionData C W A u) :
    Relator.BiUnique (fun x y => (x, y) ∈ D.fullEdge) := by
  exact biUnique_union_of_cross D.inside_biunique A.finiteEdges_biUnique
    D.cross_in D.cross_out

theorem realEdge_subset_fullEdge (D : PairedClubStageUnionData C W A u) :
    D.realEdge ⊆ D.fullEdge := by
  intro e he
  exact he.1

theorem realEdge_endpoints (D : PairedClubStageUnionData C W A u) :
    ∀ e ∈ D.realEdge, e.1 ∈ D.carrier ∧ e.2 ∈ D.carrier := by
  intro e he
  rcases he.1 with heInside | hePair
  · exact D.inside_endpoints e heInside
  · exact D.paired_endpoints e hePair

theorem realEdge_biunique (D : PairedClubStageUnionData C W A u) :
    Relator.BiUnique (fun x y => (x, y) ∈ D.realEdge) := by
  constructor
  · intro x y z hxz hyz
    exact D.fullEdge_biunique.1 hxz.1 hyz.1
  · intro x y z hxy hxz
    exact D.fullEdge_biunique.2 hxy.1 hxz.1

theorem realEdge_rank (D : PairedClubStageUnionData C W A u) :
    ∀ {x y}, (x, y) ∈ D.realEdge -> D.rank x < D.rank y := by
  intro x y hxy
  rcases hxy.1 with hInside | hPair
  · exact D.inside_rank hInside
  · exact D.paired_rank hPair

theorem realEdge_in_graph (D : PairedClubStageUnionData C W A u) :
    D.realEdge ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  exact he.2

end PairedClubStageUnionData

/-- A concrete original-web target route embedded in a paired transaction. -/
structure PairedEmbeddedTargetRoute
    {C : ClubStageGeometry Gamma Y kappa theta}
    {W : LinkageBlueprint Gamma Y kappa}
    {Zf : FracturedWarp Gamma} {X before innerRoof outerRoof : Set V}
    {A : ClosedEndpointPairing (Gamma := Gamma) (Y := Y)
      Zf X before innerRoof outerRoof}
    {u : V} (D : PairedClubStageUnionData C W A u) (x : V) where
  path : FinitePath Gamma.graph
  start : path.start = x
  finish : path.finish ∈ Gamma.target
  support : path.support ⊆ D.carrier
  edges : path.edgeSet ⊆ D.realEdge

/-- One closed endpoint-pairing transaction.

`resolve` is the genuine global scheduling input: every non-target sink of
the common real relation has an embedded route to the ambient target in that
same relation. -/
structure PairedSingleGlobalTransaction
    (C : ClubStageGeometry Gamma Y kappa theta) where
  blueprint : LinkageBlueprint Gamma Y kappa
  fractured : FracturedWarp Gamma
  closureSet : Set V
  before : Set V
  innerRoof : Set V
  outerRoof : Set V
  pairing : ClosedEndpointPairing (Gamma := Gamma) (Y := Y)
    fractured closureSet before innerRoof outerRoof
  anchor : V
  data : PairedClubStageUnionData C blueprint pairing anchor
  resolve : ∀ x,
    x ∈ data.carrier ->
    (¬ ∃ y, (x, y) ∈ data.realEdge) ->
    x ∉ Gamma.target ->
    Nonempty (PairedEmbeddedTargetRoute data x)

namespace PairedSingleGlobalTransaction

variable {C : ClubStageGeometry Gamma Y kappa theta}

/-- A singleton index for the one common closed transaction. -/
inductive StageIndex : Type
  | stage

namespace StageIndex

instance : Nonempty StageIndex := ⟨.stage⟩

instance : Preorder StageIndex where
  le _ _ := True
  le_refl _ := True.intro
  le_trans _ _ _ _ _ := True.intro

instance : IsDirectedOrder StageIndex where
  directed _ _ := ⟨.stage, True.intro, True.intro⟩

end StageIndex

/-- The pairing transaction has no non-target sink. -/
theorem no_nonTarget_sink (T : PairedSingleGlobalTransaction C) (x : V)
    (hx : x ∈ T.data.carrier)
    (hno : ¬ ∃ y, (x, y) ∈ T.data.realEdge)
    (htarget : x ∉ Gamma.target) : False := by
  obtain ⟨R⟩ := T.resolve x hx hno htarget
  have hne : R.path.start ≠ R.path.finish := by
    intro h
    apply htarget
    rw [← R.start, h]
    exact R.finish
  obtain ⟨y, hy⟩ :=
    FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      R.path R.path.start_mem_support hne
  rw [R.start] at hy
  exact hno ⟨y, R.edges hy⟩

/-- Compile the concrete paired transaction directly to the exact relation
consumed by the final scheduler. -/
def rankedFairGlobalRelation (T : PairedSingleGlobalTransaction C) :
    CardinalInduction.HalfwayScheduler.RankedFairGlobalRelation
      Gamma Y kappa Gamma.target StageIndex where
  edge := T.data.realEdge
  carrier := T.data.carrier
  rank := T.data.rank
  endpoints_mem := T.data.realEdge_endpoints
  biunique := T.data.realEdge_biunique
  rank_step := T.data.realEdge_rank
  edge_real := T.data.realEdge_in_graph
  scheduled := fun _ => T.anchor
  fair := by
    intro x hx hno htarget
    exfalso
    exact T.no_nonTarget_sink x hx hno htarget
  targetPath := fun _ => T.data.target_path
  targetPath_start := fun _ => T.data.target_path_start
  targetPath_finish := fun _ => T.data.target_path_finish
  targetPath_vertices := fun _ => T.data.target_path_vertices
  targetPath_edges := fun _ => T.data.target_path_edges

@[simp] theorem ranked_edge (T : PairedSingleGlobalTransaction C) :
    T.rankedFairGlobalRelation.edge = T.data.realEdge :=
  rfl

@[simp] theorem ranked_carrier (T : PairedSingleGlobalTransaction C) :
    T.rankedFairGlobalRelation.carrier = T.data.carrier :=
  rfl

end PairedSingleGlobalTransaction

end LinkageBlueprint
end Blueprint
end Erdos599

