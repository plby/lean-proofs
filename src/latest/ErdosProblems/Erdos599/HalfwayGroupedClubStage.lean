/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLiteralContactGeometry
import ErdosProblems.Erdos599.HalfwayContactSuccessorRun

/-!
# Retaining a grouped contact relation as actual club-stage data

The grouped contact compiler produces the literal transaction relation on
the original vertex type.  `ClubStageUnionData` has a separate assignment
slot, but no assignment representation is needed once all contact intervals
have already been compiled into that relation.  This file installs the
relation as `inside` and uses the canonical empty fractured assignment.

Consequently all representation-level fields (imaginary-graph containment,
endpoints, bi-uniqueness, rank, cross-incidence, and the empty infinite-source
condition) are theorems.  The arguments which remain are precisely the
ambient Section 9 boundary, accounting, and target-route facts; they are
kept as explicit hypotheses rather than hidden in a replacement package.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y closureFamily : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}
variable {kappa theta : Cardinal.{u}}

/-- The empty fractured warp, used only as the vacuous assignment index of
an already compiled literal relation. -/
def emptyFracturedWarp (Gamma : DWeb V) : FracturedWarp Gamma where
  paths := ∅
  edgeWarp := ∅
  edgeWarp_isWarp := by
    intro p hp
    exact hp.elim
  same_edges := by
    ext e
    simp only [familyEdges, Set.mem_iUnion, Set.mem_empty_iff_false]
  allowed_intersection := by
    intro p hp
    exact hp.elim

/-- The unique vacuous assignment on the empty fractured family. -/
def emptyFracturedAssignment (Gamma : DWeb V) (Y : Set Gamma.DPath) :
    SimultaneousAssignment (emptyFracturedWarp Gamma).paths Y :=
  SimultaneousAssignment.of_initialSet_subset (by
    intro x hx
    rcases hx with ⟨p, hp, _hpx⟩
    exact hp.elim)

@[simp] theorem assignedFiniteEdges_emptyFracturedAssignment
    (Gamma : DWeb V) (Y : Set Gamma.DPath) :
    assignedFiniteEdges (emptyFracturedAssignment Gamma Y) = ∅ := by
  ext e
  constructor
  · rintro ⟨s, _hterm, _hsource⟩
    rcases s.property.1 with ⟨p, hp, _hpinitial⟩
    exact hp.elim
  · simp

@[simp] theorem assignedInfiniteSources_emptyFracturedAssignment
    (Gamma : DWeb V) (Y : Set Gamma.DPath) :
    assignedInfiniteSources (emptyFracturedAssignment Gamma Y) = ∅ := by
  ext x
  constructor
  · rintro ⟨s, _hsx, _hinfinite⟩
    rcases s.property.1 with ⟨p, hp, _hpinitial⟩
    exact hp.elim
  · simp

namespace LiteralContactTransactionGeometry

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {W : LinkageBlueprint Gamma Y kappa} {u : V}

/-- Install any checked literal contact relation as the real content of one
club stage.  The empty assignment slot is intentional: every real fragment
and every classified shortcut has already been retained in `L.edge`.

Thus relation containment, endpoint incidence, bi-uniqueness, and rank are
all consequences of `L`; only the ambient Section 9 boundary and accounting
facts remain as construction inputs. -/
noncomputable def toClubStageUnionData
    (L : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa))
    (sink_boundary :
      {x | x ∈ L.carrier ∧ ¬ ∃ y, (x, y) ∈ L.edge} ⊆ C.newSlice)
    (carrier_roofed : L.carrier ⊆ C.outerRoof)
    (covers_source : Gamma.source ⊆
      {x | x ∈ L.carrier ∧ ¬ ∃ y, (y, x) ∈ L.edge} ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y L.carrier))
    (carrier_closed : L.carrier ⊆ C.closedSet)
    (card_carrier : #L.carrier ≤ kappa)
    (every_relation_ray_strong :
      ∀ r : Ray (imaginaryGraph Gamma Y kappa),
        r.edgeSet ⊆ L.edge → (strongEdgeIndices r).Infinite)
    (stable_boundary :
      {x | x ∈ L.carrier ∧ ¬ ∃ y, (x, y) ∈ L.edge} ∩ C.newSlice ⊆
        C.persistent)
    (old_real_vertices : W.realPart.vertices ⊆ L.carrier)
    (old_real_edges : W.realPart.edges ⊆
      relationRealEdges (Gamma := Gamma) L.edge)
    (old_vertices_accounted : W.vertexSet ⊆
      ({x | x ∈ L.carrier ∧ ¬ ∃ y, (x, y) ∈ L.edge} ∩ W.terminalSet) ∪
        {x | ∃ y, (x, y) ∈ W.familyGraph.edges ∩ L.edge} ∪
          relationCompletedRealVertices (Gamma := Gamma)
            L.edge L.carrier Gamma.target)
    (target_path : FinitePath Gamma.graph)
    (target_path_start : target_path.start = u)
    (target_path_finish : target_path.finish ∈ Gamma.target)
    (target_path_vertices : target_path.support ⊆ L.carrier)
    (target_path_edges : target_path.edgeSet ⊆
      relationRealEdges (Gamma := Gamma) L.edge)
    (preserves_other_real_terminals : W.realPart.terminals \ {u} ⊆
      relationRealTerminals (Gamma := Gamma) L.edge L.carrier) :
    ClubStageUnionData C W (emptyFracturedAssignment Gamma Y) u := by
  let E := emptyFracturedAssignment Gamma Y
  have hE : assignedFiniteEdges E = ∅ :=
    assignedFiniteEdges_emptyFracturedAssignment Gamma Y
  refine {
    inside := L.edge
    carrier := L.carrier
    inside_in_graph := L.edge_subset_imaginaryGraph
    inside_endpoints := L.endpoints_mem_carrier
    assigned_endpoints := ?_
    inside_biunique := L.biunique
    cross_in := ?_
    cross_out := ?_
    rank := L.rank
    inside_rank := fun hxy ↦ L.rank_lt_of_mem_edge hxy
    assigned_rank := ?_
    infinite_sources_sink := ?_
    sink_boundary := ?_
    carrier_roofed := carrier_roofed
    covers_source := ?_
    carrier_closed := carrier_closed
    card_carrier := card_carrier
    every_relation_ray_strong := ?_
    stable_boundary := ?_
    old_real_vertices := old_real_vertices
    old_real_edges := ?_
    old_vertices_accounted := ?_
    target_path := target_path
    target_path_start := target_path_start
    target_path_finish := target_path_finish
    target_path_vertices := target_path_vertices
    target_path_edges := ?_
    preserves_other_real_terminals := ?_ }
  · intro e he
    rw [hE] at he
    exact he.elim
  · intro x y z _hinside hassigned
    rw [hE] at hassigned
    exact hassigned.elim
  · intro x y z _hinside hassigned
    rw [hE] at hassigned
    exact hassigned.elim
  · intro x y hassigned
    rw [hE] at hassigned
    exact hassigned.elim
  · intro x hx
    rw [assignedInfiniteSources_emptyFracturedAssignment] at hx
    exact hx.elim
  · rw [assignedFiniteEdges_emptyFracturedAssignment,
      assignedInfiniteSources_emptyFracturedAssignment,
      Set.union_empty, Set.empty_union]
    exact sink_boundary
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact covers_source
  · intro r hr
    apply every_relation_ray_strong r
    rw [assignedFiniteEdges_emptyFracturedAssignment,
      Set.union_empty] at hr
    exact hr
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact stable_boundary
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact old_real_edges
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact old_vertices_accounted
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact target_path_edges
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact preserves_other_real_terminals

/-- Add concrete target-resolution routes to a literal contact stage.  The
result is the actual constant transaction consumed by the successor-run
compiler, with no extra rank or scheduler assumptions. -/
noncomputable def toSingleGlobalClubStageTransaction
    (L : LiteralContactTransactionGeometry
      (Gamma := Gamma) (Y := Y) (kappa := kappa))
    (D : ClubStageUnionData C W (emptyFracturedAssignment Gamma Y) u)
    (resolve : ∀ x,
      x ∈ D.carrier →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) D.inside) →
      x ∉ Gamma.target →
      Nonempty (EmbeddedTransactionTargetRoute D x)) :
    SingleGlobalClubStageTransaction C where
  blueprint := W
  fractured := emptyFracturedWarp Gamma
  assignment := emptyFracturedAssignment Gamma Y
  anchor := u
  data := D
  resolve := by
    intro x hx hno htarget
    apply resolve x hx
    · simpa only [assignedFiniteEdges_emptyFracturedAssignment,
        Set.union_empty] using hno
    · exact htarget

end LiteralContactTransactionGeometry

namespace GroupedContactSegmentedAssignment

variable {Z : Set Gamma.DPath} {A : SimultaneousAssignment Z Y}
variable {G : Type v}
variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {W : LinkageBlueprint Gamma Y kappa} {u : V}

/-- Install a compiled grouped-contact relation as the literal relation of
one club stage.  No rank, acyclicity, or assignment incidence is assumed:
all of those fields are supplied by the grouped compiler and the empty
assignment. -/
noncomputable def toClubStageUnionData
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (carrier : Set V)
    (endpoints : ∀ e ∈ S.edge, e.1 ∈ carrier ∧ e.2 ∈ carrier)
    (sink_boundary :
      {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ S.edge} ⊆ C.newSlice)
    (carrier_roofed : carrier ⊆ C.outerRoof)
    (covers_source : Gamma.source ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ S.edge} ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y carrier))
    (carrier_closed : carrier ⊆ C.closedSet)
    (card_carrier : #carrier ≤ kappa)
    (every_relation_ray_strong :
      ∀ r : Ray (imaginaryGraph Gamma Y kappa),
        r.edgeSet ⊆ S.edge → (strongEdgeIndices r).Infinite)
    (stable_boundary :
      {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ S.edge} ∩ C.newSlice ⊆
        C.persistent)
    (old_real_vertices : W.realPart.vertices ⊆ carrier)
    (old_real_edges : W.realPart.edges ⊆
      relationRealEdges (Gamma := Gamma) S.edge)
    (old_vertices_accounted : W.vertexSet ⊆
      ({x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ S.edge} ∩ W.terminalSet) ∪
        {x | ∃ y, (x, y) ∈ W.familyGraph.edges ∩ S.edge} ∪
          relationCompletedRealVertices (Gamma := Gamma)
            S.edge carrier Gamma.target)
    (target_path : FinitePath Gamma.graph)
    (target_path_start : target_path.start = u)
    (target_path_finish : target_path.finish ∈ Gamma.target)
    (target_path_vertices : target_path.support ⊆ carrier)
    (target_path_edges : target_path.edgeSet ⊆
      relationRealEdges (Gamma := Gamma) S.edge)
    (preserves_other_real_terminals : W.realPart.terminals \ {u} ⊆
      relationRealTerminals (Gamma := Gamma) S.edge carrier) :
    ClubStageUnionData C W (emptyFracturedAssignment Gamma Y) u := by
  let E := emptyFracturedAssignment Gamma Y
  have hE : assignedFiniteEdges E = ∅ :=
    assignedFiniteEdges_emptyFracturedAssignment Gamma Y
  refine {
    inside := S.edge
    carrier := carrier
    inside_in_graph := S.edge_subset_imaginaryGraph hclosed
    inside_endpoints := endpoints
    assigned_endpoints := ?_
    inside_biunique := S.edge_biunique
    cross_in := ?_
    cross_out := ?_
    rank := S.rank
    inside_rank := fun hxy ↦ S.rank_lt_of_mem_edge hxy
    assigned_rank := ?_
    infinite_sources_sink := ?_
    sink_boundary := ?_
    carrier_roofed := carrier_roofed
    covers_source := ?_
    carrier_closed := carrier_closed
    card_carrier := card_carrier
    every_relation_ray_strong := ?_
    stable_boundary := ?_
    old_real_vertices := old_real_vertices
    old_real_edges := ?_
    old_vertices_accounted := ?_
    target_path := target_path
    target_path_start := target_path_start
    target_path_finish := target_path_finish
    target_path_vertices := target_path_vertices
    target_path_edges := ?_
    preserves_other_real_terminals := ?_ }
  · intro e he
    rw [hE] at he
    exact he.elim
  · intro x y z _hinside hassigned
    rw [hE] at hassigned
    exact hassigned.elim
  · intro x y z _hinside hassigned
    rw [hE] at hassigned
    exact hassigned.elim
  · intro x y hassigned
    rw [hE] at hassigned
    exact hassigned.elim
  · intro x hx
    rw [assignedInfiniteSources_emptyFracturedAssignment] at hx
    exact hx.elim
  · rw [assignedFiniteEdges_emptyFracturedAssignment,
      assignedInfiniteSources_emptyFracturedAssignment,
      Set.union_empty, Set.empty_union]
    exact sink_boundary
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact covers_source
  · intro r hr
    apply every_relation_ray_strong r
    rw [assignedFiniteEdges_emptyFracturedAssignment,
      Set.union_empty] at hr
    exact hr
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact stable_boundary
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact old_real_edges
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact old_vertices_accounted
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact target_path_edges
  · rw [assignedFiniteEdges_emptyFracturedAssignment, Set.union_empty]
    exact preserves_other_real_terminals

/-- Add concrete target-resolution routes to the retained grouped stage.
The output is the actual transaction repeated by `successorRun`; no
scheduler fairness or monotonicity is an input. -/
noncomputable def toSingleGlobalClubStageTransaction
    (S : GroupedContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily G)
    (D : ClubStageUnionData C W (emptyFracturedAssignment Gamma Y) u)
    (resolve : ∀ x,
      x ∈ D.carrier →
      (¬ ∃ y, (x, y) ∈ relationRealEdges (Gamma := Gamma) D.inside) →
      x ∉ Gamma.target →
      Nonempty (EmbeddedTransactionTargetRoute D x)) :
    SingleGlobalClubStageTransaction C where
  blueprint := W
  fractured := emptyFracturedWarp Gamma
  assignment := emptyFracturedAssignment Gamma Y
  anchor := u
  data := D
  resolve := by
    intro x hx hno htarget
    apply resolve x hx
    · simpa only [assignedFiniteEdges_emptyFracturedAssignment,
        Set.union_empty] using hno
    · exact htarget

end GroupedContactSegmentedAssignment

end LinkageBlueprint
end Blueprint
end Erdos599
