/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMacroStageAccounting
import ErdosProblems.Erdos599.WholeFamilyOrientedReplacementExact

/-!
# A retained marker-absorbed successor transaction

`MarkerAbsorbedMacroRequest` and `MacroStageContinuationData` construct the
raw relation of one Section 9 transaction.  The global scheduler must retain
more than its stable-extension conclusion: it needs the assignment, raw
relation, exact carrier, oriented replacement, and successor blueprint in one
dependent object.  This file packages precisely that data and proves the two
exact equations used by the monotone successor recursion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- One actual marker-absorbed successor, retaining both the source-level
request and the exact oriented result. -/
structure MarkerAbsorbedResolvedSuccessor
    (C : ClubStageGeometry Gamma Y kappa theta)
    (old : LinkageBlueprint Gamma Y kappa) (u : V) where
  seed : MarkerAbsorbedMacroSeed
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
  request : MarkerAbsorbedMacroRequest seed
  continuation : request.MacroStageContinuationData C old u
  replacement : WholeFamilyOrientedReplacement
    (Zf := FracturedWarp.ofWarp
      (outsideReference seed.later request.closureSet)
      (outsideReference_isWarp seed.later_isWarp))
    old request.assignment.assignment u C.newSlice C.closedSet C.persistent
      Gamma.target
  orientation_edge : replacement.orientation.edge = request.macroEdge
  orientation_carrier : replacement.orientation.carrier =
    request.inside.insideFamily.vertexSet

namespace MarkerAbsorbedResolvedSuccessor

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {old : LinkageBlueprint Gamma Y kappa} {u : V}

/-- The exact raw datum retained by the successor. -/
def data (Q : MarkerAbsorbedResolvedSuccessor C old u) :
    ClubStageUnionData
      (Zf := FracturedWarp.ofWarp
        (outsideReference Q.seed.later Q.request.closureSet)
        (outsideReference_isWarp Q.seed.later_isWarp))
      C old Q.request.assignment.assignment u :=
  Q.continuation.toClubStageUnionData

/-- The actual successor blueprint is the root-orbit decomposition of the
constructed oriented relation. -/
def result (Q : MarkerAbsorbedResolvedSuccessor C old u) :
    LinkageBlueprint Gamma Y kappa :=
  orientationBlueprint Q.replacement.orientation

/-- The result has exactly the macro request's inside and finite assigned
edges; no relation is forgotten by the orientation step. -/
theorem result_edgeSet_exact
    (Q : MarkerAbsorbedResolvedSuccessor C old u) :
    Q.result.edgeSet = Q.request.macroEdge := by
  rw [result, orientationBlueprint_edgeSet, Q.orientation_edge]

/-- The real part of the successor is exactly the original-web filter of
the constructed macro relation. -/
theorem result_realPart_edges_exact
    (Q : MarkerAbsorbedResolvedSuccessor C old u) :
    Q.result.realPart.edges =
      relationRealEdges (Gamma := Gamma) Q.request.macroEdge := by
  rw [realPart_edges, Q.result_edgeSet_exact]
  rfl

/-- The oriented successor retains the exact canonical inside carrier,
including isolated roots and sinks. -/
theorem result_vertexSet_exact
    (Q : MarkerAbsorbedResolvedSuccessor C old u) :
    Q.result.vertexSet = Q.request.inside.insideFamily.vertexSet := by
  rw [result, orientationBlueprint_vertexSet, Q.orientation_carrier]

/-- The spanning real part has the same exact retained carrier. -/
theorem result_realPart_vertices_exact
    (Q : MarkerAbsorbedResolvedSuccessor C old u) :
    Q.result.realPart.vertices =
      Q.request.inside.insideFamily.vertexSet := by
  rw [realPart_vertices, Q.result_vertexSet_exact]

/-- Every old real edge survives in the successor's exact real relation. -/
theorem old_realEdges_subset_result
    (Q : MarkerAbsorbedResolvedSuccessor C old u) :
    old.realPart.edges ⊆ Q.result.realPart.edges := by
  rw [Q.result_realPart_edges_exact]
  exact Q.continuation.old_real_edges

/-- Every old real vertex survives in the successor's exact carrier. -/
theorem old_realVertices_subset_result
    (Q : MarkerAbsorbedResolvedSuccessor C old u) :
    old.realPart.vertices ⊆ Q.result.realPart.vertices := by
  rw [Q.result_realPart_vertices_exact]
  exact Q.continuation.old_real_vertices

/-- Claim 2 for the retained request supplies the exact stable successor
conclusion, including terminal persistence and the scheduled target route. -/
theorem stableExtensionConclusion
    (Q : MarkerAbsorbedResolvedSuccessor C old u) :
    StableExtensionConclusion old Q.result u C.newSlice C.closedSet
      C.persistent Gamma.target := by
  exact Q.replacement.stableExtensionConclusion
    (Q.request.classified (persistent := C.persistent)).2

/-- Orient one constructed marker-absorbed macro stage while retaining the
exact edge and carrier equations needed by the cofinal scheduler. -/
theorem exists_of_continuation
    (S : MarkerAbsorbedMacroSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa))
    (R : MarkerAbsorbedMacroRequest S)
    (D : R.MacroStageContinuationData C old u) :
    Nonempty (MarkerAbsorbedResolvedSuccessor C old u) := by
  let U : ClubStageUnionData
      (Zf := FracturedWarp.ofWarp
        (outsideReference S.later R.closureSet)
        (outsideReference_isWarp S.later_isWarp))
      C old R.assignment.assignment u :=
    D.toClubStageUnionData
  let G := U.toWholeFamilyUnionGeometry
  let hclassified := R.classified (persistent := C.persistent)
  let Q := (G.spliceRelation hclassified.1).exists_orientedReplacement_exact
  exact ⟨{
    seed := S
    request := R
    continuation := D
    replacement := Q.choose
    orientation_edge := Q.choose_spec.1
    orientation_carrier := Q.choose_spec.2 }⟩

/-- Consecutive marker-absorbed successors have monotone real relations.
The local ranks and closure sets may be unrelated. -/
theorem consecutive_realEdges_mono
    {v : V}
    (Q₀ : MarkerAbsorbedResolvedSuccessor C old u)
    (Q₁ : MarkerAbsorbedResolvedSuccessor C Q₀.result v) :
    relationRealEdges (Gamma := Gamma) Q₀.request.macroEdge ⊆
      relationRealEdges (Gamma := Gamma) Q₁.request.macroEdge := by
  rw [← Q₀.result_realPart_edges_exact,
    ← Q₁.result_realPart_edges_exact]
  exact Q₁.old_realEdges_subset_result

/-- Consecutive marker-absorbed successors have monotone exact carriers. -/
theorem consecutive_carrier_mono
    {v : V}
    (Q₀ : MarkerAbsorbedResolvedSuccessor C old u)
    (Q₁ : MarkerAbsorbedResolvedSuccessor C Q₀.result v) :
    Q₀.request.inside.insideFamily.vertexSet ⊆
      Q₁.request.inside.insideFamily.vertexSet := by
  rw [← Q₀.result_realPart_vertices_exact,
    ← Q₁.result_realPart_vertices_exact]
  exact Q₁.old_realVertices_subset_result

end MarkerAbsorbedResolvedSuccessor

end LinkageBlueprint
end Blueprint
end Erdos599
