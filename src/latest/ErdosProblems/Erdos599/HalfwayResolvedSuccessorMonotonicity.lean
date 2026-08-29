/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLinkageFirstClosure

/-!
# Exact relations retained by resolved successors

`ResolvedSuccessor` keeps both the raw club-stage union datum and the
oriented replacement built from it.  This file records the exact equations
which make that retained data usable by a transfinite scheduler.  In
particular, the real relation and carrier of a successor result are not
merely bounded by the raw transaction: they are equal to it.

The final two lemmas isolate the elementary successor-to-successor
monotonicity argument.  They only use the `old_real_edges` and
`old_real_vertices` fields of the later transaction, so no compatibility of
the two locally constructed ranks is required.
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
variable {C : ClubStageGeometry Gamma Y kappa theta}

namespace LinkageFirstClubStageSeedSystem.ResolvedSuccessor

variable {S : LinkageFirstClubStageSeedSystem C}
variable {U : ClubStageUnionSystem C}
variable {W : LinkageBlueprint Gamma Y kappa} {u : V}

/-- The full edge relation of the successor blueprint is exactly the raw
inside relation together with the finite assigned edges. -/
theorem result_edgeSet_exact (R : ResolvedSuccessor S U W u) :
    R.result.edgeSet =
      R.data.inside ∪ assignedFiniteEdges R.request.assignment := by
  rw [result, WholeFamilyOrientedReplacement.result_eq,
    orientationBlueprint_edgeSet, R.orientation_edge]

/-- The real edge relation of the successor blueprint is exactly the real
part of the raw transaction relation. -/
theorem result_realPart_edges_exact (R : ResolvedSuccessor S U W u) :
    R.result.realPart.edges = relationRealEdges (Gamma := Gamma)
      (R.data.inside ∪ assignedFiniteEdges R.request.assignment) := by
  rw [realPart_edges, result_edgeSet_exact]
  rfl

/-- The successor blueprint has exactly the carrier stored by the raw
transaction, including isolated root vertices. -/
theorem result_vertexSet_exact (R : ResolvedSuccessor S U W u) :
    R.result.vertexSet = R.data.carrier := by
  rw [result, R.replacement.result_vertexSet, R.orientation_carrier]

/-- The spanning real part has the same exact retained carrier. -/
theorem result_realPart_vertices_exact (R : ResolvedSuccessor S U W u) :
    R.result.realPart.vertices = R.data.carrier := by
  rw [realPart_vertices, result_vertexSet_exact]

/-- Every old real edge survives in the exact real relation of the retained
successor. -/
theorem old_realEdges_subset_result (R : ResolvedSuccessor S U W u) :
    W.realPart.edges ⊆ R.result.realPart.edges := by
  rw [R.result_realPart_edges_exact]
  exact R.data.old_real_edges

/-- Every old real vertex survives in the exact retained carrier. -/
theorem old_realVertices_subset_result (R : ResolvedSuccessor S U W u) :
    W.realPart.vertices ⊆ R.result.realPart.vertices := by
  rw [R.result_realPart_vertices_exact]
  exact R.data.old_real_vertices

/-- Consecutive retained successors have monotone real-edge relations.
The later successor may be built from a different seed or union system. -/
theorem consecutive_realEdges_mono
    {S' : LinkageFirstClubStageSeedSystem C}
    {U' : ClubStageUnionSystem C} {v : V}
    (R₀ : ResolvedSuccessor S U W u)
    (R₁ : ResolvedSuccessor S' U' R₀.result v) :
    relationRealEdges (Gamma := Gamma)
        (R₀.data.inside ∪ assignedFiniteEdges R₀.request.assignment) ⊆
      relationRealEdges (Gamma := Gamma)
        (R₁.data.inside ∪ assignedFiniteEdges R₁.request.assignment) := by
  rw [← R₀.result_realPart_edges_exact,
    ← R₁.result_realPart_edges_exact]
  exact R₁.old_realEdges_subset_result

/-- Consecutive retained successors have monotone carriers. -/
theorem consecutive_carrier_mono
    {S' : LinkageFirstClubStageSeedSystem C}
    {U' : ClubStageUnionSystem C} {v : V}
    (R₀ : ResolvedSuccessor S U W u)
    (R₁ : ResolvedSuccessor S' U' R₀.result v) :
    R₀.data.carrier ⊆ R₁.data.carrier := by
  rw [← R₀.result_realPart_vertices_exact,
    ← R₁.result_realPart_vertices_exact]
  exact R₁.old_realVertices_subset_result

end LinkageFirstClubStageSeedSystem.ResolvedSuccessor

end LinkageBlueprint
end Blueprint
end Erdos599
