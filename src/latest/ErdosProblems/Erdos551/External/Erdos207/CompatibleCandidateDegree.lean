/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.CompatibleCandidates

/-!
# Compatible candidates from vertex-degree control

For an uncovered pair, every ambient third vertex is either still compatible
or is blocked by a covered edge.  Packinghood identifies each covered vertex
degree with twice the number of chosen triples through that vertex.  These
deterministic facts reduce the common-leave candidate estimate to a vertex
star-count estimate.
-/

namespace Erdos207

open Finset

/-- Ambient candidates split into compatible candidates and candidates
blocked by a covered edge. -/
lemma candidateThirdVertices_subset_compatible_union_edgeBlocked
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V} (huv : u ≠ v) :
    candidateThirdVertices A huv ⊆
      packingCompatibleThirdVertices A P huv ∪
        edgeBlockedThirdVertices A P huv := by
  intro w hw
  by_cases hav : TriangleAvoidsGraph (coveredGraph P)
      (thirdVertexTriple huv w)
  · exact mem_union.mpr (Or.inl
      (mem_packingCompatibleThirdVertices_iff.mpr
        ⟨mem_candidateThirdVertices_iff.mp hw, hav⟩))
  · exact mem_union.mpr (Or.inr
      (mem_edgeBlockedThirdVertices_iff.mpr
        ⟨mem_candidateThirdVertices_iff.mp hw, hav⟩))

/-- Candidate cardinality is at most the compatible supply plus the covered
edge obstruction. -/
theorem card_candidate_le_compatible_add_edgeBlocked
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V} (huv : u ≠ v) :
    (candidateThirdVertices A huv).card ≤
      (packingCompatibleThirdVertices A P huv).card +
        (edgeBlockedThirdVertices A P huv).card := by
  exact (card_le_card
    (candidateThirdVertices_subset_compatible_union_edgeBlocked huv)).trans
      (card_union_le _ _)

/-- For an uncovered pair, the compatible loss is controlled by the two
covered degrees. -/
theorem card_candidate_le_compatible_add_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V}
    (huv : (leaveGraph P).Adj u v) :
    (candidateThirdVertices A huv.ne).card ≤
      (packingCompatibleThirdVertices A P huv.ne).card +
        ((coveredGraph P).degree u + (coveredGraph P).degree v) := by
  exact (card_candidate_le_compatible_add_edgeBlocked
    (A := A) (P := P) huv.ne).trans
      (Nat.add_le_add_left
        (card_edgeBlockedThirdVertices_le_degree_add (A := A) huv) _)

/-- In a packing, every chosen triple through `v` contributes exactly its
two other vertices to the covered degree of `v`. -/
theorem IsPackingOn.coveredGraph_degree_eq_two_mul_triplesThrough
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : TripleSystemOn V} (hP : IsPackingOn P) (v : V) :
    (coveredGraph P).degree v = 2 * (triplesThrough P v).card := by
  let hdec := hP.isTriangleDecomposition
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    hdec.neighborFinset_eq_biUnion_erase v,
    card_biUnion (hdec.pairwiseDisjoint_erase v)]
  calc
    ∑ T ∈ triplesThrough P v, (T.1.erase v).card =
        ∑ _T ∈ triplesThrough P v, 2 := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [card_erase_of_mem (mem_filter.mp hT).2, T.2]
    _ = 2 * (triplesThrough P v).card := by
      simp [Nat.mul_comm]

/-- Star-count control gives the compatible-candidate lower bound in the
form most convenient for the probabilistic stage. -/
theorem card_candidate_le_compatible_add_starCounts
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} (hP : IsPackingOn P) {u v : V}
    (huv : (leaveGraph P).Adj u v) :
    (candidateThirdVertices A huv.ne).card ≤
      (packingCompatibleThirdVertices A P huv.ne).card +
        (2 * (triplesThrough P u).card +
          2 * (triplesThrough P v).card) := by
  simpa [hP.coveredGraph_degree_eq_two_mul_triplesThrough] using
    card_candidate_le_compatible_add_degrees (A := A) huv

end Erdos207
