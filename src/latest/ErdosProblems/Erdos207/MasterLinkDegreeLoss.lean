/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CompatibleCandidateDegree
import ErdosProblems.Erdos207.MasterIterationData

/-!
# Degree loss caused by a master-stage link family

Inside the next vortex set, an old neighbor disappears only when its pair is
covered by the newly adjoined triangle family.  Packinghood then identifies
the covered degree at a vertex with twice its selected triangle-star count.
These deterministic lemmas turn the cardinality-tail estimates for selected
triangles into the T1--T2 degree-loss certificates used by the master
typicality update.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The ambient finite family of all triples containing `v`. -/
def ambientTriplesThrough
    {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    TripleSystemOn V :=
  triplesThrough univ v

@[simp]
lemma ambientTriplesThrough_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : TripleSystemOn V) (v : V) :
    ambientTriplesThrough v ∩ M = triplesThrough M v := by
  ext T
  simp only [ambientTriplesThrough, triplesThrough, mem_inter, mem_filter,
    mem_univ, true_and]
  tauto

/-- When both endpoints remain in `U`, every old neighbor removed by the
stage update is a neighbor in the graph covered by the update family. -/
lemma removedNeighbors_subset_coveredNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U S : Finset V) (M : TripleSystemOn V)
    (v : V) (hv : v ∈ U) (hSU : S ⊆ U) :
    neighborsIn G S v \ neighborsIn (updatedStageGraph G U M) S v ⊆
      (coveredGraph M).neighborFinset v := by
  intro w hw
  obtain ⟨hwOld, hwNotNew⟩ := mem_sdiff.mp hw
  have hwOldData := mem_neighborsIn_iff.mp hwOld
  rw [SimpleGraph.mem_neighborFinset]
  by_contra hwNotCovered
  apply hwNotNew
  apply mem_neighborsIn_iff.mpr
  exact ⟨hwOldData.1,
    ⟨graphRestrictedTo_adj.mpr
        ⟨hwOldData.2, hv, hSU hwOldData.1⟩,
      hwOldData.2.ne, hwNotCovered⟩⟩

/-- The number of removed neighbors is at most the covered degree of the
update family. -/
theorem card_removedNeighbors_le_coveredDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U S : Finset V) (M : TripleSystemOn V)
    (v : V) (hv : v ∈ U) (hSU : S ⊆ U) :
    (neighborsIn G S v \
      neighborsIn (updatedStageGraph G U M) S v).card <=
        (coveredGraph M).degree v := by
  exact card_le_card
    (removedNeighbors_subset_coveredNeighborFinset G U S M v hv hSU)

/-- Splitting the update as a fixed preliminary family `R` and a random link
family `M`, the degree loss is bounded by twice the sum of their star
counts. -/
theorem card_removedNeighbors_le_two_mul_starCounts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U S : Finset V) (R M : TripleSystemOn V)
    (v : V) (hv : v ∈ U) (hSU : S ⊆ U)
    (hpacking : IsPackingOn (R ∪ M)) :
    (neighborsIn G S v \
      neighborsIn (updatedStageGraph G U (R ∪ M)) S v).card <=
        2 * ((triplesThrough R v).card +
          (ambientTriplesThrough v ∩ M).card) := by
  have hthrough : triplesThrough (R ∪ M) v =
      triplesThrough R v ∪ triplesThrough M v := by
    ext T
    simp only [triplesThrough, mem_filter, mem_union]
    tauto
  calc
    (neighborsIn G S v \
        neighborsIn (updatedStageGraph G U (R ∪ M)) S v).card <=
        (coveredGraph (R ∪ M)).degree v :=
      card_removedNeighbors_le_coveredDegree G U S (R ∪ M) v hv hSU
    _ = 2 * (triplesThrough (R ∪ M) v).card :=
      hpacking.coveredGraph_degree_eq_two_mul_triplesThrough v
    _ <= 2 * ((triplesThrough R v).card +
        (triplesThrough M v).card) := by
      rw [hthrough]
      exact Nat.mul_le_mul_left 2 (card_union_le _ _)
    _ = 2 * ((triplesThrough R v).card +
        (ambientTriplesThrough v ∩ M).card) := by
      rw [ambientTriplesThrough_inter]

/-- A strict selected-star cap and a scalar budget discharge one concrete
degree-loss inequality. -/
theorem nnreal_card_removedNeighbors_le_of_starCap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U S : Finset V) (R M : TripleSystemOn V)
    (v : V) (hv : v ∈ U) (hSU : S ⊆ U)
    (hpacking : IsPackingOn (R ∪ M)) (cap : Nat) (budget : NNReal)
    (hcap : (ambientTriplesThrough v ∩ M).card < cap)
    (hbudget : (2 : NNReal) *
      ((triplesThrough R v).card + cap) <= budget) :
    ((neighborsIn G S v \
      neighborsIn (updatedStageGraph G U (R ∪ M)) S v).card : NNReal) <=
        budget := by
  apply le_trans _ hbudget
  norm_cast
  exact (card_removedNeighbors_le_two_mul_starCounts
    G U S R M v hv hSU hpacking).trans <| by
      gcongr

end

end Erdos207
