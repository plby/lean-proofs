/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616HierarchicalCoordinateHostLayout
import ErdosProblems.Erdos547b.Claim616CoordinateEdgeMaps

/-!
# Current regular pairs for the coordinate Claim 6.16 host

This module records only literal whole-cluster regular pairs.  It depends on
the current `Claim616` certificate and the current original-edge map, and has
no dependency on the obsolete coarse host-pool implementation.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateHostPairs

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616CoordinateEdgeMaps
open Erdos547b.ZhaoClaim616HierarchicalSourceLayout

universe u v

variable {B : Type u} {I : Type v}
variable [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable (G : SimpleGraph B) [DecidableRel G.Adj]
variable (cluster : I → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L O : Finset I} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (A Broot : I) (C W : Finset I) (rhoK : ℕ)
variable (Pcluster : ClusterAssignment B I) (threshold quota : ℕ)
variable (Gdegree : SimpleGraph B) [DecidableRel Gdegree.Adj]
variable
  (H : IndexedHostSystem G cluster epsilon density A Broot C D.Mout W rhoK
    Pcluster threshold quota Gdegree)

/-- Any actual reduced edge supplies its defining whole regular pair. -/
theorem pair_of_reducedAdj {x y : I}
    (hxy : (regularityReducedGraph G cluster epsilon density).Adj x y) :
    G.IsUniform epsilon (cluster x) (cluster y) ∧
      density ≤ G.edgeDensity (cluster x) (cluster y) :=
  ⟨hxy.2.1, hxy.2.2⟩

include H

/-- The stored distinguished A--B edge as a whole regular pair. -/
theorem distinguishedPair :
    G.IsUniform epsilon (cluster A) (cluster Broot) ∧
      density ≤ G.edgeDensity (cluster A) (cluster Broot) :=
  pair_of_reducedAdj G cluster epsilon density H.distinguished_adj

/-- The stored distinguished-A to selected-C whole regular pair. -/
theorem root_selectedPair (i : Fin C.card) :
    G.IsUniform epsilon (cluster A) (indexedCluster cluster C i) ∧
      density ≤ G.edgeDensity (cluster A) (indexedCluster cluster C i) :=
  H.root_pair i

/-- The selected-C to accessible `M_out` endpoint pair in the exact local
orientation used by the coordinate source layout. -/
theorem selected_accessPair
    (i : Fin C.card) (e : Fin D.Mout.edgeSet.toFinite.toFinset.card)
    (he : e ∈ indexedAllowedEdges
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i) :
    let access := indexedAccessSide
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i e
    G.IsUniform epsilon (indexedCluster cluster C i)
        (cluster (matchingEdgeEndpoint (moutOriginalEdge D e).1
          (orientedSide access 1))) ∧
      density ≤ G.edgeDensity (indexedCluster cluster C i)
        (cluster (matchingEdgeEndpoint (moutOriginalEdge D e).1
          (orientedSide access 1))) := by
  dsimp only
  have h := H.access_pair i e he
  by_cases hs : indexedAccessSide
      (regularityReducedGraph G cluster epsilon density)
      D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i e = 0
  · simpa [orientedSide, hs, moutOriginalEdge_val, indexedMatchingSide]
      using h
  · have hsOne : indexedAccessSide
        (regularityReducedGraph G cluster epsilon density)
        D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i e = 1 := by
      apply Fin.ext
      have hlt := (indexedAccessSide
        (regularityReducedGraph G cluster epsilon density)
        D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i e).isLt
      have hnzero : (indexedAccessSide
          (regularityReducedGraph G cluster epsilon density)
          D.Mout.edgeSet.toFinite.toFinset matchingEdgeEndpoint C W i e).val
          ≠ 0 := by
        intro hz
        apply hs
        apply Fin.ext
        simpa using hz
      omega
    simpa [orientedSide, hs, hsOne, moutOriginalEdge_val,
      indexedMatchingSide] using h

omit H

/-- Every literal original matching edge is a genuine whole regular pair. -/
theorem originalMatchingPair (e : MatchingEdge C67.M) :
    G.IsUniform epsilon
        (cluster (matchingEdgeEndpoint e.1 0))
        (cluster (matchingEdgeEndpoint e.1 1)) ∧
      density ≤ G.edgeDensity
        (cluster (matchingEdgeEndpoint e.1 0))
        (cluster (matchingEdgeEndpoint e.1 1)) := by
  have he : (regularityReducedGraph G cluster epsilon density).Adj
      (matchingEdgeEndpoint e.1 0) (matchingEdgeEndpoint e.1 1) := by
    have hadj : C67.M.Adj e.1.out.1 e.1.out.2 := by
      rw [← Subgraph.mem_edgeSet]
      simpa only [e.1.out_eq] using e.2
    simpa [matchingEdgeEndpoint] using
      C67.M.adj_sub hadj
  exact ⟨he.2.1, he.2.2⟩

/-- The same genuine matching pair in either endpoint orientation. -/
theorem originalMatchingPair_of_ne (e : MatchingEdge C67.M)
    (sourceSide targetSide : Fin 2) (hne : sourceSide ≠ targetSide) :
    G.IsUniform epsilon
        (cluster (matchingEdgeEndpoint e.1 sourceSide))
        (cluster (matchingEdgeEndpoint e.1 targetSide)) ∧
      density ≤ G.edgeDensity
        (cluster (matchingEdgeEndpoint e.1 sourceSide))
        (cluster (matchingEdgeEndpoint e.1 targetSide)) := by
  have hpair := originalMatchingPair (C67 := C67)
    G cluster epsilon density e
  fin_cases sourceSide <;> fin_cases targetSide
  · exact False.elim (hne rfl)
  · simpa using hpair
  · exact ⟨hpair.1.symm, by simpa [G.edgeDensity_comm] using hpair.2⟩
  · exact False.elim (hne rfl)

end Erdos547b.ZhaoClaim616CoordinateHostPairs

#print axioms Erdos547b.ZhaoClaim616CoordinateHostPairs.distinguishedPair
#print axioms Erdos547b.ZhaoClaim616CoordinateHostPairs.selected_accessPair
#print axioms Erdos547b.ZhaoClaim616CoordinateHostPairs.originalMatchingPair_of_ne
