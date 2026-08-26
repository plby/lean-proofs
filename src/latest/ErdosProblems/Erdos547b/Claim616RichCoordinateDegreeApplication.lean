/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateAverageApplication

/-!
# Positive source-degree specialization of coordinate containment

The rich source records control matching families through real source-degree
sums.  This file converts strict positivity of those genuine sums into the
nonempty finite bin types required by the current total-function allocator.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateDegreeApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoClaim616RichCoordinateCanonicalNumerics
open Erdos547b.ZhaoClaim616RichCoordinateSourceApplication
open Erdos547b.ZhaoClaim616RichCoordinateAverageApplication
open Erdos547b.ZhaoLemma59Part2Full

universe u v w

/-- A strictly positive source degree cannot be supported on an empty edge
family. -/
theorem card_pos_of_sourceDegree_pos
    {I : Type u} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset I) (sourceDensity : I → I → ℝ)
    (N : ℝ) (A : I) (S : Finset (MatchingEdge M))
    (hpositive : 0 < sourceDegree M L sourceDensity N A S) :
    0 < S.card := by
  by_contra hnot
  have hzero : S.card = 0 := Nat.eq_zero_of_not_pos hnot
  have hempty : S = ∅ := Finset.card_eq_zero.mp hzero
  subst S
  simpa [sourceDegree_eq_sum] using hpositive

variable {V : Type u} {B : Type v} {K : Type w}
variable [Fintype V] [DecidableEq V]
variable [Fintype B] [DecidableEq B] [Fintype K] [DecidableEq K]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}
variable (G Gdegree : SimpleGraph B)
variable [DecidableRel G.Adj] [DecidableRel Gdegree.Adj]
variable (cluster : K → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (Aroot Broot : K) (C : Finset K) (rhoK : ℕ)
variable (Pcluster : ClusterAssignment B K) (threshold quota : ℕ)
variable
  (H : IndexedHostSystem G cluster epsilon density Aroot Broot C
    (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D)
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D)))
    rhoK Pcluster threshold quota Gdegree)

include H

/-- Average-capacity containment from the source-shaped positivity facts
carried by Lemmas 6.11 and 6.14. -/
theorem isContained_of_richCoordinatePositiveSourceDegrees
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hCV1 : C ⊆ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D)
    (hV1Adj : ∀ x ∈ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Aroot x)
    (hMbAdj : ∀ e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Broot
          (matchingEdgeEndpoint e.1.1 (mbSide e)))
    (sourceDensity : K → K → ℝ) (N : ℝ)
    (hremainingDegree : 0 < sourceDegree C67.M L sourceDensity N Aroot
      (MatchingDecomposition.MoneEdges
        (R := regularityReducedGraph G cluster epsilon density) D C))
    (hreservedDegree : 0 < sourceDegree C67.M L sourceDensity N Broot
      (MatchingDecomposition.mbEdges
        (R := regularityReducedGraph G cluster epsilon density) D))
    (hrhoK : 0 < rhoK)
    (m : ℕ) (removalBudget : ℝ)
    (scale : CanonicalClusterScaleFacts cluster Aroot Broot
      (epsilon : ℝ) quota m)
    (margins : CanonicalMarginScalars P.numParts small
      (canonicalClusterCapacity target slack small C.card)
      (canonicalSelectedCapacity
        (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1)) rhoK)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (F1 P S))
        (MatchingDecomposition.MoneEdges
          (R := regularityReducedGraph G cluster epsilon density) D C).card
        small)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (Fb P))
        (MatchingDecomposition.mbEdges
          (R := regularityReducedGraph G cluster epsilon density) D).card
        small)
      quota m (epsilon : ℝ) (density : ℝ) removalBudget)
    (online : CanonicalOnlineScalars
      (Fintype.card
          (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey
            (Erdos547b.ZhaoLemma614HierarchicalFullTree.wholeOrderedTree
              T hT globalRoot)) +
        (P.numParts + Fintype.card (BranchIndex P) + P.numParts))
      small m quota (epsilon : ℝ) removalBudget) :
    T.IsContained G := by
  have hremaining : 0 < (MatchingDecomposition.MoneEdges
      (R := regularityReducedGraph G cluster epsilon density) D C).card :=
    card_pos_of_sourceDegree_pos C67.M L sourceDensity N Aroot _
      hremainingDegree
  have hreserved : 0 < (MatchingDecomposition.mbEdges
      (R := regularityReducedGraph G cluster epsilon density) D).card :=
    card_pos_of_sourceDegree_pos C67.M L sourceDensity N Broot _
      hreservedDegree
  exact isContained_of_richCoordinateAverageCapacities G Gdegree cluster
    epsilon density D Aroot Broot C rhoK Pcluster threshold quota H hT P
    hsmall S mbSide hCV1 hV1Adj hMbAdj hrhoK hremaining hreserved m
    removalBudget scale margins online

end Erdos547b.ZhaoClaim616RichCoordinateDegreeApplication

#print axioms Erdos547b.ZhaoClaim616RichCoordinateDegreeApplication.card_pos_of_sourceDegree_pos
#print axioms Erdos547b.ZhaoClaim616RichCoordinateDegreeApplication.isContained_of_richCoordinatePositiveSourceDegrees
