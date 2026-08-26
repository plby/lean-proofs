/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateDegreeApplication
import ErdosProblems.Erdos547b.Lemma611CapacitySplit

/-!
# Lemma 6.14 capacity-split specialization of coordinate containment

The `M₁` source degree is obtained from the literal `M_in \ M₀`
subtraction, and the `M_b` source degree from the stored small-`f_b`
capacity lower bound.  Thus neither matching-family nonemptiness nor its
strict degree is an independent premise.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateCapacitySplitApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoLemma611CapacitySplit
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
open Erdos547b.ZhaoClaim616RichCoordinateDegreeApplication
open Erdos547b.ZhaoLemma59Part2Full

universe u v w

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

/-- Coordinate containment from the exact Lemma-6.14(2) subtraction data
and the small-`f_b` reserved-capacity certificate. -/
theorem isContained_of_richCoordinateCapacitySplit
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
    (n f0 f1 epsilon1 epsilon2 gamma : ℝ)
    (hn : 0 ≤ n)
    (hMin : (1 - epsilon1) * n ≤
      sourceDegree C67.M L sourceDensity N Aroot D.minEdges)
    (hMzero : sourceDegree C67.M L sourceDensity N Aroot
      (MatchingDecomposition.MzeroEdges
        (R := regularityReducedGraph G cluster epsilon density) D C) ≤
        f0 - epsilon2 * n)
    (hforest : f0 + f1 ≤ n)
    (hhierarchy : 3 * gamma ≤ epsilon2 - epsilon1)
    (hresidualPositive : 0 < f1 + 3 * gamma * n)
    (targetB fb cutoff : ℝ) (mbEdgesBound : ℕ)
    (reserved : OptionalReservedCapacity D
      (sourceDegree C67.M L sourceDensity N Broot)
      targetB N fb cutoff mbEdgesBound)
    (hsmallFb : fb < cutoff) (htargetB : 0 < targetB)
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
  have hremainingLower := remaining_A_capacity D C sourceDensity N Aroot n f0
    f1 epsilon1 epsilon2 gamma hn hMin hMzero hforest hhierarchy
  have hremainingDegree : 0 < sourceDegree C67.M L sourceDensity N Aroot
      (MatchingDecomposition.MoneEdges
        (R := regularityReducedGraph G cluster epsilon density) D C) :=
    hresidualPositive.trans_le hremainingLower
  have hreservedLower := reserved_B_capacity D
    (sourceDegree C67.M L sourceDensity N Broot) targetB N fb cutoff
      mbEdgesBound reserved hsmallFb
  have hreservedDegree : 0 < sourceDegree C67.M L sourceDensity N Broot
      (MatchingDecomposition.mbEdges
        (R := regularityReducedGraph G cluster epsilon density) D) :=
    htargetB.trans_le hreservedLower
  exact isContained_of_richCoordinatePositiveSourceDegrees G Gdegree cluster
    epsilon density D Aroot Broot C rhoK Pcluster threshold quota H hT P
    hsmall S mbSide hCV1 hV1Adj hMbAdj sourceDensity N hremainingDegree
    hreservedDegree hrhoK m removalBudget scale margins online

end Erdos547b.ZhaoClaim616RichCoordinateCapacitySplitApplication

#print axioms Erdos547b.ZhaoClaim616RichCoordinateCapacitySplitApplication.isContained_of_richCoordinateCapacitySplit
