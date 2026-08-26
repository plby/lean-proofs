/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateOutputFacts
import ErdosProblems.Erdos547b.Claim616RichGraphTransport

/-!
# Coordinate containment from the literal rich Lemma 6.11 output

This module performs the single graph-equality transport between the padded
reduced graph carried by `RichLemma611Output` and the concrete padded
regularity reduced graph used by `IndexedHostSystem`.  It then supplies the
current coordinate backend with the source-degree and distinguished-root
facts extracted from that output.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateOutputApplication

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
open Erdos547b.ZhaoClaim616RichCoordinateOutputFacts
open Erdos547b.ZhaoClaim616RichCoordinateMbOrientation
open Erdos547b.ZhaoClaim616RichAdapter
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma59Part2Full

universe u v w

variable {V : Type u} {B : Type v} {I : Type w}
variable [Fintype V] [DecidableEq V]
variable [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}
variable (Gdegree Hregular : SimpleGraph B)
variable [DecidableRel Gdegree.Adj] [DecidableRel Hregular.Adj]
variable (Pcluster : ClusterAssignment B I)
variable (cluster : I → Finset B) (epsilon reducedDensity : ℚ)
variable [DecidableRel
  (regularityReducedGraph Hregular cluster epsilon reducedDensity).Adj]
variable (threshold quota miss rhoK : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota
    (regularityReducedGraph Hregular cluster epsilon reducedDensity)
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)
variable (N eta targetA targetB fb cutoff : ℝ)
variable (lowerV1 upperV1 upperV2 mbEdgesBound mbBound : ℕ)
variable (lowerA lowerB exceptionalBound : ℝ)
variable
  (O : RichLemma611Output Pcluster Gdegree threshold quota
    (regularityReducedGraph Hregular cluster epsilon reducedDensity)
    miss Q sourceDensity N eta targetA targetB fb cutoff
    lowerV1 upperV1 upperV2 mbEdgesBound mbBound lowerA lowerB
    exceptionalBound)

/-- Once the literal equality of reduced graphs and its indexed host are
available, every remaining matching/source premise of the coordinate backend
is extracted directly from `RichLemma611Output`. -/
theorem isContained_of_richCoordinateOutputAtIndexedHost
    (hEq :
      padGraph (regularityReducedGraph Hregular cluster epsilon reducedDensity) =
        regularityReducedGraph Hregular (padCluster cluster) epsilon
          reducedDensity)
    (C : Finset (EvenPadding I))
    (H : IndexedHostSystem Hregular (padCluster cluster) epsilon reducedDensity
      (Sum.inl Q.A) (Sum.inl Q.B) C
      (transportSubgraph hEq O.D.Mout)
      (O.D.V2 ∩
        (matchingSupport (transportSubgraph hEq O.D.Mout) \
          matchingSupport (transportSubgraph hEq O.D.Mb)))
      rhoK (padAssignment Pcluster) threshold quota Gdegree)
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (hCV1 : C ⊆ O.D.V1)
    (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (n f0 f1 epsilon1 epsilon2 gamma : ℝ)
    (hn : 0 ≤ n)
    (hMinTarget : (1 - epsilon1) * n ≤ targetA)
    (hdensityOne : ∀ e ∈ reservedMinEdges O.D C, ∀ c,
      sourceDensity (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e c) ≤ 1)
    (hMzeroScalar : 2 * N * C.card ≤ f0 - epsilon2 * n)
    (hforest : f0 + f1 ≤ n)
    (hhierarchy : 3 * gamma ≤ epsilon2 - epsilon1)
    (hresidualPositive : 0 < f1 + 3 * gamma * n)
    (hN : 0 < N) (hsmallFb : fb < cutoff) (htargetB : 0 < targetB)
    (hrhoK : 0 < rhoK)
    (m : ℕ) (removalBudget : ℝ)
    (scale : CanonicalClusterScaleFacts (padCluster cluster)
      (Sum.inl Q.A) (Sum.inl Q.B) (epsilon : ℝ) quota m)
    (margins : CanonicalMarginScalars P.numParts small
      (canonicalClusterCapacity target slack small C.card)
      (canonicalSelectedCapacity
        (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1)) rhoK)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (F1 P S))
        (MatchingDecomposition.MoneEdges O.D C).card small)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (Fb P))
        O.D.mbEdges.card small)
      quota m (epsilon : ℝ) (reducedDensity : ℝ) removalBudget)
    (online : CanonicalOnlineScalars
      (Fintype.card
          (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey
            (Erdos547b.ZhaoLemma614HierarchicalFullTree.wholeOrderedTree
              T hT globalRoot)) +
        (P.numParts + Fintype.card (BranchIndex P) + P.numParts))
      small m quota (epsilon : ℝ) removalBudget) :
    T.IsContained Hregular := by
  have hV1Adj := rich_V1_adj_A Pcluster Gdegree threshold quota
    (regularityReducedGraph Hregular cluster epsilon reducedDensity) miss Q
    sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
    mbEdgesBound mbBound lowerA lowerB exceptionalBound O heta hetaHalf
  have hremainingDegree := rich_remaining_sourceDegree_pos Pcluster Gdegree
    threshold quota
    (regularityReducedGraph Hregular cluster epsilon reducedDensity) miss Q
    sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
    mbEdgesBound mbBound lowerA lowerB exceptionalBound O C n f0 f1 epsilon1
    epsilon2 gamma hn hMinTarget hdensityOne hMzeroScalar hforest hhierarchy
    hresidualPositive hN.le
  have hreservedDegree := rich_reserved_sourceDegree_pos Pcluster Gdegree
    threshold quota
    (regularityReducedGraph Hregular cluster epsilon reducedDensity) miss Q
    sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
    mbEdgesBound mbBound lowerA lowerB exceptionalBound O hsmallFb htargetB
  have hMbAdj := rich_reservedRootSide_adj_B Pcluster Gdegree threshold quota
    (regularityReducedGraph Hregular cluster epsilon reducedDensity) miss Q
    sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
    mbEdgesBound mbBound lowerA lowerB exceptionalBound O hN hsmallFb
  let transported := coordinateSourceTransport
    (inferInstance : DecidableRel
      (padGraph
        (regularityReducedGraph Hregular cluster epsilon reducedDensity)).Adj)
    (inferInstance : DecidableRel
      (regularityReducedGraph Hregular (padCluster cluster) epsilon
        reducedDensity).Adj)
    hEq Q.claim67
    (sourceDegree Q.claim67.M
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      sourceDensity N (Sum.inl Q.A))
    O.D C sourceDensity N (Sum.inl Q.A) (Sum.inl Q.B)
    (reservedRootSide Pcluster Gdegree threshold quota
      (regularityReducedGraph Hregular cluster epsilon reducedDensity) miss Q
      sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
      mbEdgesBound mbBound lowerA lowerB exceptionalBound O)
    hV1Adj hMbAdj hremainingDegree hreservedDegree
  have Htransported : IndexedHostSystem Hregular (padCluster cluster) epsilon
      reducedDensity (Sum.inl Q.A) (Sum.inl Q.B) C transported.target.Mout
      (transported.target.V2 ∩
        (matchingSupport transported.target.Mout \
          matchingSupport transported.target.Mb))
      rhoK (padAssignment Pcluster) threshold quota Gdegree := by
    rw [transported.Mout_eq, transported.Mb_eq, transported.V2_eq]
    exact H
  have hCV1transported : C ⊆ transported.target.V1 := by
    rw [transported.V1_eq]
    exact hCV1
  have marginsTransported : CanonicalMarginScalars P.numParts small
      (canonicalClusterCapacity target slack small C.card)
      (canonicalSelectedCapacity
        (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1)) rhoK)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (F1 P S))
        (MatchingDecomposition.MoneEdges transported.target C).card small)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (Fb P))
        transported.target.mbEdges.card small)
      quota m (epsilon : ℝ) (reducedDensity : ℝ) removalBudget := by
    rw [transported.MoneEdges_card_eq, transported.mbEdges_card_eq]
    exact margins
  exact isContained_of_richCoordinatePositiveSourceDegrees Hregular Gdegree
    (padCluster cluster) epsilon reducedDensity transported.target
    (Sum.inl Q.A) (Sum.inl Q.B) C rhoK (padAssignment Pcluster) threshold
    quota Htransported hT P hsmall S transported.mbSide hCV1transported
    transported.V1_adj transported.mb_adj sourceDensity N
    transported.remaining_pos transported.reserved_pos hrhoK m removalBudget
    scale marginsTransported online

end Erdos547b.ZhaoClaim616RichCoordinateOutputApplication

#print axioms Erdos547b.ZhaoClaim616RichCoordinateOutputApplication.isContained_of_richCoordinateOutputAtIndexedHost
