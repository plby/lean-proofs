/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateOutputApplication
import ErdosProblems.Erdos547b.Claim616RichAdapter

/-!
# Final rich-output composition for coordinate Claim 6.16

The rich host constructor selects the actual `C` and builds its indexed host.
The equality-transport application then consumes that same `C` and host.
No host certificate, source allocation, graph copy, or embedding result is a
premise of the theorem below.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateFinalApplication

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
open Erdos547b.ZhaoClaim616RichCoordinateOutputApplication
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

/-- Literal composition of rich host selection and rich coordinate
containment.  Premises remaining at this boundary are scalar/regularity
inequalities, plus the margin family for the `C` selected by the host
constructor. -/
theorem isContained_of_richCoordinateOutput
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (hregularSub : Hregular ≤ Gdegree)
    (hquota : 0 < quota) (hreducedDensity : 0 < reducedDensity)
    (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hhostHierarchy : miss + mbBound ≤ rhoK)
    (hcross : rhoK * O.D.V2.card + O.D.V1.card * (9 * rhoK) <
      ((padGraph
        (regularityReducedGraph Hregular cluster epsilon reducedDensity)).interedges
          O.D.V1 O.D.V2).card)
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (n f0 f1 epsilon1 epsilon2 gamma : ℝ)
    (hn : 0 ≤ n)
    (hMinTarget : (1 - epsilon1) * n ≤ targetA)
    (hdensityOne : ∀ e : MatchingEdge Q.claim67.M, ∀ c,
      sourceDensity (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e c) ≤ 1)
    (hMzeroScalar : 2 * N * rhoK ≤ f0 - epsilon2 * n)
    (hforest : f0 + f1 ≤ n)
    (hhierarchy : 3 * gamma ≤ epsilon2 - epsilon1)
    (hresidualPositive : 0 < f1 + 3 * gamma * n)
    (hN : 0 < N) (hsmallFb : fb < cutoff) (htargetB : 0 < targetB)
    (hrhoK : 0 < rhoK)
    (m : ℕ) (removalBudget : ℝ)
    (scale : CanonicalClusterScaleFacts (padCluster cluster)
      (Sum.inl Q.A) (Sum.inl Q.B) (epsilon : ℝ) quota m)
    (margins : ∀ C : Finset (EvenPadding I), C ⊆ O.D.V1 →
      C.card = rhoK →
      CanonicalMarginScalars P.numParts small
        (canonicalClusterCapacity target slack small rhoK)
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
  let hEq := padGraph_regularityReducedGraph Hregular cluster epsilon
    reducedDensity hreducedDensity
  have hexists := exists_indexedHostSystem_of_richLemma611Output Gdegree
    Hregular Pcluster cluster epsilon reducedDensity hcluster hregularSub
    threshold quota miss rhoK hquota hreducedDensity Q sourceDensity N eta
    targetA targetB fb cutoff lowerV1 upperV1 upperV2 mbEdgesBound mbBound
    lowerA lowerB exceptionalBound O heta hetaHalf hhostHierarchy hcross
  dsimp only at hexists
  obtain ⟨C, hCV1, _hCO, hCcard, ⟨H⟩⟩ := hexists
  have hMzeroC : 2 * N * C.card ≤ f0 - epsilon2 * n := by
    rw [hCcard]
    exact hMzeroScalar
  have marginsC : CanonicalMarginScalars P.numParts small
      (canonicalClusterCapacity target slack small C.card)
      (canonicalSelectedCapacity
        (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1)) rhoK)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (F1 P S))
        (MatchingDecomposition.MoneEdges O.D C).card small)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (Fb P))
        O.D.mbEdges.card small)
      quota m (epsilon : ℝ) (reducedDensity : ℝ) removalBudget := by
    rw [hCcard]
    exact margins C hCV1 hCcard
  exact isContained_of_richCoordinateOutputAtIndexedHost Gdegree Hregular
    Pcluster cluster epsilon reducedDensity threshold quota miss rhoK Q
    sourceDensity N eta targetA targetB fb cutoff lowerV1 upperV1 upperV2
    mbEdgesBound mbBound lowerA lowerB exceptionalBound O hEq C H hT P hsmall
    S hCV1 heta hetaHalf n f0 f1 epsilon1 epsilon2 gamma hn hMinTarget
    (by
      intro e _he c
      exact hdensityOne e c)
    hMzeroC hforest hhierarchy hresidualPositive hN hsmallFb htargetB hrhoK m
    removalBudget scale marginsC online

end Erdos547b.ZhaoClaim616RichCoordinateFinalApplication

#print axioms Erdos547b.ZhaoClaim616RichCoordinateFinalApplication.isContained_of_richCoordinateOutput
