/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateFinalApplication
import ErdosProblems.Erdos547b.Section6EventualParameters

/-!
# Eventual-parameter specialization of rich coordinate Claim 6.16

All parameter-only premises of the final rich-output composition are
discharged here.  The remaining hypotheses are the host/decomposition and
tree-mass inequalities which genuinely depend on the objects selected later.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateEventualApplication

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
open Erdos547b.ZhaoClaim616RichCoordinateFinalApplication
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSection6EventualParameters
open Erdos547b.ZhaoLemma59Part2Full

universe u v w

variable {V : Type u} {B : Type v} {I : Type w}
variable [Fintype V] [DecidableEq V]
variable [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- The direct Eventual caller of the rich-output Claim-6.16 endpoint. -/
theorem isContained_of_eventualRichCoordinateOutput
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    (reducedK : ℕ) (hreducedKLarge : section6K₀ beta ≤ reducedK)
    (Gdegree Hregular : SimpleGraph B)
    [DecidableRel Gdegree.Adj] [DecidableRel Hregular.Adj]
    (Pcluster : ClusterAssignment B I) (cluster : I → Finset B)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (hregularSub : Hregular ≤ Gdegree)
    (threshold quota : ℕ) (hquota : 0 < quota)
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota
      (regularityReducedGraph Hregular cluster (regularityEpsilon beta)
        (reducedDensity beta))
      (largeClustersAtLeast Pcluster Gdegree threshold quota)
      (claim61Miss beta reducedK))
    (sourceDensity : EvenPadding I → EvenPadding I → ℝ)
    (N n targetB fb cutoff : ℝ)
    (lowerV1 upperV1 upperV2 : ℕ)
    (O : RichLemma611Output Pcluster Gdegree threshold quota
      (regularityReducedGraph Hregular cluster (regularityEpsilon beta)
        (reducedDensity beta))
      (claim61Miss beta reducedK) Q sourceDensity N (eta beta : ℝ)
      (lemma611TargetA beta n) targetB fb cutoff lowerV1 upperV1 upperV2
      (claim617Q beta reducedK) (2 * claim617Q beta reducedK)
      ((1 - 10 * Real.sqrt (lemma611D beta)) * n + 4 * N)
      ((1 - 10 * Real.sqrt (lemma611D beta)) * n + 4 * N)
      ((eta beta : ℝ) * reducedK))
    (hcross : claim616Scale beta reducedK * O.D.V2.card +
        O.D.V1.card * (9 * claim616Scale beta reducedK) <
      ((padGraph
        (regularityReducedGraph Hregular cluster (regularityEpsilon beta)
          (reducedDensity beta))).interedges O.D.V1 O.D.V2).card)
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (f0 f1 : ℝ) (hn : 0 ≤ n)
    (hdensityOne : ∀ e : MatchingEdge Q.claim67.M, ∀ c,
      sourceDensity (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e c) ≤ 1)
    (hMzeroScalar : 2 * N * claim616Scale beta reducedK ≤
      f0 - claim616EpsilonTwo beta * n)
    (hforest : f0 + f1 ≤ n)
    (hresidualPositive : 0 < f1 + 3 * claim616Gamma beta * n)
    (hN : 0 < N) (hsmallFb : fb < cutoff) (htargetB : 0 < targetB)
    (m : ℕ) (removalBudget : ℝ)
    (scale : CanonicalClusterScaleFacts (padCluster cluster)
      (Sum.inl Q.A) (Sum.inl Q.B) (regularityEpsilon beta : ℝ) quota m)
    (margins : ∀ C : Finset (EvenPadding I), C ⊆ O.D.V1 →
      C.card = claim616Scale beta reducedK →
      CanonicalMarginScalars P.numParts small
        (canonicalClusterCapacity target slack small
          (claim616Scale beta reducedK))
        (canonicalSelectedCapacity
          (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1))
          (claim616Scale beta reducedK))
        (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (F1 P S))
          (MatchingDecomposition.MoneEdges O.D C).card small)
        (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (Fb P))
          O.D.mbEdges.card small)
        quota m (regularityEpsilon beta : ℝ) (reducedDensity beta : ℝ)
        removalBudget)
    (online : CanonicalOnlineScalars
      (Fintype.card
          (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey
            (Erdos547b.ZhaoLemma614HierarchicalFullTree.wholeOrderedTree
              T hT globalRoot)) +
        (P.numParts + Fintype.card (BranchIndex P) + P.numParts))
      small m quota (regularityEpsilon beta : ℝ) removalBudget) :
    T.IsContained Hregular := by
  have hreducedDensity : 0 < reducedDensity beta :=
    reducedDensity_pos hbeta
  have heta : (0 : ℝ) < (eta beta : ℝ) := by
    exact_mod_cast eta_pos hbeta
  have hetaHalf : (eta beta : ℝ) < 1 / 2 := by
    have hetaLe := eta_le_rho_div_1000 hbeta hbetaOne
    have hrho : (rho beta : ℝ) ≤ 1 := by
      exact_mod_cast rho_le_one hbeta hbetaOne
    linarith
  have hhostHierarchy : claim61Miss beta reducedK +
      2 * claim617Q beta reducedK ≤ claim616Scale beta reducedK := by
    have hreserve := claim616_reserve_inequality hbeta hbetaOne
      hreducedKLarge
    calc
      claim61Miss beta reducedK + 2 * claim617Q beta reducedK ≤
          2 * claim61C beta reducedK + 1 + 4 * claim617Q beta reducedK := by
        simp only [claim61Miss]
        omega
      _ ≤ claim616Scale beta reducedK := hreserve
  have hMinTarget :
      (1 - lemma611EpsilonOne beta) * n ≤ lemma611TargetA beta n := by
    simp only [lemma611TargetA]
    exact le_rfl
  have hhierarchy : 3 * claim616Gamma beta ≤
      claim616EpsilonTwo beta - lemma611EpsilonOne beta :=
    claim616_margin_hierarchy hbeta hbetaOne
  have hrhoK : 0 < claim616Scale beta reducedK :=
    claim616Scale_pos hbeta hbetaOne hreducedKLarge
  exact isContained_of_richCoordinateOutput Gdegree Hregular Pcluster cluster
    (regularityEpsilon beta) (reducedDensity beta) threshold quota
    (claim61Miss beta reducedK) (claim616Scale beta reducedK) Q sourceDensity N
    (eta beta : ℝ) (lemma611TargetA beta n) targetB fb cutoff lowerV1 upperV1
    upperV2 (claim617Q beta reducedK) (2 * claim617Q beta reducedK)
    ((1 - 10 * Real.sqrt (lemma611D beta)) * n + 4 * N)
    ((1 - 10 * Real.sqrt (lemma611D beta)) * n + 4 * N)
    ((eta beta : ℝ) * reducedK) O hcluster hregularSub hquota
    hreducedDensity heta hetaHalf hhostHierarchy hcross hT P hsmall S n f0 f1
    (lemma611EpsilonOne beta) (claim616EpsilonTwo beta)
    (claim616Gamma beta) hn hMinTarget hdensityOne hMzeroScalar hforest
    hhierarchy hresidualPositive hN hsmallFb htargetB hrhoK m removalBudget
    scale margins online

end Erdos547b.ZhaoClaim616RichCoordinateEventualApplication

#print axioms Erdos547b.ZhaoClaim616RichCoordinateEventualApplication.isContained_of_eventualRichCoordinateOutput
