/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalThresholdApplication
import ErdosProblems.Erdos547b.Claim615RichExceptionalOnlineForcing

/-!
# Non-result online realization data for the rich threshold case

This module packages the source-only complete-fiber threshold orientation,
planned root cleaning, and the literal host scalar facts as the recursive
callback consumed by the exceptional-family forcing theorem.  The public
constructor contains no copy, embedding, containment, or continuation input.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichThresholdOnlineRealization

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientation
open Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootCleaning
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalFixedPlan
open Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts
open Erdos547b.ZhaoClaim615RichGlobalThresholdHostFacts
open Erdos547b.ZhaoClaim615RichGlobalThresholdApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlineSideApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlanCertifiedApplication
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58OnlineParentSideCleaning
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan
open Erdos547b.ZhaoLemma58GlobalFixedOnlineSuccessor

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)

variable {L : Finset (EvenPadding I)} {eta N targetB cap : ℝ}
variable {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta .unbalanced count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ} {ratio gamma epsilon : ℝ}
variable (S : SelectedF0 P (balancedMajorBranches P ratio) target slack)
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
    (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
    (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))

/-- Package the literal threshold orientation and its source/live-host facts
as the non-result recursive realization data used by exceptional forcing. -/
noncomputable def onlineRealizationDataOfThresholdRootPlan
    (hT : T.IsTree)
    (havailable : balancedMajorBranches P ratio ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalThresholdRootPlan Q sourceDensity E0 Mb P S A)
    (Kroot : RichThresholdRootCleaningScalarFacts Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H D)
    (initialRootImage : Fin P.numParts → Bv)
    (Kedge : ∀ e,
      RichThresholdFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho rootDensity H D
          (Kroot.toRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity H D)
        e) :
    OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P G S A := by
  let orient := physicalFiberOrient Q sourceDensity E0 Mb P S A
    D.toRootOrientationPlan.orient
  let plan := richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A orient
  let F := Kroot.toRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity H D
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let whole := richWhole Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb
  let candidate := plannedRootCandidate Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A G rootRho plan
  let clean := richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootRho plan
  have hcleanWhole : ∀ e c, clean e c ⊆ whole e c := by
    intro e c
    exact (onlineSideCleanEndpoint_subset P G candidate assign
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb) plan.coordinateSides e c).trans
        (endpoint_subset_whole
          (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          e c)
  have hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1) :=
    whole_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) hdisjoint
  refine {
    rootRho := rootRho
    rootDensity := rootDensity
    pairRealization := H
    plan := plan
    rootCleaning := F
    initialRootImage := initialRootImage
    edgeRho := fun _ ↦ rootRho
    edgeDensity := fun _ ↦ rootDensity
    successor := ?_
  }
  intro n hn state z hz hzf
  let statePlain : PlannedOnlineOwnerPrefixState (branchForest P) G assign
      clean candidate (globalFixedCoordinateAllowed (branchForest P) assign
        orient) n :=
    { state := state.state.state
      coordinate_side_mem := by
        intro j hj a
        simpa only [onlineCoordinateSide, plan, richFixedRootTargetPlan, assign,
          orient] using
          state.coordinate_side_mem j hj a }
  exact plannedOnlineOwnerSuccessorDataOfFixedFullFiberFacts (branchForest P) G
    assign orient whole clean hcleanWhole hwholeDisjoint (fun _ ↦ rootRho)
    (fun _ ↦ rootDensity) candidate n hn statePlain z (fun e ↦
      (richFixedFullFiberEdgeFactsOfThresholdRootPlan Pcluster Gdegree
        threshold quota R miss Q sourceDensity E0 Mb P S A G rootRho
        rootDensity H D F e (Kedge e)).toFixedFullFiberOnlineOwnerEdgeFacts
          Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A G
          rootRho rootDensity H orient F n hn state.state.state z e
          (onlineRootEligible_subset P G assign clean candidate n hn state.state
            hz))

end Erdos547b.ZhaoClaim615RichThresholdOnlineRealization

#print axioms Erdos547b.ZhaoClaim615RichThresholdOnlineRealization.onlineRealizationDataOfThresholdRootPlan
