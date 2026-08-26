/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalOnlinePlanCertifiedApplication
import ErdosProblems.Erdos547b.Lemma58GlobalFixedOrientationPlan
import ErdosProblems.Erdos547b.Lemma58GlobalFixedOnlineSuccessor

/-!
# Fixed edge-orientation plans for the rich synchronized backend

Parts 1/2 choose one orientation for each literal global branch before the
owner-by-owner realization begins.  The corresponding root and coordinate
target plan consists of the singleton side selected by that orientation.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalFixedPlan

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlineSideApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlanCertifiedApplication
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58OnlineParentSideCleaning
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
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
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
variable {target slack : ℕ}
variable (S : SelectedF0 P available target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    cap0 cap1 capb)

/-- Singleton root/coordinate target plan induced by one fixed orientation
of every literal global branch. -/
def richFixedRootTargetPlan
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2) : RootTargetPlan P where
  branchRootSides := globalFixedRootAllowed (branchForest P)
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)) orient
  coordinateSides := globalFixedCoordinateAllowed (branchForest P)
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)) orient

/-- Rich synchronized realization specialized to the singleton plan of a
fixed global branch orientation. -/
theorem exists_treeCopy_of_richFixedPlanCertifiedOnline
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient))
    (initialRootImage : Fin P.numParts → Bv)
    (edgeRho edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (hsuccessor : ∀ n (hn : n < P.numParts)
      (state : PlannedCutOnlineOwnerPrefixState P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
        (globalFixedCoordinateAllowed (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) orient) n)
      z,
      z ∈ onlineRootEligible P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient)) n hn state.state →
      (∀ q, q.val < n → z ≠ state.state.state.rootImage q) →
      PlannedOnlineOwnerSuccessorData (branchForest P) G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
        edgeRho edgeDensity
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
        (globalFixedRootAllowed (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) orient)
        (globalFixedCoordinateAllowed (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) orient)
        n hn state.state.state z) :
    Nonempty (T.Copy G) := by
  exact exists_treeCopy_of_richPlanCertifiedOnline Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A hT G hdisjoint rootRho
    rootDensity H
    (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient) F initialRootImage edgeRho edgeDensity
    hsuccessor

/-- Fixed-plan rich realization whose recursive input consists only of the
literal per-edge scalar/regular-pair facts in the current state. -/
theorem exists_treeCopy_of_richFixedScalarOnline
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient))
    (initialRootImage : Fin P.numParts → Bv)
    (edgeRho edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (facts : ∀ n (hn : n < P.numParts)
      (state : PlannedCutOnlineOwnerPrefixState P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
        (globalFixedCoordinateAllowed (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) orient) n)
      (z : Bv),
      z ∈ onlineRootEligible P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient)) n hn state.state →
      (∀ q, q.val < n → z ≠ state.state.state.rootImage q) →
      ∀ e, FixedFullFiberOnlineOwnerEdgeFacts (branchForest P) G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) orient
        (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
        edgeRho edgeDensity
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient)) n hn state.state.state z e) :
    Nonempty (T.Copy G) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let whole := richWhole Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb
  let raw := richEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb
  let plan := richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A orient
  let candidate := plannedRootCandidate Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A G rootRho plan
  let clean := richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootRho plan
  have hcleanWhole : ∀ e c, clean e c ⊆ whole e c := by
    intro e c
    exact (onlineSideCleanEndpoint_subset P G candidate assign raw
      plan.coordinateSides e c).trans
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
  apply exists_treeCopy_of_richFixedPlanCertifiedOnline Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A hT G hdisjoint rootRho
    rootDensity H orient F initialRootImage edgeRho edgeDensity
  intro n hn state z hz hzf
  let statePlain : PlannedOnlineOwnerPrefixState (branchForest P) G assign
      clean candidate (globalFixedCoordinateAllowed (branchForest P) assign
        orient) n :=
    { state := state.state.state
      coordinate_side_mem := by
        intro j hj a
        simpa only [onlineCoordinateSide] using
          state.coordinate_side_mem j hj a }
  exact plannedOnlineOwnerSuccessorDataOfFixedFullFiberFacts (branchForest P) G
    assign orient whole clean hcleanWhole hwholeDisjoint edgeRho edgeDensity
    candidate n hn statePlain z (facts n hn state z hz hzf)

end Erdos547b.ZhaoClaim615RichGlobalFixedPlan

#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPlan.exists_treeCopy_of_richFixedPlanCertifiedOnline
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPlan.exists_treeCopy_of_richFixedScalarOnline
