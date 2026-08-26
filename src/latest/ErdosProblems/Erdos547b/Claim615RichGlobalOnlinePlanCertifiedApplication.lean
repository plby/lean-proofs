/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalOnlineSideApplication
import ErdosProblems.Erdos547b.Lemma58GlobalPlannedOwnerSuccessor

/-!
# Plan-certified rich synchronized online application

This wrapper combines planned root cleaning, side-aware permanent endpoint
cleaning, and the synchronized owner recursion.  The stored coordinate-side
invariant discharges all dynamic cut-parent-side obligations internally.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalOnlinePlanCertifiedApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616HierarchyAttachments
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
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalOnlineApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlineSideApplication
open Erdos547b.ZhaoLemma58RootCandidateCleaning
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalOwnerBranchImage
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58GlobalCutAssembly
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
open Erdos547b.ZhaoLemma58OnlineParentSideCleaning

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

/-- Rich synchronized online realization whose sole recursive premise is the
plan-certified local source/live-host datum for the current owner batch. -/
theorem exists_treeCopy_of_richPlanCertifiedOnline
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : RootTargetPlan P)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H plan)
    (initialRootImage : Fin P.numParts → Bv)
    (edgeRho edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (hsuccessor : ∀ n (hn : n < P.numParts)
      (state : PlannedCutOnlineOwnerPrefixState P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan)
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan)
        plan.coordinateSides n)
      z,
      z ∈ onlineRootEligible P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan)
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan) n hn state.state →
      (∀ q, q.val < n → z ≠ state.state.state.rootImage q) →
      PlannedOnlineOwnerSuccessorData (branchForest P) G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan)
        edgeRho edgeDensity
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho plan)
        plan.branchRootSides plan.coordinateSides n hn state.state.state z) :
    Nonempty (T.Copy G) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let whole := richWhole Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb
  let raw := richEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb
  let candidate := plannedRootCandidate Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A G rootRho plan
  let clean := richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootRho plan
  have hrawWhole : ∀ e c, raw e c ⊆ whole e c :=
    endpoint_subset_whole
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
  have hfirst : P.numParts ≤ #(candidate ⟨0, P.numParts_pos⟩) :=
    numParts_le_card_plannedRootCandidate Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H plan F _
  have hrootLink : ∀ q (hq : q.val ≠ 0)
      (hroot : P.parent q hq = P.roots (P.parentPart q hq))
      x, x ∈ candidate (P.parentPart q hq) →
      P.numParts ≤ #((candidate q).filter (G.Adj x)) := by
    intro q hq hroot x hx
    exact numParts_le_neighbors_plannedRootCandidate Pcluster Gdegree
      threshold quota R miss Q sourceDensity E0 Mb P S A hT G rootRho
      rootDensity H plan F q hq hroot x hx
  obtain ⟨state⟩ := exists_plannedCutOnlineOwnerPrefixState_sideCleaning
    P G assign whole raw hrawWhole
    (whole_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) hdisjoint)
    edgeRho edgeDensity candidate plan.coordinateSides plan.branchRootSides
    initialRootImage hfirst hrootLink hsuccessor
  have hcleanSupport : ∀ e e', e ≠ e' →
      Disjoint (clean e 0 ∪ clean e 1) (clean e' 0 ∪ clean e' 1) := by
    intro e e' he
    apply (endpointSupport_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      hdisjoint e e' he).mono
    · exact Finset.union_subset_union
        (onlineSideCleanEndpoint_subset P G candidate assign raw
          plan.coordinateSides e 0)
        (onlineSideCleanEndpoint_subset P G candidate assign raw
          plan.coordinateSides e 1)
    · exact Finset.union_subset_union
        (onlineSideCleanEndpoint_subset P G candidate assign raw
          plan.coordinateSides e' 0)
        (onlineSideCleanEndpoint_subset P G candidate assign raw
          plan.coordinateSides e' 1)
  refine ⟨treeCopyOfCutOnlineState P G assign clean candidate state.state
    hcleanSupport ?_⟩
  intro q e c
  have hrawRoot := rootCandidate_subset_raw G rootRho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb) q (state.state.state.root_mem q q.isLt)
  have hout := Finset.disjoint_left.mp
    (rootRawSide_disjoint_endpoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (componentReservoirSide P q) e c) hrawRoot
  exact fun hm ↦ hout
    (onlineSideCleanEndpoint_subset P G candidate assign raw
      plan.coordinateSides e c hm)

end Erdos547b.ZhaoClaim615RichGlobalOnlinePlanCertifiedApplication

#print axioms Erdos547b.ZhaoClaim615RichGlobalOnlinePlanCertifiedApplication.exists_treeCopy_of_richPlanCertifiedOnline
