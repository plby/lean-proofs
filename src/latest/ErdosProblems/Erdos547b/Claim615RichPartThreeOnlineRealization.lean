/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichRootSideOnlineRealization
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartThreeRootPlan
import ErdosProblems.Erdos547b.Claim615RichGlobalRootSideFixedStep
import ErdosProblems.Erdos547b.Lemma58GlobalAppendixOnlineSuccessor
import ErdosProblems.Erdos547b.Claim615RichPartThreeTargetPlan

/-!
# Non-result online realization data for the rich Part-3 case

Exceptional physical fibers use the Appendix constructor, while the two
ordinary physical families retain the orientation chosen once on their full
matching-edge fiber.  This module synchronizes those two local constructors
under the common maximal root-good side plan.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientation
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalRootSidePlan
open Erdos547b.ZhaoClaim615RichGlobalOnlineSideApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication
open Erdos547b.ZhaoClaim615RichRootSideOnlineRealization
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan
open Erdos547b.ZhaoClaim615RichGlobalRootSideFixedStep
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58PlannedOwnerLocalStep
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan
open Erdos547b.ZhaoLemma58GlobalFixedOnlineSuccessor
open Erdos547b.ZhaoLemma58GlobalAppendixOnlineSuccessor
open Erdos547b.ZhaoLemma58OnlineParentSideCleaning
open Erdos547b.ZhaoLemma58SelectedOrientationReindex
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoClaim615RichPartThreeTargetPlan

universe u v w

/-- The two local source-data alternatives used in the nonextreme case.
The Appendix alternative records that both root sides are allowed; the fixed
alternative needs no repeated root certificate because it is supplied by the
complete-fiber physical orientation plan. -/
inductive FixedOrAppendixStepData
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole live : Fin 2 → Finset B) (rho density : ℝ)
    (rootSides : Finset (Fin 2)) : Type (max 0 v)
  | appendix
      (data : AppendixStepData F G externalParent whole live rho density)
      (all_root_sides : ∀ c, c ∈ rootSides) :
      FixedOrAppendixStepData F G externalParent orient whole live rho density
        rootSides
  | reindexedAppendix
      (data : ReindexedAppendixStepData F G externalParent whole live rho
        density)
      (all_root_sides : ∀ c, c ∈ rootSides) :
      FixedOrAppendixStepData F G externalParent orient whole live rho density
        rootSides
  | empty (data : EmptyStepData F) :
      FixedOrAppendixStepData F G externalParent orient whole live rho density
        rootSides
  | fixed
      (data : FixedOrientationStepData F G externalParent orient whole live rho
        density) :
      FixedOrAppendixStepData F G externalParent orient whole live rho density
        rootSides

/-- A synchronized fixed-edge scalar record supplies the fixed alternative
with the exact current live sets. -/
noncomputable def fixedOrAppendixStepDataOfFixedOnlineFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k) (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ) (rootCandidate : Fin r → Finset B)
    (n : ℕ) (hn : n < r)
    (state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k) (rootSides : Finset (Fin 2))
    (D : FixedOnlineOwnerEdgeFacts F G assign orient whole endpoint rho density
      rootCandidate n hn state z e)
    (hendpoint : ∀ c, endpoint e c ⊆ whole e c)
    (hwholeDisjoint : Disjoint (whole e 0) (whole e 1)) :
    FixedOrAppendixStepData
      (onlineOwnerBatchForest F assign e n hn) G
      (fun i ↦ extendedRootImage state.rootImage n hn z
        (onlineFiberOwner F assign e
          (OrderedBranchForest.selectedEquiv
            (onlineOwnerBatch F assign e n hn) i)))
      (onlineOwnerBatchFixedOrientation F assign orient e n hn)
      (whole e)
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c))
      (rho e) (density e) rootSides :=
  .fixed (D.toFixedOrientationStepData F G assign orient whole endpoint rho
    density rootCandidate n hn state z e hendpoint hwholeDisjoint)

/-- A synchronized Appendix scalar record supplies the adaptive alternative
once the ambient root-side plan contains both sides. -/
noncomputable def fixedOrAppendixStepDataOfAppendixOnlineFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ) (rootCandidate : Fin r → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (n : ℕ) (hn : n < r)
    (state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k) (rootSides : Finset (Fin 2))
    (D : AppendixOnlineOwnerEdgeFacts F G assign whole endpoint rho density
      rootCandidate n hn state z e)
    (hall : ∀ c, c ∈ rootSides) :
    FixedOrAppendixStepData
      (onlineOwnerBatchForest F assign e n hn) G
      (fun i ↦ extendedRootImage state.rootImage n hn z
        (onlineFiberOwner F assign e
          (OrderedBranchForest.selectedEquiv
            (onlineOwnerBatch F assign e n hn) i)))
      (onlineOwnerBatchFixedOrientation F assign orient e n hn)
      (whole e)
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c))
      (rho e) (density e) rootSides :=
  .appendix (D.toAppendixStepData F G assign whole endpoint rho density
    rootCandidate n hn state z e) hall

/-- Locally reordered synchronized Appendix facts supply the adaptive
alternative without assuming a fixed ordering of the two residual sizes. -/
noncomputable def fixedOrAppendixStepDataOfReindexedAppendixOnlineFacts
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (assign : Fin b → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ) (rootCandidate : Fin r → Finset B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (n : ℕ) (hn : n < r)
    (state : OnlineOwnerPrefixState F G assign endpoint rootCandidate n)
    (z : B) (e : Fin k) (rootSides : Finset (Fin 2))
    (D : ReindexedAppendixOnlineOwnerEdgeFacts F G assign whole endpoint rho
      density rootCandidate n hn state z e)
    (hall : ∀ c, c ∈ rootSides) :
    FixedOrAppendixStepData
      (onlineOwnerBatchForest F assign e n hn) G
      (fun i ↦ extendedRootImage state.rootImage n hn z
        (onlineFiberOwner F assign e
          (OrderedBranchForest.selectedEquiv
            (onlineOwnerBatch F assign e n hn) i)))
      (onlineOwnerBatchFixedOrientation F assign orient e n hn)
      (whole e)
      (fun c ↦ endpoint e c \
        (reparentedEdgeState F G assign endpoint rootCandidate n hn state z e
          |>.used c))
      (rho e) (density e) rootSides :=
  .reindexedAppendix
    (D.toReindexedAppendixStepData F G assign whole endpoint rho density
      rootCandidate n hn state z e) hall

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
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta .nonextreme count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ}
variable (S : SelectedF0 P (nontrivialMajorBranches P) target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1 capb)

/-- State-independent source and host inequalities which are sufficient for
every Appendix owner batch on one complete physical fiber.  Prefix-image and
current-batch cardinalities are derived from the synchronized state; no copy,
embedding, or continuation is stored here. -/
structure RichAppendixFullFiberEdgeFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan.RootTargetPlan P)
    (Fclean : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        plan)
    (e : PhysicalIndex Q sourceDensity E0 Mb) : Type (max u v w) where
  small : ℕ
  rootMargin : ℕ
  sideMargin : ℕ
  liveMargin : ℕ
  cleanBound : Fin 2 → ℕ
  gamma : ℝ
  epsilon : ℝ
  N : ℝ
  component_lower : ∀ i,
    2 ≤ (onlineFiberForest (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e).size i
  component_upper : ∀ i,
    (onlineFiberForest (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e).size i ≤ small
  clean_loss : ∀ c,
    #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb e c \
      richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan e c) ≤ cleanBound c
  root_degree_capacity : ∀ c,
    ((rootMargin +
        (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e).order +
        cleanBound c : ℕ) : ℝ) ≤
      (rootDensity - rootRho) *
        (#(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ)
  live_capacity : ∀ c,
    liveMargin + cleanBound c +
        (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e).order ≤
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb e c).card
  side_slots :
    (onlineFiberForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e).order +
      2 * sideMargin + small ≤ rootMargin + liveMargin
  root_side : rootMargin ≤ sideMargin
  root_round : 3 * epsilon * N ≤ rootMargin
  side_round : (gamma + 3 * epsilon) * N ≤ sideMargin
  factor_nonneg : 0 ≤ rootDensity - rootRho
  epsilonN_nonneg : 0 ≤ epsilon * N
  regular_root : ∀ c,
    rootRho *
        (#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ) < 3 * epsilon * N
  regular_interior : ∀ c,
    rootRho *
        (#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ) ≤ gamma * N
  component_margin : ∀ c,
    (small : ℝ) + rootRho *
        (#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ) ≤
      (rootDensity - rootRho) * (gamma * N)

namespace RichAppendixFullFiberEdgeFacts

/-- Specialize the state-independent complete-fiber bounds to the literal
current residual sets and root pools of one nonempty owner batch. -/
noncomputable def toReindexedAppendixOnlineOwnerEdgeFacts
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan.RootTargetPlan P)
    (Fclean : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        plan)
    (n : ℕ) (hn : n < P.numParts)
    (state : OnlineOwnerPrefixState (branchForest P) G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan)
      (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan) n)
    (z : Bv)
    (hz : z ∈ plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho plan ⟨n, hn⟩)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (hbatch : 0 < #(onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn))
    (hall : ∀ i c, c ∈ plan.branchRootSides
      (onlineOwnerBatchBranch (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn i))
    (D : RichAppendixFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H plan Fclean e) :
    ReindexedAppendixOnlineOwnerEdgeFacts (branchForest P) G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan)
      (fun _ ↦ rootRho) (fun _ ↦ rootDensity)
      (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan) n hn state z e := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let raw := richEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb
  let clean := richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootRho plan
  let whole := richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
    E0 Mb
  let candidate := plannedRootCandidate Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A G rootRho plan
  let fiber := onlineFiberForest (branchForest P) assign e
  let batch := onlineOwnerBatch (branchForest P) assign e n hn
  let batchForest := onlineOwnerBatchForest (branchForest P) assign e n hn
  let used : Fin 2 → Finset Bv :=
    (reparentedEdgeState (branchForest P) G assign clean candidate n hn state z e).used
  let live : Fin 2 → Finset Bv := fun c ↦ clean e c \ used c
  let roots : Fin 2 → Finset Bv := currentRootPool G z live
  have hcomponentLower : ∀ i, 2 ≤ batchForest.size i := by
    intro i
    exact D.component_lower (selectedEquiv batch i)
  have hcomponentUpper : ∀ i, batchForest.size i ≤ D.small := by
    intro i
    exact D.component_upper (selectedEquiv batch i)
  have husedBatch : ∀ c, #(used c) + #batch ≤ fiber.order := by
    intro c
    exact card_reparented_used_add_ownerBatch_card_le_fiber_order
      (branchForest P) G assign clean candidate n hn state z e
      (fun i ↦ Nat.one_le_iff_ne_zero.mpr (by
        intro hzero
        have := hcomponentLower i
        rw [hzero] at this
        omega)) c
  have hused : ∀ c, #(used c) ≤ fiber.order := by
    intro c
    exact (Nat.le_add_right _ _).trans (husedBatch c)
  have hbatchOrder : batchForest.order ≤ fiber.order := by
    change (selectedForest fiber batch).order ≤ fiber.order
    rw [selectedForest_order, OrderedRootedForest.order]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hcleanSubset : ∀ c, clean e c ⊆ raw e c := by
    intro c
    exact onlineSideCleanEndpoint_subset P G candidate assign raw
      plan.coordinateSides e c
  have hrootStrong : ∀ c, D.rootMargin + #batch ≤ #(roots c) := by
    intro c
    let i : Fin #batch := ⟨0, hbatch⟩
    have hplanned := plannedRootCandidate_onlineOwnerBatch_branch_degree
      Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A
      plan G rootRho rootDensity H Fclean n hn z hz e i c (hall i c)
    have hdegreeStatic : D.rootMargin + fiber.order + D.cleanBound c ≤
        #((raw e c).filter (G.Adj z)) := by
      exact_mod_cast (D.root_degree_capacity c).trans hplanned
    have hdegree : (D.rootMargin + #batch) + D.cleanBound c + #(used c) ≤
        #((raw e c).filter (G.Adj z)) := by
      have hub : #(used c) + #batch ≤ fiber.order := husedBatch c
      omega
    exact card_liveRootPool_ge_of_two_stage_bounds G z (raw e c) (clean e c)
      (used c) (D.rootMargin + #batch) (D.cleanBound c) (#(used c))
      (hcleanSubset c) (D.clean_loss c) le_rfl hdegree
  have hrootReserve : ∀ c, D.rootMargin ≤ #(roots c) := by
    intro c
    exact (Nat.le_add_right _ _).trans (hrootStrong c)
  have hrootSlots : #batch + 2 * D.rootMargin ≤ #(roots 0) + #(roots 1) := by
    have h0 := hrootStrong 0
    have h1 := hrootStrong 1
    omega
  have hlive : ∀ c, D.liveMargin ≤ #(live c) := by
    intro c
    apply card_live_ge_of_two_stage_bounds (raw e c) (clean e c) (used c)
      D.liveMargin (D.cleanBound c) (#(used c)) (hcleanSubset c)
      (D.clean_loss c) le_rfl
    have hcap : D.liveMargin + D.cleanBound c + fiber.order ≤ #(raw e c) := by
      simpa only [fiber, raw, assign] using D.live_capacity c
    have hu : #(used c) ≤ fiber.order := hused c
    omega
  have hsideSlots : batchForest.order + 2 * D.sideMargin + D.small ≤
      Nat.min #(roots 0) #(roots 1) + Nat.min #(live 0) #(live 1) := by
    have hrootMin : D.rootMargin ≤ Nat.min #(roots 0) #(roots 1) :=
      Nat.le_min.mpr ⟨hrootReserve 0, hrootReserve 1⟩
    have hliveMin : D.liveMargin ≤ Nat.min #(live 0) #(live 1) :=
      Nat.le_min.mpr ⟨hlive 0, hlive 1⟩
    have hs : fiber.order + 2 * D.sideMargin + D.small ≤
        D.rootMargin + D.liveMargin := by
      simpa only [fiber, assign] using D.side_slots
    have hb := hbatchOrder
    omega
  apply reindexedAppendixOnlineOwnerEdgeFactsOfSymmetricBounds
    (branchForest P) G assign whole clean (fun _ ↦ rootRho)
    (fun _ ↦ rootDensity) candidate n hn state z e D.small D.rootMargin
    D.sideMargin D.gamma D.epsilon D.N hcomponentLower hcomponentUpper
  · simpa only [roots, live, used, clean, candidate, assign] using hrootReserve
  · exact D.root_side
  · simpa only [roots, live, used, clean, candidate, assign, batch] using
      hrootSlots
  · simpa only [roots, live, used, clean, candidate, assign, batchForest] using
      hsideSlots
  · exact D.root_round
  · exact D.side_round
  · simpa only [whole] using
      (whole_pair Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        G rootRho rootDensity H e).1
  · intro c
    exact (Finset.sdiff_subset.trans (hcleanSubset c)).trans
      (endpoint_subset_whole Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c)
  · simpa only [whole] using
      (whole_disjoint (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        hdisjoint e)
  · simpa only [whole] using
      (whole_pair Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        G rootRho rootDensity H e).2
  · exact D.factor_nonneg
  · exact D.epsilonN_nonneg
  · exact D.regular_root
  · exact D.regular_interior
  · intro i c
    have hsize : ((batchForest.size i : ℕ) : ℝ) ≤ D.small := by
      exact_mod_cast hcomponentUpper i
    have hm := D.component_margin c
    linarith

end RichAppendixFullFiberEdgeFacts

/-- State-independent complete-fiber bounds for an ordinary fixed-orientation
edge under the larger physical root-side plan. -/
structure RichRootSideFixedFullFiberEdgeFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan.RootTargetPlan P)
    (Fclean : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        plan)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (e : PhysicalIndex Q sourceDensity E0 Mb) : Type (max u v w) where
  reserve : Fin 2 → ℕ
  cleanBound : Fin 2 → ℕ
  factor_nonneg : 0 ≤ rootDensity - rootRho
  reserve_regular : ∀ c,
    rootRho *
      (#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb e c) : ℝ) ≤ reserve c
  clean_loss : ∀ c,
    #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c \
      richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan e c) ≤ cleanBound c
  total : ∀ c,
    cleanBound c +
        sideLoad (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e)
          (globalFixedFiberOrientation (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R)
              (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
              (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) orient e) c +
        reserve c ≤
      #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c)
  eligible_margin : ∀ c,
    ((cleanBound c +
        sideLoad (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e)
          (globalFixedFiberOrientation (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R)
              (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
              (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) orient e) c +
        (1 + reserve c) : ℕ) : ℝ) ≤
      (rootDensity - rootRho) *
        (#(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ)
  component_upper : ∀ i,
    (onlineFiberForest (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e).size i ≤ small
  component_margin : ∀ c,
    (small : ℝ) + rootRho *
        (#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ) + 1 ≤
      (rootDensity - rootRho) *
        ((#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ) - cleanBound c -
          sideLoad (onlineFiberForest (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R)
              (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
              (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e)
            (globalFixedFiberOrientation (branchForest P)
              (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
                (threshold := threshold) (quota := quota) (R := R)
                (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
                (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) orient e) c)

namespace RichRootSideFixedFullFiberEdgeFacts

/-- Add reduced-pair facts and the exact synchronized owner state to the
state-independent fixed-fiber inequalities. -/
noncomputable def toFixedFullFiberOnlineOwnerEdgeFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan.RootTargetPlan P)
    (Fclean : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        plan)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (n : ℕ) (hn : n < P.numParts)
    (state : OnlineOwnerPrefixState (branchForest P) G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan)
      (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan) n)
    (z : Bv)
    (hz : z ∈ plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho plan ⟨n, hn⟩)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (hroot : ∀ i,
      (onlineOwnerBatchFixedOrientation (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) orient e n hn i) 0 ∈
        plan.branchRootSides
          (onlineOwnerBatchBranch (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R)
              (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
              (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e n hn i))
    (D : RichRootSideFixedFullFiberEdgeFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H plan Fclean
        orient e) :
    FixedFullFiberOnlineOwnerEdgeFacts (branchForest P) G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) orient
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan)
      (fun _ ↦ rootRho) (fun _ ↦ rootDensity)
      (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan) n hn state z e := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let whole := richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
    E0 Mb
  let raw := richEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb
  let clean := richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootRho plan
  let candidate := plannedRootCandidate Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A G rootRho plan
  exact {
    reserve := D.reserve
    permanentBound := D.cleanBound
    uniform := (whole_pair Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb G rootRho rootDensity H e).1
    density_lower := (whole_pair Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb G rootRho rootDensity H e).2
    factor_nonneg := D.factor_nonneg
    reserve_regular := D.reserve_regular
    permanent := D.clean_loss
    total := D.total
    eligible := by
      intro i
      let c := branchRootSide
        (onlineOwnerBatchForest (branchForest P) assign e n hn)
        (onlineOwnerBatchFixedOrientation (branchForest P) assign orient e n hn) i
      have hbatch : 0 < #(onlineOwnerBatch (branchForest P) assign e n hn) := by
        exact Nat.zero_lt_of_lt i.isLt
      have hc : c ∈ plan.branchRootSides
          (onlineOwnerBatchBranch (branchForest P) assign e n hn i) := by
        simpa only [c, branchRootSide, assign] using hroot i
      have hdegree := plannedRootCandidate_onlineOwnerBatch_branch_degree
        Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A
        plan G rootRho rootDensity H Fclean n hn z hz e i c hc
      have hneighbor :
          #((raw e c).filter (G.Adj z)) ≤
            #((whole e c).filter (G.Adj z)) :=
        Finset.card_le_card (fun x hx ↦ Finset.mem_filter.mpr
          ⟨endpoint_subset_whole Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb e c (Finset.mem_filter.mp hx).1,
           (Finset.mem_filter.mp hx).2⟩)
      have hprefix := globalFixedPrefixLoad_add_sideLoadBefore_le_sideLoad
        (branchForest P) assign orient e n hn i c
      have hstatic :
          D.cleanBound c + globalFixedPrefixLoad (branchForest P) assign orient
              e n c +
              (1 + D.reserve c +
                sideLoadBefore
                  (onlineOwnerBatchForest (branchForest P) assign e n hn)
                  (onlineOwnerBatchFixedOrientation (branchForest P) assign
                    orient e n hn) i c) ≤
            #((whole e c).filter (G.Adj z)) := by
        have hreal :
            ((D.cleanBound c +
                sideLoad (onlineFiberForest (branchForest P) assign e)
                  (globalFixedFiberOrientation (branchForest P) assign orient e)
                  c + (1 + D.reserve c) : ℕ) : ℝ) ≤
              #((whole e c).filter (G.Adj z)) := by
          exact (D.eligible_margin c).trans
            (hdegree.trans (by exact_mod_cast hneighbor))
        have hnat : D.cleanBound c +
              sideLoad (onlineFiberForest (branchForest P) assign e)
                (globalFixedFiberOrientation (branchForest P) assign orient e) c +
              (1 + D.reserve c) ≤
            #((whole e c).filter (G.Adj z)) := by
          exact_mod_cast hreal
        omega
      have hrootImage :
          extendedRootImage state.rootImage n hn z
              (onlineFiberOwner (branchForest P) assign e
                (selectedEquiv
                  (onlineOwnerBatch (branchForest P) assign e n hn) i)) = z := by
        have howner := onlineOwnerBatchBranch_owner (branchForest P) assign e n
          hn i
        change extendedRootImage state.rootImage n hn z
          ((branchForest P).owner
            (onlineOwnerBatchBranch (branchForest P) assign e n hn i)) = z
        rw [howner, extendedRootImage_current]
      change D.cleanBound c +
          globalFixedPrefixLoad (branchForest P) assign orient e n c +
          (1 + D.reserve c +
            sideLoadBefore
              (onlineOwnerBatchForest (branchForest P) assign e n hn)
              (onlineOwnerBatchFixedOrientation (branchForest P) assign orient
                e n hn) i c) ≤
        #((whole e c).filter
          (G.Adj (extendedRootImage state.rootImage n hn z
            (onlineFiberOwner (branchForest P) assign e
              (selectedEquiv
                (onlineOwnerBatch (branchForest P) assign e n hn) i)))))
      rw [hrootImage]
      exact hstatic
    component := by
      intro i c
      have hsize :
          ((onlineOwnerBatchForest (branchForest P) assign e n hn).size i : ℝ) ≤
            small := by
        exact_mod_cast D.component_upper
          (selectedEquiv (onlineOwnerBatch (branchForest P) assign e n hn) i)
      have hm := D.component_margin c
      linarith
  }

end RichRootSideFixedFullFiberEdgeFacts

/-- Package a maximal physical root-side plan, complete-fiber ordinary
orientations, and mixed Appendix/fixed local source data into the recursive
realization callback used by exceptional forcing. -/
noncomputable def onlineRealizationDataOfPartThreeRootPlan
    (hT : T.IsTree)
    (havailable : nontrivialMajorBranches P ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (Kroot : RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb))
    (initialRootImage : Fin P.numParts → Bv)
    (edgeRho edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (Kstep : ∀ n (hn : n < P.numParts)
      (state : PlannedCutOnlineOwnerPrefixState P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A
              (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R
                miss Q sourceDensity E0 Mb)))
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A
              (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R
                miss Q sourceDensity E0 Mb)))
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb)).coordinateSides n)
      (z : Bv),
      z ∈ onlineRootEligible P G
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A
              (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R
                miss Q sourceDensity E0 Mb)))
        (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
          (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A
              (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R
                miss Q sourceDensity E0 Mb))) n hn state.state →
      (∀ q, q.val < n → z ≠ state.state.state.rootImage q) →
      ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      FixedOrAppendixStepData
        (onlineOwnerBatchForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e n hn)
        G
        (fun i ↦ extendedRootImage state.state.state.rootImage n hn z
          (onlineFiberOwner (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R) (miss := miss)
              (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
              (P := P) (S := S) (A := A)) e
            (selectedEquiv (onlineOwnerBatch (branchForest P)
              (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
                (threshold := threshold) (quota := quota) (R := R)
                (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
                (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e n hn) i)))
        (onlineOwnerBatchFixedOrientation (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A))
          (partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
            (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
            (R := R) (miss := miss) Q sourceDensity E0 Mb P S D) e n hn)
        (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
          e)
        (fun c ↦ richOnlineSideEndpoint Pcluster Gdegree threshold quota R
            miss Q sourceDensity E0 Mb P S A G rootRho
              (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb P S A
                  (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R
                    miss Q sourceDensity E0 Mb)) e c \
          (reparentedEdgeState (branchForest P) G
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R) (miss := miss)
              (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
              (P := P) (S := S) (A := A))
            (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A G rootRho
                (richRootSideTargetPlan Pcluster Gdegree threshold quota R
                  miss Q sourceDensity E0 Mb P S A
                    (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R
                      miss Q sourceDensity E0 Mb)))
            (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A G rootRho
                (richRootSideTargetPlan Pcluster Gdegree threshold quota R
                  miss Q sourceDensity E0 Mb P S A
                    (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R
                      miss Q sourceDensity E0 Mb)))
            n hn state.state.state z e).used c)
        (edgeRho e) (edgeDensity e)
        ((physicalRootGoodSidePlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb).sides e)) :
    OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P G S A := by
  let Dside := physicalRootGoodSidePlan Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb
  let orient := partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
    (Gdegree := Gdegree) (threshold := threshold) (quota := quota) (R := R)
    (miss := miss) Q sourceDensity E0 Mb P S D
  apply onlineRealizationDataOfRootSidePlan Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity H
    Dside Kroot initialRootImage edgeRho edgeDensity
  intro n hn state z hz hzf e
  cases Kstep n hn state z hz hzf e with
  | appendix data hall =>
      exact plannedAppendixOwnerLocalStepData_of_rootSidePlan Pcluster Gdegree
        threshold quota R miss Q sourceDensity E0 Mb P S A hT Dside G e n hn
        _ _ _ (edgeRho e) (edgeDensity e) data hall
  | reindexedAppendix data hall =>
      exact plannedReindexedAppendixOwnerLocalStepData_of_rootSidePlan Pcluster
        Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A hT Dside G
        e n hn _ _ _ (edgeRho e) (edgeDensity e) data hall
  | empty data => exact PlannedOwnerLocalStepData.empty data
  | fixed data =>
      exact plannedFixedOwnerLocalStepData_of_rootSidePlan Pcluster Gdegree
        threshold quota R miss Q sourceDensity E0 Mb P S A hT Dside G orient e
        n hn _ _ _ (edgeRho e) (edgeDensity e) data
        (fun i ↦ by
          rw [mem_physicalRootGoodSidePlan]
          let assign := richAssign (Pcluster := Pcluster)
            (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
            (R := R) (miss := miss) (Q := Q)
            (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)
          let iFiber := selectedEquiv
            (onlineOwnerBatch (branchForest P) assign e n hn) i
          have hgood := (D.fiber e).root_good iFiber
          change physicalRootGood (Pcluster := Pcluster)
            (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
            (R := R) (miss := miss) (Q := Q)
            (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e
              ((onlineOwnerBatchFixedOrientation (branchForest P) assign orient
                e n hn i) 0)
          have hrestrict :
              onlineOwnerBatchFixedOrientation (branchForest P) assign orient e
                  n hn i =
                globalFixedFiberOrientation (branchForest P) assign orient e
                  iFiber := rfl
          have hfiber :
              globalFixedFiberOrientation (branchForest P) assign orient e =
                (D.fiber e).orient := by
            simpa only [orient, partThreeAuxiliaryGlobalOrient] using
              (globalFixedFiberOrientation_assembledOrient (branchForest P)
                assign (fun f ↦ (D.fiber f).orient) e)
          rw [hrestrict, congrFun hfiber iFiber]
          exact hgood)

end Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization

#print axioms Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization.onlineRealizationDataOfPartThreeRootPlan
#print axioms Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization.fixedOrAppendixStepDataOfFixedOnlineFacts
#print axioms Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization.fixedOrAppendixStepDataOfAppendixOnlineFacts
#print axioms Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization.fixedOrAppendixStepDataOfReindexedAppendixOnlineFacts
#print axioms Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization.RichAppendixFullFiberEdgeFacts.toReindexedAppendixOnlineOwnerEdgeFacts
#print axioms Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization.RichRootSideFixedFullFiberEdgeFacts.toFixedFullFiberOnlineOwnerEdgeFacts
