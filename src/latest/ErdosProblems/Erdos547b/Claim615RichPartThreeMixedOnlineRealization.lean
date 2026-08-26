/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPartThreeOnlineRealization

/-!
# Synchronized mixed fixed/Appendix realization

This module closes the state-dependent gap in the Part-3 online recursion.
Ordinary physical fibers use the one orientation fixed on their complete
fiber, while adaptive fibers invoke Appendix A against the literal residual
sets.  The mixed target plan remembers exactly this distinction, so the used
set on an ordinary edge is charged by its exact fixed prefix load.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPartThreeMixedOnlineRealization

open Finset Fintype SimpleGraph
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
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlineSideApplication
open Erdos547b.ZhaoClaim615RichRootSideOnlineRealization
open Erdos547b.ZhaoClaim615RichGlobalRootSidePlan
open Erdos547b.ZhaoClaim615RichPartThreeTargetPlan
open Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58DynamicBatchAppend
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
variable (E0 : SelectedExceptionalEdges Q sourceDensity L eta .nonextreme count)
variable (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ}
variable (S : SelectedF0 P (nontrivialMajorBranches P) target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1 capb)

/-- The literal mixed plan attached to the auxiliary complete-fiber
orientations. -/
abbrev partThreeMixedPlan
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop) : RootTargetPlan P :=
  partThreeRootTargetPlan Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A
      (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R
        miss Q sourceDensity E0 Mb)
      (partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
        (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
        (R := R) (miss := miss) Q sourceDensity E0 Mb P S D)
      adaptive

/-- The complete-fiber orientation supplied by the Part-3 auxiliary plan has
an admissible root side on every literal branch. -/
theorem partThreeAuxiliaryGlobalOrient_root_mem
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) :
    partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
        (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
        (R := R) (miss := miss) Q sourceDensity E0 Mb P S D j 0 ∈
      (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb).sides
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A) j) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let orient := partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
    (Gdegree := Gdegree) (threshold := threshold) (quota := quota) (R := R)
    (miss := miss) Q sourceDensity E0 Mb P S D
  let e := assign j
  let i := assignmentIndex assign j
  have hgood := (D.fiber e).root_good i
  have hfiber :
      globalFixedFiberOrientation (branchForest P) assign orient e =
        (D.fiber e).orient := by
    simpa only [orient, partThreeAuxiliaryGlobalOrient] using
      (globalFixedFiberOrientation_assembledOrient (branchForest P) assign
        (fun f ↦ (D.fiber f).orient) e)
  rw [mem_physicalRootGoodSidePlan]
  change physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e
      (orient j 0)
  have hrestrict : globalFixedFiberOrientation (branchForest P) assign orient e
      i = orient j := by
    change orient
      (((selectedEquiv (matchingFiber assign (assign j)))
        (assignmentIndex assign j) : {x // x ∈ matchingFiber assign (assign j)}) :
          ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) = orient j
    rw [selectedEquiv_assignmentIndex]
  rw [← hrestrict, hfiber]
  exact hgood

/-- The cleaned-root certificate for the mixed fixed/adaptive plan. -/
theorem partThreeMixedRootCleaningFacts
    (hT : T.IsTree)
    (havailable : nontrivialMajorBranches P ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ) (hrootRho : 0 ≤ rootRho)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop)
    (Kroot : RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb)) :
    RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (partThreeMixedPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A D adaptive) := by
  let Dside := physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb
  let orient := partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
    (Gdegree := Gdegree) (threshold := threshold) (quota := quota) (R := R)
    (miss := miss) Q sourceDensity E0 Mb P S D
  let Fold := Kroot.toRootCleaningFacts Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A hT havailable
    G rootRho rootDensity H Dside
  exact rootCleaningFactsOfPartThreeTargetPlan Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A hT G rootRho rootDensity H Dside orient
    adaptive hrootRho
      (partThreeAuxiliaryGlobalOrient_root_mem Pcluster Gdegree threshold quota
        R miss Q sourceDensity E0 Mb P S A D)
      Fold

/-- State-independent local facts for every physical fiber.  The adaptive
alternative supplies the symmetric Appendix inequalities; every other edge
supplies complete-fiber fixed-orientation inequalities. -/
structure PartThreeMixedFullFiberFacts
    (hT : T.IsTree)
    (havailable : nontrivialMajorBranches P ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ) (hrootRho : 0 ≤ rootRho)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop)
    (Kroot : RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R
          miss Q sourceDensity E0 Mb)) : Type (max u v w) where
  adaptive_all : ∀ e, adaptive e → ∀ c,
    c ∈ (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb).sides e
  appendix : ∀ e, adaptive e →
    RichAppendixFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
      (partThreeMixedPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A D adaptive)
      (partThreeMixedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity hrootRho
        H D adaptive Kroot) e
  fixed : ∀ e, ¬ adaptive e →
    RichRootSideFixedFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
      (partThreeMixedPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A D adaptive)
      (partThreeMixedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity hrootRho
        H D adaptive Kroot)
      (partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
        (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
        (R := R) (miss := miss) Q sourceDensity E0 Mb P S D) e

/-- Build the complete non-result realization package from state-independent
full-fiber facts.  All prefix-used bounds, residual live sets, and local
embeddings are constructed internally. -/
noncomputable def onlineRealizationDataOfPartThreeMixedFullFiberFacts
    (hT : T.IsTree)
    (havailable : nontrivialMajorBranches P ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ) (hrootRho : 0 ≤ rootRho)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (adaptive : PhysicalIndex Q sourceDensity E0 Mb → Prop)
    (Kroot : RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R
          miss Q sourceDensity E0 Mb))
    (initialRootImage : Fin P.numParts → Bv)
    (Kedge : PartThreeMixedFullFiberFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity
      hrootRho H D adaptive Kroot) :
    OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P G S A := by
  let Dside := physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let orient := partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
    (Gdegree := Gdegree) (threshold := threshold) (quota := quota) (R := R)
    (miss := miss) Q sourceDensity E0 Mb P S D
  let plan := partThreeMixedPlan Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A D adaptive
  let Fclean := partThreeMixedRootCleaningFacts Pcluster Gdegree threshold quota
    R miss Q sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity
    hrootRho H D adaptive Kroot
  let whole := richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
    E0 Mb
  let endpoint := richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A G rootRho plan
  let candidate := plannedRootCandidate Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A G rootRho plan
  have hendpoint : ∀ e c, endpoint e c ⊆ whole e c := by
    intro e c
    exact (onlineSideCleanEndpoint_subset P G candidate assign
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb) plan.coordinateSides e c).trans
      (endpoint_subset_whole Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c)
  have hwholeDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1) := by
    intro e
    simpa only [whole] using
      (whole_disjoint (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        hdisjoint e)
  refine {
    rootRho := rootRho
    rootDensity := rootDensity
    pairRealization := H
    plan := plan
    rootCleaning := Fclean
    initialRootImage := initialRootImage
    edgeRho := fun _ ↦ rootRho
    edgeDensity := fun _ ↦ rootDensity
    successor := ?_
  }
  intro n hn state z hz _hzfresh e
  have hzCandidate : z ∈ candidate ⟨n, hn⟩ :=
    onlineRootEligible_subset P G assign endpoint candidate n hn state.state hz
  let batch := onlineOwnerBatch (branchForest P) assign e n hn
  by_cases hbatch : #batch = 0
  · exact .empty ⟨by simpa only [onlineOwnerBatchForest, batch] using hbatch⟩
  · have hbatchPos : 0 < #batch := Nat.pos_of_ne_zero hbatch
    by_cases ha : adaptive e
    · have hallPlan : ∀ i c, c ∈ plan.branchRootSides
          (onlineOwnerBatchBranch (branchForest P) assign e n hn i) := by
        intro i c
        have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
        change c ∈ Dside.sides
          (assign (onlineOwnerBatchBranch (branchForest P) assign e n hn i))
        rw [he]
        exact Kedge.adaptive_all e ha c
      let Donline := (Kedge.appendix e ha).toReindexedAppendixOnlineOwnerEdgeFacts
        Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A
        hdisjoint G rootRho rootDensity H plan Fclean n hn state.state.state z
        hzCandidate e hbatchPos hallPlan
      let Dlocal := Donline.toReindexedAppendixStepData (branchForest P) G assign
        whole endpoint (fun _ ↦ rootRho) (fun _ ↦ rootDensity) candidate n hn
        state.state.state z e
      apply PlannedOwnerLocalStepData.reindexedAppendix Dlocal
      · exact hallPlan
      · intro i a c
        let zg : Σ j, Fin ((branchForest P).branches.size j) :=
          ⟨onlineOwnerBatchBranch (branchForest P) assign e n hn i,
            onlineOwnerBatchVertex (branchForest P) assign e n hn i a⟩
        have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
        have haz : adaptive (assign zg.1) := by simpa only [zg, he] using ha
        change c ∈ plan.coordinateSides zg
        rw [show plan.coordinateSides zg = Dside.sides (assign zg.1) by
          simpa only [plan, partThreeMixedPlan] using
            partThreeRootTargetPlan_coordinateSides_adaptive Pcluster Gdegree
              threshold quota R miss Q sourceDensity E0 Mb P S A Dside orient
              adaptive zg haz]
        rw [he]
        exact Kedge.adaptive_all e ha c
    · have hrootPlan : ∀ i,
          (onlineOwnerBatchFixedOrientation (branchForest P) assign orient e n
            hn i) 0 ∈ plan.branchRootSides
              (onlineOwnerBatchBranch (branchForest P) assign e n hn i) := by
        intro i
        have hroot := auxiliary_onlineOwnerBatch_root_mem
          (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
          (quota := quota) (R := R) (miss := miss) Q sourceDensity E0 Mb P S
          D e n hn i
        have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
        simpa only [plan, partThreeMixedPlan,
          partThreeRootTargetPlan_branchRootSides, he, orient, assign, Dside]
          using hroot
      let Dfull := (Kedge.fixed e ha).toFixedFullFiberOnlineOwnerEdgeFacts
        Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A G
        rootRho rootDensity H plan Fclean orient n hn state.state.state z
        hzCandidate e hrootPlan
      let Dprefix := Dfull.toFixedPrefixOnlineOwnerEdgeFacts (branchForest P) G
        assign orient whole endpoint (fun _ ↦ rootRho) (fun _ ↦ rootDensity)
        candidate n hn state.state.state z e
      have hused : ∀ c,
          #((reparentedEdgeState (branchForest P) G assign endpoint candidate n
            hn state.state.state z e).used c) ≤
            globalFixedPrefixLoad (branchForest P) assign orient e n c := by
        intro c
        exact
          Erdos547b.ZhaoClaim615RichPartThreeTargetPlan.PlannedCutOnlineOwnerPrefixState.card_reparented_used_le_partThreeFixedPrefix
            Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A
            G Dside orient adaptive endpoint candidate n hn state z e ha c
      let Donline := Dprefix.toFixedOnlineOwnerEdgeFacts (branchForest P) G
        assign orient whole endpoint (fun _ ↦ rootRho) (fun _ ↦ rootDensity)
        candidate n hn state.state.state z e hused
      let Dlocal := Donline.toFixedOrientationStepData (branchForest P) G assign
        orient whole endpoint (fun _ ↦ rootRho) (fun _ ↦ rootDensity)
        candidate n hn state.state.state z e (hendpoint e) (hwholeDisjoint e)
      apply PlannedOwnerLocalStepData.fixed Dlocal
      · exact hrootPlan
      · intro i a
        let zg : Σ j, Fin ((branchForest P).branches.size j) :=
          ⟨onlineOwnerBatchBranch (branchForest P) assign e n hn i,
            onlineOwnerBatchVertex (branchForest P) assign e n hn i a⟩
        have he := onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
        have hnot : ¬ adaptive (assign zg.1) := by simpa only [zg, he] using ha
        change (onlineOwnerBatchFixedOrientation (branchForest P) assign orient
          e n hn i)
            ((onlineOwnerBatchForest (branchForest P) assign e n hn).isTree i
              |>.coloringTwoOfVert
                ((onlineOwnerBatchForest (branchForest P) assign e n hn).root i)
                a) ∈ plan.coordinateSides zg
        rw [show plan.coordinateSides zg =
            {globalFixedCoordinateSide (branchForest P) assign orient zg} by
          simpa only [plan, partThreeMixedPlan] using
            partThreeRootTargetPlan_coordinateSides_fixed Pcluster Gdegree
              threshold quota R miss Q sourceDensity E0 Mb P S A Dside orient
              adaptive zg hnot]
        exact onlineOwnerBatchFixedOrientation_coordinate_mem
          (branchForest P) assign orient e n hn i a

end Erdos547b.ZhaoClaim615RichPartThreeMixedOnlineRealization

#print axioms Erdos547b.ZhaoClaim615RichPartThreeMixedOnlineRealization.partThreeAuxiliaryGlobalOrient_root_mem
#print axioms Erdos547b.ZhaoClaim615RichPartThreeMixedOnlineRealization.partThreeMixedRootCleaningFacts
#print axioms Erdos547b.ZhaoClaim615RichPartThreeMixedOnlineRealization.onlineRealizationDataOfPartThreeMixedFullFiberFacts
