/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalFixedPhysicalPlan

/-!
# Complete synchronized Claim 6.15 application from a physical plan

This module packages the scalar inequalities which remain after the checked
physical-fiber orientation constructors, planned root cleaning, and permanent
host cleaning have been composed.  The public theorem returns an actual tree
copy and has no embedding, copy, continuation, or online-state premise.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalApplication

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
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim615RichPhysicalFiberApplication
open Erdos547b.ZhaoClaim615RichPhysicalFiberScalarApplication
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalFixedPlan
open Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts
open Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics

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

/-- Exact scalar boundary remaining after a physical plan has selected all
fiber orientations. -/
structure RichFixedPhysicalPlanScalarFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity removalBudget : ℝ)
    (plan : PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S cap0 cap1 capb A rootRho rootDensity
        removalBudget) : Type (max u v w) where
  cleaning_root_budget : ∀ q,
    P.numParts + richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A rootRho
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient)) q ≤
      quota
  cleaning_root_link : ∀ j (hj : j.val ≠ 0)
    (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
    (P.numParts : ℝ) +
        richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A rootRho
            (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A
                (physicalFiberOrient Q sourceDensity E0 Mb P S A
                  plan.orient)) j ≤
      (rootDensity - rootRho) * quota
  factor_nonneg : 0 ≤ rootDensity - rootRho
  root_candidate_budget : ∀ q,
    thresholdReserve rootRho
        #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) +
      richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A
              (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient)) q ≤
        quota
  parent_threshold : ∀ e c q (hq : q.val ≠ 0)
    (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq)),
    let coord := cutParentBranchCoordinate P q hq hnotroot
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)) coord.1 = e →
    c ∈ globalFixedCoordinateAllowed (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) coord →
      (P.numParts : ℝ) ≤ (rootDensity - rootRho) *
        #(richFixedCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
            (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) q)
  total : ∀ e c,
    (2 * quota + P.numParts *
        thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c)) +
        sideLoad (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e)
          (globalFixedFiberOrientation (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R)
              (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
              (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A))
            (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) e) c +
        thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) ≤
      #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c)
  plan_overhead : ∀ e c,
    (((2 * quota + P.numParts *
          thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
              E0 Mb e c)) +
        (1 + thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c)) : ℕ) : ℝ) ≤
      (small : ℝ) + 1 + removalBudget + 1
  component_margin : ∀ e c,
    let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
    (small : ℝ) + rootRho *
        (#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ) + 1 ≤
      (rootDensity - rootRho) *
        ((#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ) -
          (2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c) : ℕ) -
          sideLoad (onlineFiberForest (branchForest P) assign e)
            (globalFixedFiberOrientation (branchForest P) assign
              (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) e)
            c)

/-- Complete synchronized realization from a checked physical-fiber plan and
its remaining scalar inequalities. -/
theorem exists_treeCopy_of_richFixedPhysicalPlan
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity removalBudget : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (plan : PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S cap0 cap1 capb A rootRho rootDensity
        removalBudget)
    (m : ℕ)
    (D : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R miss Q P
      hT rootRho rootDensity removalBudget m)
    (K : RichFixedPhysicalPlanScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity removalBudget
        plan)
    (initialRootImage : Fin P.numParts → Bv) :
    Nonempty (T.Copy G) := by
  let F := richPlannedRootCleaningFactsOfPhysicalFiberGlobalFacts Pcluster
    Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A hT havailable G
      rootRho rootDensity removalBudget H plan m D K.cleaning_root_budget
        K.cleaning_root_link
  apply exists_treeCopy_of_richFixedHostScalarOnline Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A hT G hdisjoint rootRho rootDensity
      H (physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient) F
        initialRootImage
  intro e
  exact richFixedFullFiberEdgeFactsOfPhysicalPlan Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A G rootRho rootDensity
      removalBudget H plan F e K.factor_nonneg K.root_candidate_budget
        (K.parent_threshold e) (K.total e) (K.plan_overhead e)
          (K.component_margin e)

end Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalApplication

#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalApplication.exists_treeCopy_of_richFixedPhysicalPlan
