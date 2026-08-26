/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalThresholdRootPlan
import ErdosProblems.Erdos547b.Claim615RichGlobalFixedPhysicalPlan

/-!
# Online host facts from complete-fiber threshold loads

This is the dynamic replacement for the old static physical-fiber capacity
certificate.  A source threshold plan supplies only a complete-fiber side
load bound.  The scalar hypotheses below compare that one bound with the
literal cleaned host pair, and therefore feed the synchronized owner-by-owner
online recursion without charging the threshold budget once per owner.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalThresholdHostFacts

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientation
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootCleaning
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichGlobalFixedPlan
open Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts
open Erdos547b.ZhaoClaim615RichGlobalFixedPhysicalPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.RegularPair

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
variable {target slack : ℕ} {ratio : ℝ}
variable (S : SelectedF0 P (balancedMajorBranches P ratio) target slack)
variable {gamma epsilon : ℝ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
    (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
    (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))

/-- Literal scalar inequalities for one physical threshold edge.  The load
appearing here is the source plan's single complete-fiber high budget. -/
structure RichThresholdFullFiberEdgeFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalThresholdRootPlan Q sourceDensity E0 Mb P S A)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (physicalFiberOrient Q sourceDensity E0 Mb P S A
              D.toRootOrientationPlan.orient)))
    (e : PhysicalIndex Q sourceDensity E0 Mb) : Prop where
  factor_nonneg : 0 ≤ rootDensity - rootRho
  root_candidate_budget : ∀ q,
    thresholdReserve rootRho
        #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) +
      richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A
              (physicalFiberOrient Q sourceDensity E0 Mb P S A
                D.toRootOrientationPlan.orient)) q ≤ quota
  parent_threshold : ∀ c q (hq : q.val ≠ 0)
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
      (physicalFiberOrient Q sourceDensity E0 Mb P S A
        D.toRootOrientationPlan.orient) coord →
      (P.numParts : ℝ) ≤ (rootDensity - rootRho) *
        #(richFixedCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho
            (physicalFiberOrient Q sourceDensity E0 Mb P S A
              D.toRootOrientationPlan.orient) q)
  total : ∀ c,
    (2 * quota + P.numParts *
        thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c)) +
        (D.fiber e).loadBound +
        thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) ≤
      #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c)
  eligible_margin : ∀ c,
    (((2 * quota + P.numParts *
          thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
              E0 Mb e c)) +
        (D.fiber e).loadBound +
        (1 + thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c)) : ℕ) : ℝ) ≤
      (rootDensity - rootRho) *
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c)
  component_margin : ∀ c,
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
          (D.fiber e).loadBound)

/-- Convert the source high-budget bound into the exact full-fiber facts used
by the synchronized online recursion. -/
def richFixedFullFiberEdgeFactsOfThresholdRootPlan
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalThresholdRootPlan Q sourceDensity E0 Mb P S A)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (physicalFiberOrient Q sourceDensity E0 Mb P S A
              D.toRootOrientationPlan.orient)))
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (K : RichThresholdFullFiberEdgeFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H D F e) :
    RichFixedFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalFiberOrient Q sourceDensity E0 Mb P S A
          D.toRootOrientationPlan.orient) F e := by
  refine {
    factor_nonneg := K.factor_nonneg
    root_candidate_budget := K.root_candidate_budget
    parent_threshold := K.parent_threshold
    total := ?_
    eligible_margin := ?_
    component_margin := ?_
  }
  · intro c
    have hlocal := (D.fiber e).load_le c
    have heq := sideLoad_globalFixed_physicalFiberOrient Pcluster Gdegree
      threshold quota R miss Q sourceDensity E0 Mb P S A
        D.toRootOrientationPlan.orient e c
    rw [heq]
    change
      (2 * quota + P.numParts *
          thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
              E0 Mb e c)) +
        sideLoad
          (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A) e)
          (D.fiber e).orient c +
        thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) ≤
        #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
          Mb e c)
    have htotal := K.total c
    omega
  · intro c
    dsimp only
    have hlocal := (D.fiber e).load_le c
    have heq := sideLoad_globalFixed_physicalFiberOrient Pcluster Gdegree
      threshold quota R miss Q sourceDensity E0 Mb P S A
        D.toRootOrientationPlan.orient e c
    rw [heq]
    have hnat :
        (2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c)) +
          sideLoad
            (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R) (miss := miss)
              (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
              (P := P) (S := S) (A := A) e)
            (D.fiber e).orient c +
          (1 + thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb e c)) ≤
        (2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c)) +
          (D.fiber e).loadBound +
          (1 + thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb e c)) := by
      omega
    have hreal :
        (((2 * quota + P.numParts *
              thresholdReserve rootRho
                #(richWhole Pcluster Gdegree threshold quota R miss Q
                  sourceDensity E0 Mb e c)) +
            sideLoad
              (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
                (threshold := threshold) (quota := quota) (R := R)
                (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
                (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A) e)
              (D.fiber e).orient c +
            (1 + thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c)) : ℕ) : ℝ) ≤
          (((2 * quota + P.numParts *
              thresholdReserve rootRho
                #(richWhole Pcluster Gdegree threshold quota R miss Q
                  sourceDensity E0 Mb e c)) +
            (D.fiber e).loadBound +
            (1 + thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c)) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans (K.eligible_margin c)
  · intro c
    dsimp only
    have hlocal := (D.fiber e).load_le c
    have heq := sideLoad_globalFixed_physicalFiberOrient Pcluster Gdegree
      threshold quota R miss Q sourceDensity E0 Mb P S A
        D.toRootOrientationPlan.orient e c
    rw [heq]
    have hloadReal :
        (sideLoad
          (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A) e)
          (D.fiber e).orient c : ℝ) ≤ (D.fiber e).loadBound := by
      exact_mod_cast hlocal
    have hinner :
        ((#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) : ℝ) -
          (2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c) : ℕ) -
          (D.fiber e).loadBound) ≤
        ((#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) : ℝ) -
          (2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c) : ℕ) -
          sideLoad
            (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R) (miss := miss)
              (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
              (P := P) (S := S) (A := A) e)
            (D.fiber e).orient c) := by
      norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
        Nat.cast_card]
      linarith
    exact (K.component_margin c).trans
      (mul_le_mul_of_nonneg_left hinner K.factor_nonneg)

end Erdos547b.ZhaoClaim615RichGlobalThresholdHostFacts

#print axioms Erdos547b.ZhaoClaim615RichGlobalThresholdHostFacts.richFixedFullFiberEdgeFactsOfThresholdRootPlan
