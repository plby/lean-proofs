/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalThresholdHostFacts
import ErdosProblems.Erdos547b.Claim615RichGlobalRootOrientationPlan

/-!
# Complete synchronized threshold realization for Claim 6.15

This module composes the source-only complete-fiber threshold plan, planned
root cleaning, and the dynamic fixed-orientation owner recursion.  The public
endpoint constructs an actual tree copy; no orientation, embedding, copy, or
continuation is an input.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalThresholdApplication

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
open Erdos547b.ZhaoClaim615RichGlobalFixedPlan
open Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts
open Erdos547b.ZhaoClaim615RichGlobalRootOrientationPlan
open Erdos547b.ZhaoClaim615RichGlobalThresholdHostFacts
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
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

/-- Scalar root-cleaning hypotheses for the source-only threshold plan. -/
structure RichThresholdRootCleaningScalarFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalThresholdRootPlan Q sourceDensity E0 Mb P S A) : Prop where
  root_large : ∀ side,
    rootRho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q side) ≤
      quota
  endpoint_large : ∀ e c,
    rootRho * #(richWhole Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb e c) ≤
      #(richEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c)
  root_budget : ∀ q,
    P.numParts + richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A rootRho
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (physicalFiberOrient Q sourceDensity E0 Mb P S A
              D.toRootOrientationPlan.orient)) q ≤ quota
  root_link : ∀ j (hj : j.val ≠ 0)
    (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
    (P.numParts : ℝ) +
        richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A rootRho
            (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A
                (physicalFiberOrient Q sourceDensity E0 Mb P S A
                  D.toRootOrientationPlan.orient)) j ≤
      (rootDensity - rootRho) * quota

/-- Construct the planned root-cleaning certificate for the literal pasted
threshold orientation. -/
theorem RichThresholdRootCleaningScalarFacts.toRootCleaningFacts
    (hT : T.IsTree)
    (havailable : balancedMajorBranches P ratio ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalThresholdRootPlan Q sourceDensity E0 Mb P S A)
    (K : RichThresholdRootCleaningScalarFacts Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H D) :
    RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A
            (physicalFiberOrient Q sourceDensity E0 Mb P S A
              D.toRootOrientationPlan.orient)) := by
  exact richPlannedRootCleaningFactsOfRootOrientation Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A hT havailable G
    rootRho rootDensity H D.toRootOrientationPlan K.root_large K.endpoint_large
    K.root_budget K.root_link

/-- Actual tree-copy endpoint for the unbalanced Part-2/Part-1 orientation.
Every local online step is built internally from the stored complete-fiber
threshold load and the literal host inequalities. -/
theorem exists_treeCopy_of_richThresholdOnline
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
    Nonempty (T.Copy G) := by
  let F := Kroot.toRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity H D
  apply exists_treeCopy_of_richFixedHostScalarOnline Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A hT G hdisjoint rootRho rootDensity
      H (physicalFiberOrient Q sourceDensity E0 Mb P S A
        D.toRootOrientationPlan.orient) F initialRootImage
  intro e
  exact richFixedFullFiberEdgeFactsOfThresholdRootPlan Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
    D F e (Kedge e)

end Erdos547b.ZhaoClaim615RichGlobalThresholdApplication

#print axioms Erdos547b.ZhaoClaim615RichGlobalThresholdApplication.RichThresholdRootCleaningScalarFacts.toRootCleaningFacts
#print axioms Erdos547b.ZhaoClaim615RichGlobalThresholdApplication.exists_treeCopy_of_richThresholdOnline
