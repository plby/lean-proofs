/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalRootSidePlan
import ErdosProblems.Erdos547b.Claim615RichExceptionalOnlineForcing

/-!
# Non-result online data from a rich physical root-side plan

This is the mixed threshold/Appendix analogue of the fixed-threshold package.
The side plan is cleaned before the synchronized recursion starts; the local
callback then supplies only plan-certified threshold, Appendix, or fixed-step
source data.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichRootSideOnlineRealization

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootCleaning
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalRootSidePlan
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters

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
variable (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
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
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1 capb)

/-- Scalar facts which turn a reduced-graph root-side plan into the literal
planned root-cleaning certificate. -/
structure RichRootSideCleaningScalarFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb) : Prop where
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
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A D) q ≤ quota
  root_link : ∀ j (hj : j.val ≠ 0)
    (_hroot : P.parent j hj = P.roots (P.parentPart j hj)),
    (P.numParts : ℝ) +
        richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A rootRho
            (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A D) j ≤
      (rootDensity - rootRho) * quota

/-- Construct the literal planned root-cleaning certificate. -/
theorem RichRootSideCleaningScalarFacts.toRootCleaningFacts
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (K : RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H D) :
    RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A D) := by
  exact richPlannedRootCleaningFactsOfRootSidePlan Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A hT havailable G rootRho
    rootDensity H D K.root_large K.endpoint_large K.root_budget K.root_link

/-- Package a cleaned physical side plan and its plan-certified local source
steps as the non-result data consumed by exceptional-family forcing. -/
noncomputable def onlineRealizationDataOfRootSidePlan
    (hT : T.IsTree) (havailable : available ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (Kroot : RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H D)
    (initialRootImage : Fin P.numParts → Bv)
    (edgeRho edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (successor : RichPlannedOnlineSuccessor Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P G S A rootRho
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A D) edgeRho edgeDensity) :
    OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P G S A where
  rootRho := rootRho
  rootDensity := rootDensity
  pairRealization := H
  plan := richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A D
  rootCleaning := Kroot.toRootCleaningFacts Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity H D
  initialRootImage := initialRootImage
  edgeRho := edgeRho
  edgeDensity := edgeDensity
  successor := successor

end Erdos547b.ZhaoClaim615RichRootSideOnlineRealization

#print axioms Erdos547b.ZhaoClaim615RichRootSideOnlineRealization.RichRootSideCleaningScalarFacts.toRootCleaningFacts
#print axioms Erdos547b.ZhaoClaim615RichRootSideOnlineRealization.onlineRealizationDataOfRootSidePlan
