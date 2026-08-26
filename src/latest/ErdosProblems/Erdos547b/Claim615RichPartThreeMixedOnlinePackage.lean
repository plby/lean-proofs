/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPartThreeMixedFamilyFacts
import ErdosProblems.Erdos547b.Claim615RichExceptionalOnlineSelection

/-!
# Nonextreme online package from state-independent family facts

Claim 6.8 chooses the selected source forest and the packing theorem chooses
its physical allocation.  The remaining input below consists only of
allocation-independent source facts and allocation-dependent, but
state-independent, root-cleaning and complete-fiber inequalities.  The
synchronized recursive realization is constructed internally.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPartThreeMixedOnlinePackage

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
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
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan
open Erdos547b.ZhaoClaim615RichGlobalRootSidePlan
open Erdos547b.ZhaoClaim615RichRootSideOnlineRealization
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim615RichExceptionalOnlineSelection
open Erdos547b.ZhaoClaim615RichPartThreeMixedOnlineRealization
open Erdos547b.ZhaoClaim615RichPartThreeMixedFamilyFacts
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
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
variable {count cardBound : ℕ}
variable (E0 : SelectedExceptionalEdges Q sourceDensity L eta .nonextreme count)
variable (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ}

/-- State-independent host data for every source forest/allocation which may
be selected by Claim 6.8 and the integral packing step. -/
structure PartThreeMixedOnlineHostFacts
    (hT : T.IsTree)
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (gamma epsilon : ℝ)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ) (hrootRho : 0 ≤ rootRho)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (Fsource : PhysicalPartThreeRootSourceFacts (small := small)
      Q sourceDensity E0 Mb gamma epsilon) : Type (max u v w) where
  root : ∀ S : SelectedF0 P (nontrivialMajorBranches P) target slack,
    ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
    RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R
          miss Q sourceDensity E0 Mb)
  initial : ∀ S : SelectedF0 P (nontrivialMajorBranches P) target slack,
    ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
    Fin P.numParts → Bv
  fiber : ∀ S : SelectedF0 P (nontrivialMajorBranches P) target slack,
    ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
    PartThreeFamilyFullFiberFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A hT
      (fun j hj ↦ (mem_nontrivialMajorBranches P j).mp hj |>.1)
      G rootRho rootDensity hrootRho H
      (physicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S gamma
        epsilon A Fsource)
      (root S A)

/-- Claim 6.8, physical packing, and state-independent mixed family facts
construct the full nonextreme online package internally. -/
theorem exists_partThreeOnlinePackage_of_claim6_8_mixedFamilyFacts
    (hT : T.IsTree)
    (d : ℝ) (hd : 0 ≤ d) (n : ℕ)
    (hcardT : Fintype.card V = n + 1)
    (horiginalLeaves :
      (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
        11 * Real.sqrt d * n)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * n)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * n)
    (htarget : (target : ℝ) < (n : ℝ) / 2 - 12 * Real.sqrt d * n)
    (hslack : 0 < slack)
    (hbranchSmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (gamma epsilon : ℝ)
    (packing : ∀ S : SelectedF0 P (nontrivialMajorBranches P) target slack,
      PartThreePackingFacts (P := P) (S := S)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (cap0 := cap0) (gamma := gamma) (epsilon := epsilon))
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ) (hrootRho : 0 ≤ rootRho)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (Fsource : PhysicalPartThreeRootSourceFacts (small := small)
      Q sourceDensity E0 Mb gamma epsilon)
    (K : PartThreeMixedOnlineHostFacts (target := target) (slack := slack)
      Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P hT cap0
      gamma epsilon G rootRho rootDensity hrootRho H Fsource) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P G hT) := by
  apply exists_partThreeOnlinePackage_of_claim6_8 Pcluster Gdegree threshold
    quota R miss Q sourceDensity P E0 Mb hT d hd n hcardT horiginalLeaves
    hhierarchyF hhierarchyA htarget hslack hbranchSmall cap0 gamma epsilon
    packing G
  intro S A
  let D := physicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S gamma
    epsilon A Fsource
  let Kroot := K.root S A
  exact ⟨onlineRealizationDataOfPartThreeFamilyFullFiberFacts Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A hT
    (fun j hj ↦ (mem_nontrivialMajorBranches P j).mp hj |>.1)
    hdisjoint
    G rootRho rootDensity hrootRho H D Kroot (K.initial S A)
    (K.fiber S A)⟩

end Erdos547b.ZhaoClaim615RichPartThreeMixedOnlinePackage

#print axioms Erdos547b.ZhaoClaim615RichPartThreeMixedOnlinePackage.exists_partThreeOnlinePackage_of_claim6_8_mixedFamilyFacts
