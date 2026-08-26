/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichExceptionalForcing
import ErdosProblems.Erdos547b.Claim615RichPhysicalThresholdApplication
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartThreeApplication
import ErdosProblems.Erdos547b.Claim615SourceMass

/-!
# Source constructors for the two exceptional physical packages

The two theorems below stop immediately before the common cut-aware
realization.  They choose the finite source allocation and construct the
literal physical-fiber plan from Zhao Lemma 5.4(2), respectively Appendix
A.2, returning the non-result package consumed by the exceptional-family
contrapositive.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichExceptionalPackages

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
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
open Erdos547b.ZhaoClaim615RichPhysicalFiberApplication
open Erdos547b.ZhaoClaim615RichPhysicalFiberScalarApplication
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalPartThree
open Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication
open Erdos547b.ZhaoClaim615RichExceptionalForcing
open Erdos547b.ZhaoClaim615SourceMass

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

variable {L : Finset (EvenPadding I)} {eta0 N targetB cap : ℝ}
variable {count cardBound : ℕ}

variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ}

/-- Construct the common physical package in the unbalanced case from the
checked aggregate source-degree inequalities. -/
theorem exists_thresholdPackage
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .unbalanced count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    {ratio : ℝ}
    (S : SelectedF0 P (balancedMajorBranches P ratio) target slack)
    (hT : T.IsTree) (hsmall : 1 ≤ small)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (havailable : balancedMajorBranches P ratio ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Hpair : Erdos547b.ZhaoClaim615RichCoordinatePairFacts.ReducedPairRealization
      Pcluster R G rho pairDensity)
    (F : PhysicalThresholdFacts (small := small) (ratio := ratio)
      Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb rho
        pairDensity removalBudget gamma epsilon)
    (packing : PhysicalThresholdPackingFacts
      (P := P) (S := S) (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (gamma := gamma) (epsilon := epsilon))
    (m : ℕ)
    (H : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R miss Q P
      hT rho pairDensity removalBudget m) :
    Nonempty (FixedPhysicalApplicationPackage Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P G hT) := by
  have hratio_lt_one : ratio < 1 := by linarith [F.ratio_le_half]
  obtain ⟨A⟩ := exists_sourceAllocation_partTwo_partOne_of_sourceDegrees
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (ratio := ratio) (S := S) gamma epsilon packing.count_pos
    packing.targetB_pos packing.A_edge_nonneg packing.remaining_A_pos
    F.ratio_nonneg hratio_lt_one F.N_pos.le packing.exceptional_budget
    packing.remaining_budget packing.reserved_budget
  let plan := physicalPartTwoPartOnePlan Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S rho pairDensity removalBudget gamma epsilon A
      havailable F
  exact ⟨{
    available := balancedMajorBranches P ratio
    target := target
    slack := slack
    selected := S
    cap0 := exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N
    cap1 := remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon
    capb := reservedPartOneCapacity Q sourceDensity Mb gamma epsilon
    allocation := A
    small_pos := hsmall
    available_half := havailable
    rootRho := rho
    rootDensity := pairDensity
    removalBudget := removalBudget
    pairRealization := Hpair
    plan := plan
    commonCard := m
    globalFacts := H
  }⟩

/-- Construct the common physical package in the nonextreme case from the
checked Appendix-A and ordinary Part-1 source data. -/
theorem exists_partThreePackage
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .nonextreme count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (S : SelectedF0 P (nontrivialMajorBranches P) target slack)
    (hT : T.IsTree) (hsmall : 1 ≤ small)
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (packing : PartThreePackingFacts (P := P) (S := S)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (cap0 := cap0) (gamma := gamma) (epsilon := epsilon))
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Hpair : Erdos547b.ZhaoClaim615RichCoordinatePairFacts.ReducedPairRealization
      Pcluster R G rho pairDensity)
    (F : OrdinaryPartOneFacts (small := small) Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb rho pairDensity removalBudget gamma epsilon)
    (F0 : ∀ (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
        (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
        (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon)),
      ∀ e : K0 Q sourceDensity E0,
        Erdos547b.ZhaoClaim615RichPhysicalPartThree.ExceptionalPartThreeFacts
          Q sourceDensity E0 Mb P S A rho pairDensity removalBudget gamma
            epsilon e)
    (m : ℕ)
    (H : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R miss Q P
      hT rho pairDensity removalBudget m) :
    Nonempty (FixedPhysicalApplicationPackage Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P G hT) := by
  obtain ⟨A⟩ := exists_sourceAllocation_partOne_physical
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) gamma epsilon cap0 packing.count_pos
    packing.targetB_pos packing.A_edge_nonneg packing.remaining_A_pos
    packing.exceptional_budget packing.remaining_budget packing.reserved_budget
  let plan := physicalPartThreePartOnePlan Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S rho pairDensity removalBudget gamma epsilon
    A F (F0 A)
  exact ⟨{
    available := nontrivialMajorBranches P
    target := target
    slack := slack
    selected := S
    cap0 := cap0
    cap1 := remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon
    capb := reservedPartOneCapacity Q sourceDensity Mb gamma epsilon
    allocation := A
    small_pos := hsmall
    available_half := fun j hj ↦ (mem_nontrivialMajorBranches P j).mp hj |>.1
    rootRho := rho
    rootDensity := pairDensity
    removalBudget := removalBudget
    pairRealization := Hpair
    plan := plan
    commonCard := m
    globalFacts := H
  }⟩

/-- The nonextreme package with the finite source selection constructed
internally from the already proved Claim 6.8 lower bound.  All remaining
inputs are physical regular-pair or scalar facts; no selected subforest is an
input. -/
theorem exists_partThreePackage_of_claim6_8
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .nonextreme count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (hT : T.IsTree) (hsmall : 1 ≤ small)
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
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (packing : ∀ S : SelectedF0 P (nontrivialMajorBranches P) target slack,
      PartThreePackingFacts (P := P) (S := S)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (cap0 := cap0) (gamma := gamma) (epsilon := epsilon))
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Hpair : Erdos547b.ZhaoClaim615RichCoordinatePairFacts.ReducedPairRealization
      Pcluster R G rho pairDensity)
    (F : OrdinaryPartOneFacts (small := small) Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb rho pairDensity removalBudget gamma epsilon)
    (F0 : ∀ (S : SelectedF0 P (nontrivialMajorBranches P) target slack),
      ∀ (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
        (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
        (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon)),
      ∀ e : K0 Q sourceDensity E0,
        Erdos547b.ZhaoClaim615RichPhysicalPartThree.ExceptionalPartThreeFacts
          Q sourceDensity E0 Mb P S A rho pairDensity removalBudget gamma
            epsilon e)
    (m : ℕ)
    (H : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R miss Q P
      hT rho pairDensity removalBudget m) :
    Nonempty (FixedPhysicalApplicationPackage Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P G hT) := by
  obtain ⟨S⟩ := exists_nontrivialSelectedF0_of_claim6_8 P d hd n target slack
    hcardT horiginalLeaves hhierarchyF hhierarchyA htarget hslack hbranchSmall
  exact exists_partThreePackage Pcluster Gdegree threshold quota R miss Q
    sourceDensity P E0 Mb S hT hsmall cap0 rho pairDensity removalBudget gamma
    epsilon (packing S) G Hpair F (F0 S) m H

end Erdos547b.ZhaoClaim615RichExceptionalPackages

#print axioms Erdos547b.ZhaoClaim615RichExceptionalPackages.exists_thresholdPackage
#print axioms Erdos547b.ZhaoClaim615RichExceptionalPackages.exists_partThreePackage
#print axioms Erdos547b.ZhaoClaim615RichExceptionalPackages.exists_partThreePackage_of_claim6_8
