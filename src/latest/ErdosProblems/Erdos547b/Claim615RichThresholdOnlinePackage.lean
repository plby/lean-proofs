/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichThresholdOnlineRealization
import ErdosProblems.Erdos547b.Claim615RichExceptionalOnlineSelection

/-!
# Unbalanced online package from complete-fiber scalar facts

Claim 6.10 chooses the balanced selected forest, the integral packing theorem
chooses the physical allocation, and the threshold online realizer constructs
the synchronized recursion.  No embedding, copy, continuation, containment,
or recursive-state datum is an input here.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichThresholdOnlinePackage

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
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication
open Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan
open Erdos547b.ZhaoClaim615RichGlobalThresholdApplication
open Erdos547b.ZhaoClaim615RichGlobalThresholdHostFacts
open Erdos547b.ZhaoClaim615RichThresholdOnlineRealization
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim615RichExceptionalOnlineSelection
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
variable (E0 : SelectedExceptionalEdges Q sourceDensity L eta .unbalanced count)
variable (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ} {ratio gamma epsilon : ℝ}

/-- State-independent host facts for every balanced source selection and its
physical allocation. -/
structure ThresholdOnlineHostFacts
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (Fsource : PhysicalThresholdSourceFacts (small := small) (ratio := ratio)
      Q sourceDensity E0 Mb gamma epsilon) : Type (max u v w) where
  root : ∀ S : SelectedF0 P (balancedMajorBranches P ratio) target slack,
    ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
    RichThresholdRootCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
      (physicalPartTwoPartOneRootPlan Q sourceDensity E0 Mb P S gamma epsilon A
        (fun j hj ↦ (mem_balancedMajorBranches P ratio j).mp hj |>.1) Fsource)
  initial : ∀ S : SelectedF0 P (balancedMajorBranches P ratio) target slack,
    ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
    Fin P.numParts → Bv
  edge : ∀ S : SelectedF0 P (balancedMajorBranches P ratio) target slack,
    ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
    ∀ e,
    let D := physicalPartTwoPartOneRootPlan Q sourceDensity E0 Mb P S gamma
      epsilon A (fun j hj ↦ (mem_balancedMajorBranches P ratio j).mp hj |>.1)
      Fsource
    RichThresholdFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H D
      ((root S A).toRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A hT
        (fun j hj ↦ (mem_balancedMajorBranches P ratio j).mp hj |>.1)
        G rootRho rootDensity H D) e

/-- Claim 6.10, physical packing, and complete-fiber threshold facts construct
the unbalanced online package internally. -/
theorem exists_thresholdOnlinePackage_of_claim6_10_fullFiberFacts
    (hT : T.IsTree)
    {n k : ℕ} (hn : 2 ≤ n) (beta : ℚ)
    (Ghost : SimpleGraph (Fin (2 * n - 2))) [DecidableRel Ghost.Adj]
    (hlarge : n - 1 ≤
      #(Finset.univ.filter fun x ↦ n - 1 ≤ Ghost.degree x))
    (hnotEC1 : ¬ZhaoExtremalCaseOne beta Ghost)
    (hnumeric : (2 * k * ((n - 1 : ℕ) : ℚ)) ≤
      beta * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ))
    (hcard : 3 ≤ Fintype.card V)
    (horder : Fintype.card V - 1 ≤ n - 1)
    (hnotContained : ¬T.IsContained Ghost)
    (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hN : 0 < N)
    (hslack : 0 < slack)
    (hbranchSmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hthreshold : ((Fintype.card V - (k + 1) : ℕ) : ℝ) ≤
      (1 - 2 * ratio) *
          ((branchMass P (halfBranches P) : ℝ) - target) -
        2 * P.numParts)
    (packing : ∀ S : SelectedF0 P (balancedMajorBranches P ratio) target slack,
      PhysicalThresholdPackingFacts
        (P := P) (S := S) (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (gamma := gamma) (epsilon := epsilon))
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (Fsource : PhysicalThresholdSourceFacts (small := small) (ratio := ratio)
      Q sourceDensity E0 Mb gamma epsilon)
    (Khost : ThresholdOnlineHostFacts (target := target) (slack := slack)
      Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P hT G
      rootRho rootDensity H Fsource) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P G hT) := by
  apply exists_thresholdOnlinePackage_of_claim6_10 Pcluster Gdegree threshold
    quota R miss Q sourceDensity P E0 Mb hT hn beta Ghost hlarge hnotEC1
    hnumeric hcard horder hnotContained hratio hratioHalf hN hslack hbranchSmall
    hthreshold gamma epsilon packing G
  intro S A
  let havailable : balancedMajorBranches P ratio ⊆ halfBranches P :=
    fun j hj ↦ (mem_balancedMajorBranches P ratio j).mp hj |>.1
  let D := physicalPartTwoPartOneRootPlan Q sourceDensity E0 Mb P S gamma
    epsilon A havailable Fsource
  let Kroot := Khost.root S A
  exact ⟨onlineRealizationDataOfThresholdRootPlan Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A hT havailable hdisjoint G rootRho
    rootDensity H D Kroot (Khost.initial S A) (Khost.edge S A)⟩

end Erdos547b.ZhaoClaim615RichThresholdOnlinePackage

#print axioms Erdos547b.ZhaoClaim615RichThresholdOnlinePackage.exists_thresholdOnlinePackage_of_claim6_10_fullFiberFacts
