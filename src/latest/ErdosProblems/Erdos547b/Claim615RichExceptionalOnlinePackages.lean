/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichExceptionalOnlineForcing
import ErdosProblems.Erdos547b.Claim615RichPhysicalThresholdApplication
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartThreeApplication

/-!
# Source allocation for exceptional-family online packages

These are the source-faithful replacements for the two constructors in
`Claim615RichExceptionalPackages`.  They retain the valid integral packing
argument, but hand the chosen allocation to the synchronized owner-local
backend instead of requiring the false static endpoint-capacity plan.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichExceptionalOnlinePackages

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
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing

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

/-- Choose the Part-2/Part-1 source allocation and retain only the valid
owner-local online host data. -/
theorem exists_thresholdOnlinePackage
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .unbalanced count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    {ratio : ℝ}
    (S : SelectedF0 P (balancedMajorBranches P ratio) target slack)
    (hT : T.IsTree)
    (hratio : 0 ≤ ratio) (hratioOne : ratio < 1) (hN : 0 < N)
    (gamma epsilon : ℝ)
    (packing : PhysicalThresholdPackingFacts
      (P := P) (S := S) (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (gamma := gamma) (epsilon := epsilon))
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (online : ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
        (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
        (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
        (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
      Nonempty (OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P G S A)) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P G hT) := by
  obtain ⟨A⟩ := exists_sourceAllocation_partTwo_partOne_of_sourceDegrees
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (ratio := ratio) (S := S) gamma epsilon packing.count_pos
    packing.targetB_pos packing.A_edge_nonneg packing.remaining_A_pos
    hratio hratioOne hN.le
    packing.exceptional_budget packing.remaining_budget packing.reserved_budget
  obtain ⟨D⟩ := online A
  exact ⟨onlinePhysicalApplicationPackageOfAllocation Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P G S A D⟩

/-- Choose the Appendix-A/Part-1 source allocation and retain only the valid
owner-local online host data. -/
theorem exists_partThreeOnlinePackage
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .nonextreme count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (S : SelectedF0 P (nontrivialMajorBranches P) target slack)
    (hT : T.IsTree)
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (gamma epsilon : ℝ)
    (packing : PartThreePackingFacts (P := P) (S := S)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (cap0 := cap0) (gamma := gamma) (epsilon := epsilon))
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (online : ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
        cap0
        (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
        (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
      Nonempty (OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P G S A)) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P G hT) := by
  obtain ⟨A⟩ := exists_sourceAllocation_partOne_physical
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) gamma epsilon cap0 packing.count_pos
    packing.targetB_pos packing.A_edge_nonneg packing.remaining_A_pos
    packing.exceptional_budget packing.remaining_budget packing.reserved_budget
  obtain ⟨D⟩ := online A
  exact ⟨onlinePhysicalApplicationPackageOfAllocation Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P G S A D⟩

end Erdos547b.ZhaoClaim615RichExceptionalOnlinePackages

#print axioms Erdos547b.ZhaoClaim615RichExceptionalOnlinePackages.exists_thresholdOnlinePackage
#print axioms Erdos547b.ZhaoClaim615RichExceptionalOnlinePackages.exists_partThreeOnlinePackage
