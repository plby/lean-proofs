/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim610Full
import ErdosProblems.Erdos547b.Claim615RichExceptionalOnlinePackages
import ErdosProblems.Erdos547b.Claim615SourceMass

/-!
# Internal source selection for online exceptional packages

Claim 6.10 supplies the balanced selected forest for the unbalanced case;
Claim 6.8 supplies the nontrivial selected forest for Appendix A.  The only
remaining family passed forward is the owner-local online source/host data.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichExceptionalOnlineSelection

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
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim615RichExceptionalOnlinePackages
open Erdos547b.ZhaoClaim615SourceMass
open Erdos547b.ZhaoClaim610Full

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

/-- Construct the unbalanced online package with the balanced source forest
chosen internally by Claim 6.10. -/
theorem exists_thresholdOnlinePackage_of_claim6_10
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .unbalanced count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
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
    {ratio : ℝ} (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hN : 0 < N)
    (hslack : 0 < slack)
    (hbranchSmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hthreshold : ((Fintype.card V - (k + 1) : ℕ) : ℝ) ≤
      (1 - 2 * ratio) *
          ((branchMass P (halfBranches P) : ℝ) - target) -
        2 * P.numParts)
    (gamma epsilon : ℝ)
    (packing : ∀ S : SelectedF0 P (balancedMajorBranches P ratio) target slack,
      PhysicalThresholdPackingFacts
        (P := P) (S := S) (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (gamma := gamma) (epsilon := epsilon))
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (online : ∀ S : SelectedF0 P (balancedMajorBranches P ratio) target slack,
      ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
        (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
        (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
        (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
      Nonempty (OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P G S A)) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P G hT) := by
  obtain ⟨S⟩ := exists_balancedSelectedF0_of_not_extremalCaseOne hn beta
    Ghost hlarge hnotEC1 hnumeric hT hcard horder hnotContained P ratio
      hratio hratioHalf target slack hslack hbranchSmall hthreshold
  exact exists_thresholdOnlinePackage Pcluster Gdegree threshold quota R miss Q
    sourceDensity P E0 Mb S hT hratio (by linarith) hN gamma epsilon
    (packing S) G (online S)

/-- Construct the nonextreme online package with the selected source forest
chosen internally by Claim 6.8. -/
theorem exists_partThreeOnlinePackage_of_claim6_8
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .nonextreme count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
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
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (gamma epsilon : ℝ)
    (packing : ∀ S : SelectedF0 P (nontrivialMajorBranches P) target slack,
      PartThreePackingFacts (P := P) (S := S)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (cap0 := cap0) (gamma := gamma) (epsilon := epsilon))
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (online : ∀ S : SelectedF0 P (nontrivialMajorBranches P) target slack,
      ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
        (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
        (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
      Nonempty (OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P G S A)) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P G hT) := by
  obtain ⟨S⟩ := exists_nontrivialSelectedF0_of_claim6_8 P d hd n target slack
    hcardT horiginalLeaves hhierarchyF hhierarchyA htarget hslack hbranchSmall
  exact exists_partThreeOnlinePackage Pcluster Gdegree threshold quota R miss Q
    sourceDensity P E0 Mb S hT cap0 gamma epsilon (packing S) G (online S)

end Erdos547b.ZhaoClaim615RichExceptionalOnlineSelection

#print axioms Erdos547b.ZhaoClaim615RichExceptionalOnlineSelection.exists_thresholdOnlinePackage_of_claim6_10
#print axioms Erdos547b.ZhaoClaim615RichExceptionalOnlineSelection.exists_partThreeOnlinePackage_of_claim6_8
