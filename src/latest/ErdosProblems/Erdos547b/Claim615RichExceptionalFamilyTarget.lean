/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichExceptionalOnlineSelection
import ErdosProblems.Erdos547b.Claim615SourceFamilyTarget

/-!
# Family-dependent exceptional online packages

This module threads Zhao's literal threshold

`⌈deg(A,E₀) + η³ n⌉`

through the two source selectors and the synchronized online realization.
In particular, `E₀` is chosen before the target, as in the proof of
Lemma 6.15.  The resulting object is still the concrete
`OnlinePhysicalApplicationPackage`, whose endpoint is a copy of the literal
input tree.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichExceptionalFamilyTarget

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
open Erdos547b.ZhaoClaim615SourceFamilyTarget
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim615RichExceptionalOnlineSelection

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
variable {slack : ℕ}

/-- Unbalanced exceptional package with the target computed after `E₀`.
Claim 6.10 supplies the selected balanced forest; all later source allocation
and host realization is performed by the checked online constructor. -/
theorem exists_thresholdOnlinePackage_familyTarget
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .unbalanced count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (hT : T.IsTree)
    (exceptionalDegree nReal : ℝ)
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
          ((branchMass P (halfBranches P) : ℝ) -
            exceptionalForestTarget exceptionalDegree eta0 nReal) -
        2 * P.numParts)
    (gamma epsilon : ℝ)
    (packing : ∀ S : SelectedF0 P (balancedMajorBranches P ratio)
        (exceptionalForestTarget exceptionalDegree eta0 nReal) slack,
      PhysicalThresholdPackingFacts
        (P := P) (S := S) (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (gamma := gamma) (epsilon := epsilon))
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (online : ∀ S : SelectedF0 P (balancedMajorBranches P ratio)
        (exceptionalForestTarget exceptionalDegree eta0 nReal) slack,
      ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
        (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
        (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
        (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
      Nonempty (OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P G S A)) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P G hT) := by
  exact exists_thresholdOnlinePackage_of_claim6_10 Pcluster Gdegree threshold
    quota R miss Q sourceDensity P E0 Mb hT hn beta Ghost hlarge hnotEC1
    hnumeric hcard horder hnotContained hratio hratioHalf hN hslack
    hbranchSmall hthreshold gamma epsilon packing G online

/-- Nonextreme exceptional package with the target computed after `E₀`.
The one-unit ceiling loss is exposed in `hroom`; Claim 6.8 then supplies the
selected nontrivial forest, and the checked Part-3 online constructor embeds
the full tree. -/
theorem exists_partThreeOnlinePackage_familyTarget
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .nonextreme count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (hT : T.IsTree)
    (exceptionalDegree nReal : ℝ)
    (hfamilyNonneg : 0 ≤ exceptionalDegree + eta0 ^ 3 * nReal)
    (d : ℝ) (hd : 0 ≤ d) (n : ℕ)
    (hcardT : Fintype.card V = n + 1)
    (horiginalLeaves :
      (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
        11 * Real.sqrt d * n)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * n)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * n)
    (hroom : exceptionalDegree + eta0 ^ 3 * nReal + 1 <
      (n : ℝ) / 2 - 12 * Real.sqrt d * n)
    (hslack : 0 < slack)
    (hbranchSmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (gamma epsilon : ℝ)
    (packing : ∀ S : SelectedF0 P (nontrivialMajorBranches P)
        (exceptionalForestTarget exceptionalDegree eta0 nReal) slack,
      PartThreePackingFacts (P := P) (S := S)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (cap0 := cap0) (gamma := gamma) (epsilon := epsilon))
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (online : ∀ S : SelectedF0 P (nontrivialMajorBranches P)
        (exceptionalForestTarget exceptionalDegree eta0 nReal) slack,
      ∀ A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
        (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
        (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon),
      Nonempty (OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P G S A)) :
    Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P G hT) := by
  have htarget :
      (exceptionalForestTarget exceptionalDegree eta0 nReal : ℝ) <
        (n : ℝ) / 2 - 12 * Real.sqrt d * n :=
    (exceptionalForestTarget_lt_add_one hfamilyNonneg).trans hroom
  exact exists_partThreeOnlinePackage_of_claim6_8 Pcluster Gdegree threshold
    quota R miss Q sourceDensity P E0 Mb hT d hd n hcardT horiginalLeaves
    hhierarchyF hhierarchyA htarget hslack hbranchSmall cap0 gamma epsilon
    packing G online

end Erdos547b.ZhaoClaim615RichExceptionalFamilyTarget

#print axioms Erdos547b.ZhaoClaim615RichExceptionalFamilyTarget.exists_thresholdOnlinePackage_familyTarget
#print axioms Erdos547b.ZhaoClaim615RichExceptionalFamilyTarget.exists_partThreeOnlinePackage_familyTarget
