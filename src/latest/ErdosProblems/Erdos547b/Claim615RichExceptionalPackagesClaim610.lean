/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim610Full
import ErdosProblems.Erdos547b.Claim615RichExceptionalPackages

/-!
# Claim 6.10 specialization of the unbalanced exceptional package

The balanced source forest required by Lemma 5.4(2) is constructed here from
the checked Claim 6.10 theorem.  No selected source forest is an input.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichExceptionalPackagesClaim610

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
open Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication
open Erdos547b.ZhaoClaim615RichExceptionalForcing
open Erdos547b.ZhaoClaim615RichExceptionalPackages
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

/-- Construct the unbalanced physical package with its balanced source
selection obtained from Claim 6.10. -/
theorem exists_thresholdPackage_of_claim6_10
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 .unbalanced count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (hT : T.IsTree) (hsmall : 1 ≤ small)
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
    {ratio : ℝ} (halpha0 : 0 ≤ ratio) (halphaHalf : ratio ≤ 1 / 2)
    (hslack : 0 < slack)
    (hbranchSmall : ∀ j, (branchForest P).branches.size j ≤ slack)
    (hthreshold : ((Fintype.card V - (k + 1) : ℕ) : ℝ) ≤
      (1 - 2 * ratio) *
          ((branchMass P (halfBranches P) : ℝ) - target) -
        2 * P.numParts)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (havailable : balancedMajorBranches P ratio ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Hpair : Erdos547b.ZhaoClaim615RichCoordinatePairFacts.ReducedPairRealization
      Pcluster R G rho pairDensity)
    (F : PhysicalThresholdFacts (small := small) (ratio := ratio)
      Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb rho
        pairDensity removalBudget gamma epsilon)
    (packing : ∀ S : SelectedF0 P (balancedMajorBranches P ratio) target slack,
      PhysicalThresholdPackingFacts
        (P := P) (S := S) (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (gamma := gamma) (epsilon := epsilon))
    (m : ℕ)
    (H : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R miss Q P
      hT rho pairDensity removalBudget m) :
    Nonempty (FixedPhysicalApplicationPackage Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb P G hT) := by
  obtain ⟨S⟩ := exists_balancedSelectedF0_of_not_extremalCaseOne hn beta
    Ghost hlarge hnotEC1 hnumeric hT hcard horder hnotContained P ratio
      halpha0 halphaHalf target slack hslack hbranchSmall hthreshold
  exact exists_thresholdPackage Pcluster Gdegree threshold quota R miss Q
    sourceDensity P E0 Mb S hT hsmall rho pairDensity removalBudget gamma
      epsilon havailable G Hpair F (packing S) m H

end Erdos547b.ZhaoClaim615RichExceptionalPackagesClaim610

#print axioms Erdos547b.ZhaoClaim615RichExceptionalPackagesClaim610.exists_thresholdPackage_of_claim6_10
