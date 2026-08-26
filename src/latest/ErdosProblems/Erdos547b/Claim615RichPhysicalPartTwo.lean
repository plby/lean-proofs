/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartOne

/-!
# Source-faithful Part-2 capacities on exceptional Claim-6.15 edges

The unbalanced exceptional family uses Zhao Lemma 5.4(2).  Its capacity is
rounded down edge by edge; the extra gap term therefore remains attached to
the physical edge on which it is actually available.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalPartTwo

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
open Erdos547b.ZhaoClaim615RichPhysicalFiberMass
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable {Pcluster : ClusterAssignment Bv I}
variable {Gdegree : SimpleGraph Bv} [DecidableRel Gdegree.Adj]
variable {threshold quota : ℕ} {R : SimpleGraph I} [DecidableRel R.Adj]
variable {miss : ℕ}
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

/-- High endpoint selected by the unbalanced exceptional row. -/
def exceptionalHighSide (e : K0 Q sourceDensity E0) : Fin 2 :=
  rootSide0 Q sourceDensity E0 e

/-- The opposite, low-density endpoint. -/
def exceptionalLowSide (e : K0 Q sourceDensity E0) : Fin 2 :=
  otherSide (exceptionalHighSide Q sourceDensity E0 e)

def exceptionalLowDensity (e : K0 Q sourceDensity E0) : ℝ :=
  rawDensityA Q sourceDensity (edge0 Q sourceDensity E0 e)
    (exceptionalLowSide Q sourceDensity E0 e)

def exceptionalHighDensity (e : K0 Q sourceDensity E0) : ℝ :=
  rawDensityA Q sourceDensity (edge0 Q sourceDensity E0 e)
    (exceptionalHighSide Q sourceDensity E0 e)

/-- Literal Zhao-Part-2 real capacity on one exceptional edge. -/
def exceptionalPartTwoTarget (ratio gamma epsilon N : ℝ)
    (e : K0 Q sourceDensity E0) : ℝ :=
  (exceptionalLowDensity Q sourceDensity E0 e +
      exceptionalHighDensity Q sourceDensity E0 e - 2 * gamma -
      3 * epsilon) * N +
    ratio / (1 - ratio) *
      (exceptionalHighDensity Q sourceDensity E0 e -
        exceptionalLowDensity Q sourceDensity E0 e) * N

/-- Downward-rounded integral Part-2 capacity. -/
def exceptionalPartTwoCapacity (ratio gamma epsilon N : ℝ)
    (e : K0 Q sourceDensity E0) : ℕ :=
  lowerScale (exceptionalPartTwoTarget Q sourceDensity E0
    ratio gamma epsilon N e)

theorem exceptionalLowDensity_le_highDensity
    (e : K0 Q sourceDensity E0) :
    exceptionalLowDensity Q sourceDensity E0 e ≤
      exceptionalHighDensity Q sourceDensity E0 e := by
  exact otherSide_largerSide_le
    (rawDensityA Q sourceDensity (edge0 Q sourceDensity E0 e))

theorem exceptionalGap
    (e : K0 Q sourceDensity E0) :
    eta ≤ exceptionalHighDensity Q sourceDensity E0 e -
      exceptionalLowDensity Q sourceDensity E0 e := by
  exact SelectedExceptionalEdges.rootSide_gap_of_unbalanced
    Q sourceDensity E0 e

theorem exceptionalPartTwoCapacity_cast_le
    (ratio gamma epsilon N : ℝ) (e : K0 Q sourceDensity E0)
    (hnonneg : 0 ≤ exceptionalPartTwoTarget Q sourceDensity E0
      ratio gamma epsilon N e) :
    (exceptionalPartTwoCapacity Q sourceDensity E0
        ratio gamma epsilon N e : ℝ) ≤
      exceptionalPartTwoTarget Q sourceDensity E0
        ratio gamma epsilon N e :=
  lowerScale_cast_le hnonneg

/-- Summation over the canonical finite index of selected exceptional edges
is literal summation over the selected finset. -/
theorem sum_exceptionalEdge
    (f : MatchingEdge Q.claim67.M → ℝ) :
    ∑ e : K0 Q sourceDensity E0, f (edge0 Q sourceDensity E0 e) =
      ∑ e ∈ E0.selected, f e := by
  classical
  let equiv := (Finset.equivFin E0.selected).symm
  calc
    ∑ e : K0 Q sourceDensity E0, f (edge0 Q sourceDensity E0 e) =
        ∑ e : {e // e ∈ E0.selected}, f e := by
      exact Fintype.sum_equiv equiv
        (fun e : K0 Q sourceDensity E0 ↦
          f (edge0 Q sourceDensity E0 e))
        (fun e : {e // e ∈ E0.selected} ↦ f e)
        (fun _ ↦ rfl)
    _ = ∑ e ∈ E0.selected, f e := Finset.sum_attach E0.selected f

theorem exceptionalLow_add_high_eq_oriented
    (e : K0 Q sourceDensity E0) :
    exceptionalLowDensity Q sourceDensity E0 e +
        exceptionalHighDensity Q sourceDensity E0 e =
      sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L
            (edge0 Q sourceDensity E0 e) 0) +
        sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L
            (edge0 Q sourceDensity E0 e) 1) := by
  generalize hside : exceptionalHighSide Q sourceDensity E0 e = side
  fin_cases side <;>
    by_cases hlarge : (edge0 Q sourceDensity E0 e).1.out.1 ∈ L <;>
    simp [exceptionalLowDensity, exceptionalHighDensity, exceptionalLowSide,
      hside, rawDensityA, orientedEndpoint, rawEndpoint,
      matchingEdgeEndpoint, hlarge, add_comm]

/-- The sum of the literal Part-2 edge targets contains the selected source
degree plus Zhao's exceptional-gap contribution on every selected edge. -/
theorem sourceDegree_add_exceptionalGap_le_sum_partTwoTarget
    (ratio gamma epsilon N : ℝ)
    (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1) (hN : 0 ≤ N) :
    sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.A) E0.selected +
        (Fintype.card (K0 Q sourceDensity E0) : ℝ) *
          ((ratio / (1 - ratio) * eta - 2 * gamma - 3 * epsilon) * N) ≤
      ∑ e : K0 Q sourceDensity E0,
        exceptionalPartTwoTarget Q sourceDensity E0
          ratio gamma epsilon N e := by
  have hden : 0 < 1 - ratio := sub_pos.mpr hratio1
  have hfactor : 0 ≤ ratio / (1 - ratio) := div_nonneg hratio0 hden.le
  have hedge (e : K0 Q sourceDensity E0) :
      N * (exceptionalLowDensity Q sourceDensity E0 e +
          exceptionalHighDensity Q sourceDensity E0 e) +
          (ratio / (1 - ratio) * eta - 2 * gamma - 3 * epsilon) * N ≤
        exceptionalPartTwoTarget Q sourceDensity E0
          ratio gamma epsilon N e := by
    have hgap := exceptionalGap Q sourceDensity E0 e
    have hweighted : ratio / (1 - ratio) * eta ≤
        ratio / (1 - ratio) *
          (exceptionalHighDensity Q sourceDensity E0 e -
            exceptionalLowDensity Q sourceDensity E0 e) :=
      mul_le_mul_of_nonneg_left hgap hfactor
    unfold exceptionalPartTwoTarget
    nlinarith
  calc
    sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.A) E0.selected +
        (Fintype.card (K0 Q sourceDensity E0) : ℝ) *
          ((ratio / (1 - ratio) * eta - 2 * gamma - 3 * epsilon) * N) =
        ∑ e : K0 Q sourceDensity E0,
          (N * (exceptionalLowDensity Q sourceDensity E0 e +
              exceptionalHighDensity Q sourceDensity E0 e) +
            (ratio / (1 - ratio) * eta - 2 * gamma - 3 * epsilon) * N) := by
      rw [sourceDegree_eq_sum]
      rw [← sum_exceptionalEdge Q sourceDensity E0
        (fun e ↦ N * (sourceDensity (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M L e 0) +
          sourceDensity (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M L e 1)))]
      simp_rw [← exceptionalLow_add_high_eq_oriented
        Q sourceDensity E0]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ ∑ e : K0 Q sourceDensity E0,
        exceptionalPartTwoTarget Q sourceDensity E0
          ratio gamma epsilon N e := by
      exact Finset.sum_le_sum fun e _ ↦ hedge e

variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ}
variable (ratio : ℝ)
variable
  (S : SelectedF0 P (balancedMajorBranches P ratio) target slack)

/-- Construct all three physical source allocations with Part-2 capacities
on `K0` and Part-1 capacities on `K1,Kb`. -/
theorem exists_sourceAllocation_partTwo_partOne_physical
    (gamma epsilon : ℝ)
    (hcount : 0 < count) (htargetB : 0 < targetB)
    (hnonnegA : ∀ e ∈ allMatchingEdges Q.claim67.M,
      0 ≤ N * (sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 0) +
        sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 1)))
    (hremainingA : 0 < sourceDegree Q.claim67.M L sourceDensity N
      (Sum.inl Q.A) (allMatchingEdges Q.claim67.M \
        (E0.selected ∪ Mb.selected)))
    (hbudget0 :
      ((branchMass P S.selected +
          Fintype.card (K0 Q sourceDensity E0) * small +
          Fintype.card (K0 Q sourceDensity E0) : ℕ) : ℝ) ≤
        ∑ e : K0 Q sourceDensity E0,
          exceptionalPartTwoTarget Q sourceDensity E0
            ratio gamma epsilon N e)
    (hbudget1 :
      ((branchMass P (majorResidualBranches P S) +
          Fintype.card (K1 Q sourceDensity E0 Mb) * small +
          Fintype.card (K1 Q sourceDensity E0 Mb) : ℕ) : ℝ) ≤
        ∑ e : K1 Q sourceDensity E0 Mb,
          (remainingLowDensity Q sourceDensity E0 Mb e +
            remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
            3 * epsilon) * N)
    (hbudgetb :
      ((branchMass P (minorBranches P) +
          Fintype.card (Kb Q sourceDensity Mb) * small +
          Fintype.card (Kb Q sourceDensity Mb) : ℕ) : ℝ) ≤
        ∑ e : Kb Q sourceDensity Mb,
          (reservedLowDensity Q sourceDensity Mb e +
            reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
            3 * epsilon) * N) :
    Nonempty (PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon)) := by
  apply exists_sourceAllocation_partOne_physical
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) gamma epsilon
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      hcount htargetB hnonnegA hremainingA
  · have h := demand_add_slack_le_sum_lowerScale
      (fun e : K0 Q sourceDensity E0 ↦
        exceptionalPartTwoTarget Q sourceDensity E0 ratio gamma epsilon N e)
      (branchMass P S.selected) small hbudget0
    simpa only [exceptionalPartTwoCapacity] using h
  · exact hbudget1
  · exact hbudgetb

/-- Source-degree form of the three aggregate packing hypotheses.  It is the
interface used by the rich decomposition: the ordinary families pay their
literal Part-1 reserve, while the exceptional family receives the Part-2
gap bonus on every selected edge. -/
theorem exists_sourceAllocation_partTwo_partOne_of_sourceDegrees
    (gamma epsilon : ℝ)
    (hcount : 0 < count) (htargetB : 0 < targetB)
    (hnonnegA : ∀ e ∈ allMatchingEdges Q.claim67.M,
      0 ≤ N * (sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 0) +
        sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 1)))
    (hremainingA : 0 < sourceDegree Q.claim67.M L sourceDensity N
      (Sum.inl Q.A) (allMatchingEdges Q.claim67.M \
        (E0.selected ∪ Mb.selected)))
    (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1) (hN : 0 ≤ N)
    (hbudget0 :
      ((branchMass P S.selected +
          Fintype.card (K0 Q sourceDensity E0) * small +
          Fintype.card (K0 Q sourceDensity E0) : ℕ) : ℝ) ≤
        sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.A)
            E0.selected +
          (Fintype.card (K0 Q sourceDensity E0) : ℝ) *
            ((ratio / (1 - ratio) * eta - 2 * gamma - 3 * epsilon) * N))
    (hbudget1 :
      ((branchMass P (majorResidualBranches P S) +
          Fintype.card (K1 Q sourceDensity E0 Mb) * small +
          Fintype.card (K1 Q sourceDensity E0 Mb) : ℕ) : ℝ) +
        (Fintype.card (K1 Q sourceDensity E0 Mb) : ℝ) *
          ((2 * gamma + 3 * epsilon) * N) ≤
        sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.A)
          (positiveRemainingEdgesA Q sourceDensity L N
            (E0.selected ∪ Mb.selected)))
    (hbudgetb :
      ((branchMass P (minorBranches P) +
          Fintype.card (Kb Q sourceDensity Mb) * small +
          Fintype.card (Kb Q sourceDensity Mb) : ℕ) : ℝ) +
        (Fintype.card (Kb Q sourceDensity Mb) : ℝ) *
          ((2 * gamma + 3 * epsilon) * N) ≤
        sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.B)
          Mb.selected) :
    Nonempty (PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon)) := by
  apply exists_sourceAllocation_partTwo_partOne_physical
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (ratio := ratio) (S := S) gamma epsilon hcount htargetB
    hnonnegA hremainingA
  · exact hbudget0.trans
      (sourceDegree_add_exceptionalGap_le_sum_partTwoTarget
        Q sourceDensity E0 ratio gamma epsilon N hratio0 hratio1 hN)
  · rw [sum_remainingPartOneTarget_eq
      Q sourceDensity E0 Mb gamma epsilon]
    linarith
  · rw [sum_reservedPartOneTarget_eq Q sourceDensity Mb gamma epsilon]
    linarith

/-- Source-only canonical threshold numerics for an exceptional Part-2
fiber. -/
theorem exceptionalPartTwoSourceNumerics
    (gamma epsilon N : ℝ)
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      cap1 capb)
    (e : K0 Q sourceDensity E0)
    (hratio0 : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hN : 0 < N) (hepsilon : 0 ≤ epsilon)
    (htarget : 0 ≤ exceptionalPartTwoTarget Q sourceDensity E0
      ratio gamma epsilon N e)
    (hhigh : 0 ≤
      (exceptionalHighDensity Q sourceDensity E0 e - gamma) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N)) :
    ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (exceptionalIndex Q sourceDensity E0 Mb e))
      ratio (exceptionalLowDensity Q sourceDensity E0 e)
        (exceptionalHighDensity Q sourceDensity E0 e) gamma epsilon N
        small := by
  apply exceptionalFiber_partTwoNumerics
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) ratio
    (exceptionalLowDensity Q sourceDensity E0 e)
    (exceptionalHighDensity Q sourceDensity E0 e) gamma epsilon N rfl e
  · exact hratio0
  · exact hratioHalf
  · exact exceptionalLowDensity_le_highDensity Q sourceDensity E0 e
  · exact hN.le
  · exact hhigh
  · exact hepsilon
  · exact exceptionalPartTwoCapacity_cast_le Q sourceDensity E0
      ratio gamma epsilon N e htarget
  · exact hround

/-- The literal exceptional Part-2 capacity yields the canonical threshold
certificate on that physical fiber. -/
noncomputable def exceptionalPartTwoCertificate
    (rho pairDensity removalBudget gamma epsilon N : ℝ)
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      cap1 capb)
    (e : K0 Q sourceDensity E0)
    (hratio0 : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hN : 0 < N) (hgamma : 0 ≤ gamma) (hepsilon : 0 ≤ epsilon)
    (htarget : 0 ≤ exceptionalPartTwoTarget Q sourceDensity E0
      ratio gamma epsilon N e)
    (hhigh : 0 ≤
      (exceptionalHighDensity Q sourceDensity E0 e - gamma) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N))
    (heta : 0 < eta)
    (hrow : ∀ x, 0 ≤ sourceDensity (Sum.inl Q.A) x)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x)
    (hmargin : ∀ c,
      (thresholdHighBudget
          (exceptionalHighDensity Q sourceDensity E0 e) gamma N : ℝ) +
          small + 1 + removalBudget + 1 ≤
        physicalFiberRhs Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb rho pairDensity
          (exceptionalIndex Q sourceDensity E0 Mb e) c) :
    PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) rho pairDensity removalBudget
      (exceptionalIndex Q sourceDensity E0 Mb e) := by
  let lowSide := exceptionalLowSide Q sourceDensity E0 e
  let highSide := exceptionalHighSide Q sourceDensity E0 e
  let dx := exceptionalLowDensity Q sourceDensity E0 e
  let dy := exceptionalHighDensity Q sourceDensity E0 e
  have D : ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (exceptionalIndex Q sourceDensity E0 Mb e))
      ratio dx dy gamma epsilon N small :=
    exceptionalPartTwoSourceNumerics Q sourceDensity E0 Mb P ratio S
      gamma epsilon N A e
      hratio0 hratioHalf hN hepsilon htarget hhigh hround
  apply physicalClassifiedThresholdCertificate
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
    rho pairDensity removalBudget ratio dx dy gamma epsilon N
    (exceptionalIndex Q sourceDensity E0 Mb e) lowSide highSide D
  · exact (otherSide_ne highSide).symm
  · simpa only [physicalRootGood, physicalRootVertex_exceptionalIndex,
      indexedPhysicalEdge_exceptionalIndex, highSide, exceptionalHighSide]
      using rootSide0_adj_A Q sourceDensity E0 heta hrow hAdj e
  · intro hbudget
    have hdxpos : 0 < dx := by
      by_contra hdx
      have hdxGamma : dx - gamma ≤ 0 := by linarith
      have htargetLow : (dx - gamma) * N ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hdxGamma hN.le
      exact hbudget (thresholdLowBudget_eq_zero_of_nonpos htargetLow)
    have hadj := hAdj
      (matchingEdgeEndpoint (edge0 Q sourceDensity E0 e).1 lowSide)
      (by change 0 < dx; exact hdxpos)
    simpa only [physicalRootGood, physicalRootVertex_exceptionalIndex,
      indexedPhysicalEdge_exceptionalIndex] using hadj
  · exact hmargin

end Erdos547b.ZhaoClaim615RichPhysicalPartTwo

#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartTwo.exceptionalGap
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartTwo.exists_sourceAllocation_partTwo_partOne_physical
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartTwo.exists_sourceAllocation_partTwo_partOne_of_sourceDegrees
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartTwo.exceptionalPartTwoCertificate
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartTwo.exceptionalPartTwoSourceNumerics
