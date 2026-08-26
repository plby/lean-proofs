/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalRootOrientation
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartOne
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartTwo
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartThree
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberMass

/-!
# Source-family constructors for physical root orientations

The arithmetic below is exactly the orientation/root-adjacency portion of
the older physical certificates, with their invalid static capacity premise
removed.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies

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
open Erdos547b.ZhaoClaim615RichPhysicalPartThree
open Erdos547b.ZhaoClaim615RichPhysicalFiberMass
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientation
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58FiberRootOrientation
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma54AppendixA

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
variable {which : ExceptionalCase}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
variable {target slack : ℕ}
variable (S : SelectedF0 P available target slack)

/-- Exceptional Part 2: source numerics choose the canonical root-admissible
orientation without any host capacity conclusion. -/
noncomputable def exceptionalPartTwoRootOrientation
    {E0 : SelectedExceptionalEdges Q sourceDensity L eta .unbalanced count}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {ratio gamma epsilon : ℝ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      cap1 capb)
    (havailableBalanced : available = balancedMajorBranches P ratio)
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
      (padGraph R).Adj (Sum.inl Q.A) x) :
    FiberRootOrientation
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (exceptionalIndex Q sourceDensity E0 Mb e))
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (exceptionalIndex Q sourceDensity E0 Mb e)) := by
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
      ratio dx dy gamma epsilon N small := by
    apply exceptionalFiber_partTwoNumerics
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) ratio dx dy gamma epsilon N
      havailableBalanced e
    · exact hratio0
    · exact hratioHalf
    · exact exceptionalLowDensity_le_highDensity Q sourceDensity E0 e
    · exact hN.le
    · exact hhigh
    · exact hepsilon
    · exact exceptionalPartTwoCapacity_cast_le Q sourceDensity E0
        ratio gamma epsilon N e htarget
    · exact hround
  apply physicalClassifiedRootOrientation
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) ratio dx dy gamma epsilon N
    (exceptionalIndex Q sourceDensity E0 Mb e) lowSide highSide D
  · exact (otherSide_ne highSide).symm
  · simpa only [physicalRootGood, physicalRootVertex_exceptionalIndex,
      indexedPhysicalEdge_exceptionalIndex, highSide, exceptionalHighSide]
      using rootSide0_adj_A Q sourceDensity E0 heta hrow hAdj e
  · intro hbudget
    have hdxpos : 0 < dx := by
      by_contra hdx
      have htargetLow : (dx - gamma) * N ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      exact hbudget (thresholdLowBudget_eq_zero_of_nonpos htargetLow)
    have hadj := hAdj
      (matchingEdgeEndpoint (edge0 Q sourceDensity E0 e).1 lowSide)
      (by change 0 < dx; exact hdxpos)
    simpa only [physicalRootGood, physicalRootVertex_exceptionalIndex,
      indexedPhysicalEdge_exceptionalIndex] using hadj

/-- The root-only exceptional orientation retains the complete-fiber load
bound supplied by the source threshold calculation. -/
theorem exceptionalPartTwoRootOrientation_sideLoad_le
    {E0 : SelectedExceptionalEdges Q sourceDensity L eta .unbalanced count}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {ratio gamma epsilon : ℝ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      cap1 capb)
    (havailableBalanced : available = balancedMajorBranches P ratio)
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
    (c : Fin 2) :
    sideLoad
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (exceptionalIndex Q sourceDensity E0 Mb e))
        (exceptionalPartTwoRootOrientation Q sourceDensity Mb P S A
          havailableBalanced e hratio0 hratioHalf hN hgamma hepsilon htarget
          hhigh hround heta hrow hAdj).orient c ≤
      thresholdHighBudget
        (exceptionalHighDensity Q sourceDensity E0 e) gamma N := by
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
      ratio dx dy gamma epsilon N small := by
    apply exceptionalFiber_partTwoNumerics
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) ratio dx dy gamma epsilon N
      havailableBalanced e
    · exact hratio0
    · exact hratioHalf
    · exact exceptionalLowDensity_le_highDensity Q sourceDensity E0 e
    · exact hN.le
    · exact hhigh
    · exact hepsilon
    · exact exceptionalPartTwoCapacity_cast_le Q sourceDensity E0
        ratio gamma epsilon N e htarget
    · exact hround
  unfold exceptionalPartTwoRootOrientation
  apply classifiedThresholdRootOrientation_sideLoad_le
    _ _ ratio dx dy gamma epsilon N small lowSide highSide D

/-- Remaining Part 1 root orientation. -/
noncomputable def remainingPartOneRootOrientation
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {gamma epsilon : ℝ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon) capb)
    (e : K1 Q sourceDensity E0 Mb)
    (hN : 0 < N) (hgamma : 0 ≤ gamma) (hepsilon : 0 ≤ epsilon)
    (htarget : 0 ≤
      (remainingLowDensity Q sourceDensity E0 Mb e +
        remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
        3 * epsilon) * N)
    (hhigh : 0 ≤
      (remainingHighDensity Q sourceDensity E0 Mb e - gamma) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N))
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x) :
    FiberRootOrientation
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (remainingIndex Q sourceDensity E0 Mb e))
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (remainingIndex Q sourceDensity E0 Mb e)) := by
  let lowSide := remainingLowSide Q sourceDensity E0 Mb e
  let highSide := remainingHighSide Q sourceDensity E0 Mb e
  let dx := remainingLowDensity Q sourceDensity E0 Mb e
  let dy := remainingHighDensity Q sourceDensity E0 Mb e
  have D : ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (remainingIndex Q sourceDensity E0 Mb e))
      0 dx dy gamma epsilon N small := by
    apply remainingFiber_partOneNumerics
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) e dx dy gamma epsilon N
    · exact remainingLowDensity_le_highDensity Q sourceDensity E0 Mb e
    · exact hN.le
    · exact hhigh
    · exact hepsilon
    · exact remainingPartOneCapacity_cast_le Q sourceDensity E0 Mb
        gamma epsilon e htarget
    · exact hround
  apply physicalClassifiedRootOrientation
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) 0 dx dy gamma epsilon N
    (remainingIndex Q sourceDensity E0 Mb e) lowSide highSide D
  · exact (otherSide_ne highSide).symm
  · simpa only [physicalRootGood, physicalRootVertex_remainingIndex,
      indexedPhysicalEdge_remainingIndex, highSide, remainingHighSide] using
        rootSide1_adj_A Q sourceDensity E0 Mb hN hAdj e
  · intro hbudget
    have hdxpos : 0 < dx := by
      by_contra hdx
      have htargetLow : (dx - gamma) * N ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      exact hbudget (thresholdLowBudget_eq_zero_of_nonpos htargetLow)
    have hadj := hAdj
      (matchingEdgeEndpoint (edge1 Q sourceDensity E0 Mb e).1 lowSide)
      (by change 0 < dx; exact hdxpos)
    simpa only [physicalRootGood, physicalRootVertex_remainingIndex,
      indexedPhysicalEdge_remainingIndex] using hadj

/-- Complete-fiber load bound for the remaining Part-1 orientation. -/
theorem remainingPartOneRootOrientation_sideLoad_le
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {gamma epsilon : ℝ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon) capb)
    (e : K1 Q sourceDensity E0 Mb)
    (hN : 0 < N) (hgamma : 0 ≤ gamma) (hepsilon : 0 ≤ epsilon)
    (htarget : 0 ≤
      (remainingLowDensity Q sourceDensity E0 Mb e +
        remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
        3 * epsilon) * N)
    (hhigh : 0 ≤
      (remainingHighDensity Q sourceDensity E0 Mb e - gamma) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N))
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x)
    (c : Fin 2) :
    sideLoad
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (remainingIndex Q sourceDensity E0 Mb e))
        (remainingPartOneRootOrientation Q sourceDensity E0 Mb P S A e hN
          hgamma hepsilon htarget hhigh hround hAdj).orient c ≤
      thresholdHighBudget
        (remainingHighDensity Q sourceDensity E0 Mb e) gamma N := by
  unfold remainingPartOneRootOrientation
  apply classifiedThresholdRootOrientation_sideLoad_le

/-- Total remaining-edge Part-1 orientation.  The published aggregate
packing estimate does not imply that every positive source edge individually
survives the `2*gamma+3*epsilon` reserve.  When it does survive, use the
classified threshold orientation above.  Otherwise its downward-rounded
capacity is zero, hence the source allocation assigns it an empty fiber; a
constant root orientation then has zero load. -/
noncomputable def remainingPartOneRootOrientationTotal
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {gamma epsilon : ℝ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon) capb)
    (e : K1 Q sourceDensity E0 Mb)
    (hN : 0 < N) (hgamma : 0 ≤ gamma) (hepsilon : 0 ≤ epsilon)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N))
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x) :
    FiberRootOrientationWithLoad
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (remainingIndex Q sourceDensity E0 Mb e))
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (remainingIndex Q sourceDensity E0 Mb e)) := by
  let dx := remainingLowDensity Q sourceDensity E0 Mb e
  let dy := remainingHighDensity Q sourceDensity E0 Mb e
  let target := (dx + dy - 2 * gamma - 3 * epsilon) * N
  by_cases htarget : 0 ≤ target
  · have hsum : 0 ≤ dx + dy - 2 * gamma - 3 * epsilon :=
      (mul_nonneg_iff_of_pos_right hN).mp htarget
    have hhighBase : 0 ≤ dy - gamma := by
      have hlowHigh := remainingLowDensity_le_highDensity
        Q sourceDensity E0 Mb e
      dsimp only [dx, dy] at hlowHigh ⊢
      nlinarith
    have hhigh : 0 ≤ (dy - gamma) * N :=
      mul_nonneg hhighBase hN.le
    exact (remainingPartOneRootOrientation Q sourceDensity E0 Mb P S A e
      hN hgamma hepsilon (by simpa only [target, dx, dy] using htarget)
      (by simpa only [dy] using hhigh) hround hAdj).withLoad
        (thresholdHighBudget dy gamma N)
        (by
          intro c
          simpa only [dy] using
            (remainingPartOneRootOrientation_sideLoad_le Q sourceDensity E0
              Mb P S A e hN hgamma hepsilon
              (by simpa only [target, dx, dy] using htarget)
              (by simpa only [dy] using hhigh) hround hAdj c))
  · have htargetNeg : target < 0 := lt_of_not_ge htarget
    have hcapacity :
        remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon e = 0 := by
      unfold remainingPartOneCapacity lowerScale
      apply Nat.floor_eq_zero.mpr
      simpa only [target, dx, dy] using htargetNeg.trans (by norm_num : (0 : ℝ) < 1)
    let forest := physicalFiberForest (Pcluster := Pcluster)
      (Gdegree := Gdegree) (threshold := threshold) (quota := quota) (R := R)
      (miss := miss) (Q := Q) (sourceDensity := sourceDensity) (E0 := E0)
      (Mb := Mb) (P := P) (S := S) (A := A)
      (remainingIndex Q sourceDensity E0 Mb e)
    have horderLe := remainingFiber_order_le_capacity
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) e
    have horder : forest.order = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [forest, hcapacity] using horderLe
    let orient : Fin (matchingFiber
        (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
          (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A))
        (remainingIndex Q sourceDensity E0 Mb e)).card → Fin 2 ≃ Fin 2 :=
      fun _ ↦ rootToSide (remainingHighSide Q sourceDensity E0 Mb e)
    refine {
      orient := orient
      root_good := ?_
      loadBound := thresholdHighBudget dy gamma N
      load_le := ?_
    }
    · intro i
      simpa only [orient, rootToSide_zero, remainingHighSide,
        physicalRootGood,
        physicalRootVertex_remainingIndex, indexedPhysicalEdge_remainingIndex]
        using rootSide1_adj_A Q sourceDensity E0 Mb hN hAdj e
    · intro c
      have htotal := sideLoad_zero_add_one forest orient
      have hleSum : sideLoad forest orient c ≤
          sideLoad forest orient 0 + sideLoad forest orient 1 := by
        fin_cases c
        · exact Nat.le_add_right _ _
        · exact Nat.le_add_left _ _
      have hle : sideLoad forest orient c ≤ forest.order :=
        hleSum.trans_eq htotal
      rw [horder] at hle
      exact hle.trans (Nat.zero_le _)

/-- Reserved Part 1 root orientation. -/
noncomputable def reservedPartOneRootOrientation
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {gamma epsilon : ℝ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (havailable : available ⊆ halfBranches P)
    (e : Kb Q sourceDensity Mb)
    (hN : 0 < N) (hgamma : 0 ≤ gamma) (hepsilon : 0 ≤ epsilon)
    (htarget : 0 ≤
      (reservedLowDensity Q sourceDensity Mb e +
        reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
        3 * epsilon) * N)
    (hhigh : 0 ≤
      (reservedHighDensity Q sourceDensity Mb e - gamma) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N))
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.B) x →
      (padGraph R).Adj (Sum.inl Q.B) x) :
    FiberRootOrientation
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (reservedIndex Q sourceDensity E0 Mb e))
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (reservedIndex Q sourceDensity E0 Mb e)) := by
  let lowSide := reservedLowSide Q sourceDensity Mb e
  let highSide := reservedHighSide Q sourceDensity Mb e
  let dx := reservedLowDensity Q sourceDensity Mb e
  let dy := reservedHighDensity Q sourceDensity Mb e
  have D : ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (reservedIndex Q sourceDensity E0 Mb e))
      0 dx dy gamma epsilon N small := by
    apply reservedFiber_partOneNumerics
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) havailable e dx dy gamma epsilon N
    · exact reservedLowDensity_le_highDensity Q sourceDensity Mb e
    · exact hN.le
    · exact hhigh
    · exact hepsilon
    · exact reservedPartOneCapacity_cast_le Q sourceDensity Mb
        gamma epsilon e htarget
    · exact hround
  apply physicalClassifiedRootOrientation
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) 0 dx dy gamma epsilon N
    (reservedIndex Q sourceDensity E0 Mb e) lowSide highSide D
  · exact (otherSide_ne highSide).symm
  · simpa only [physicalRootGood, physicalRootVertex_reservedIndex,
      indexedPhysicalEdge_reservedIndex, highSide, reservedHighSide] using
        rootSideb_adj_B Q sourceDensity Mb hN hAdj e
  · intro hbudget
    have hdxpos : 0 < dx := by
      by_contra hdx
      have htargetLow : (dx - gamma) * N ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
      exact hbudget (thresholdLowBudget_eq_zero_of_nonpos htargetLow)
    have hadj := hAdj
      (matchingEdgeEndpoint (edgeb Q sourceDensity Mb e).1 lowSide)
      (by change 0 < dx; exact hdxpos)
    simpa only [physicalRootGood, physicalRootVertex_reservedIndex,
      indexedPhysicalEdge_reservedIndex] using hadj

/-- Complete-fiber load bound for the reserved Part-1 orientation. -/
theorem reservedPartOneRootOrientation_sideLoad_le
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {gamma epsilon : ℝ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (havailable : available ⊆ halfBranches P)
    (e : Kb Q sourceDensity Mb)
    (hN : 0 < N) (hgamma : 0 ≤ gamma) (hepsilon : 0 ≤ epsilon)
    (htarget : 0 ≤
      (reservedLowDensity Q sourceDensity Mb e +
        reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
        3 * epsilon) * N)
    (hhigh : 0 ≤
      (reservedHighDensity Q sourceDensity Mb e - gamma) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N))
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.B) x →
      (padGraph R).Adj (Sum.inl Q.B) x)
    (c : Fin 2) :
    sideLoad
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (reservedIndex Q sourceDensity E0 Mb e))
        (reservedPartOneRootOrientation Q sourceDensity E0 Mb P S A
          havailable e hN hgamma hepsilon htarget hhigh hround hAdj).orient c ≤
      thresholdHighBudget
        (reservedHighDensity Q sourceDensity Mb e) gamma N := by
  unfold reservedPartOneRootOrientation
  apply classifiedThresholdRootOrientation_sideLoad_le

/-- Total reserved-edge Part-1 orientation, including the zero-capacity
case omitted by the pointwise source-threshold presentation. -/
noncomputable def reservedPartOneRootOrientationTotal
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {gamma epsilon : ℝ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (havailable : available ⊆ halfBranches P)
    (e : Kb Q sourceDensity Mb)
    (hN : 0 < N) (hgamma : 0 ≤ gamma) (hepsilon : 0 ≤ epsilon)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N))
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.B) x →
      (padGraph R).Adj (Sum.inl Q.B) x) :
    FiberRootOrientationWithLoad
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (reservedIndex Q sourceDensity E0 Mb e))
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (reservedIndex Q sourceDensity E0 Mb e)) := by
  let dx := reservedLowDensity Q sourceDensity Mb e
  let dy := reservedHighDensity Q sourceDensity Mb e
  let target := (dx + dy - 2 * gamma - 3 * epsilon) * N
  by_cases htarget : 0 ≤ target
  · have hsum : 0 ≤ dx + dy - 2 * gamma - 3 * epsilon :=
      (mul_nonneg_iff_of_pos_right hN).mp htarget
    have hhighBase : 0 ≤ dy - gamma := by
      have hlowHigh := reservedLowDensity_le_highDensity
        Q sourceDensity Mb e
      dsimp only [dx, dy] at hlowHigh ⊢
      nlinarith
    have hhigh : 0 ≤ (dy - gamma) * N :=
      mul_nonneg hhighBase hN.le
    exact (reservedPartOneRootOrientation Q sourceDensity E0 Mb P S A
      havailable e hN hgamma hepsilon
      (by simpa only [target, dx, dy] using htarget)
      (by simpa only [dy] using hhigh) hround hAdj).withLoad
        (thresholdHighBudget dy gamma N)
        (by
          intro c
          simpa only [dy] using
            (reservedPartOneRootOrientation_sideLoad_le Q sourceDensity E0 Mb
              P S A havailable e hN hgamma hepsilon
              (by simpa only [target, dx, dy] using htarget)
              (by simpa only [dy] using hhigh) hround hAdj c))
  · have htargetNeg : target < 0 := lt_of_not_ge htarget
    have hcapacity :
        reservedPartOneCapacity Q sourceDensity Mb gamma epsilon e = 0 := by
      unfold reservedPartOneCapacity lowerScale
      apply Nat.floor_eq_zero.mpr
      simpa only [target, dx, dy] using htargetNeg.trans (by norm_num : (0 : ℝ) < 1)
    let forest := physicalFiberForest (Pcluster := Pcluster)
      (Gdegree := Gdegree) (threshold := threshold) (quota := quota) (R := R)
      (miss := miss) (Q := Q) (sourceDensity := sourceDensity) (E0 := E0)
      (Mb := Mb) (P := P) (S := S) (A := A)
      (reservedIndex Q sourceDensity E0 Mb e)
    have horderLe := reservedFiber_order_le_capacity
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) havailable e
    have horder : forest.order = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [forest, hcapacity] using horderLe
    let orient : Fin (matchingFiber
        (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
          (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A))
        (reservedIndex Q sourceDensity E0 Mb e)).card → Fin 2 ≃ Fin 2 :=
      fun _ ↦ rootToSide (reservedHighSide Q sourceDensity Mb e)
    refine {
      orient := orient
      root_good := ?_
      loadBound := thresholdHighBudget dy gamma N
      load_le := ?_
    }
    · intro i
      simpa only [orient, rootToSide_zero, reservedHighSide,
        physicalRootGood,
        physicalRootVertex_reservedIndex, indexedPhysicalEdge_reservedIndex]
        using rootSideb_adj_B Q sourceDensity Mb hN hAdj e
    · intro c
      have htotal := sideLoad_zero_add_one forest orient
      have hleSum : sideLoad forest orient c ≤
          sideLoad forest orient 0 + sideLoad forest orient 1 := by
        fin_cases c
        · exact Nat.le_add_right _ _
        · exact Nat.le_add_left _ _
      have hle : sideLoad forest orient c ≤ forest.order :=
        hleSum.trans_eq htotal
      rw [horder] at hle
      exact hle.trans (Nat.zero_le _)

/-- Nonextreme Appendix orientation, stripped of the old static margin. -/
noncomputable def exceptionalPartThreeRootOrientation
    {E0 : SelectedExceptionalEdges Q sourceDensity L eta .nonextreme count}
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {gamma epsilon : ℝ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb)
    (e : K0 Q sourceDensity E0)
    (rootReserve sideReserve X Y P0 Q0 : ℕ)
    (D : AppendixA2NumericData
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (exceptionalIndex Q sourceDensity E0 Mb e))
      small rootReserve sideReserve X Y P0 Q0 gamma epsilon N)
    (heta : 0 < eta)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x) :
    FiberRootOrientation
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (exceptionalIndex Q sourceDensity E0 Mb e))
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (exceptionalIndex Q sourceDensity E0 Mb e)) := by
  apply physicalAppendixRootOrientation
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) gamma epsilon N
    (exceptionalIndex Q sourceDensity E0 Mb e) rootReserve sideReserve X Y P0
    Q0 D
  intro c
  have hadj := nonextremeRawSide_adj_A Q sourceDensity L eta heta hAdj
    (edge0 Q sourceDensity E0 e) (E0.edge_mem_family Q sourceDensity e) c
  simpa only [physicalRootGood, physicalRootVertex_exceptionalIndex,
    indexedPhysicalEdge_exceptionalIndex] using hadj

end Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies

#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies.exceptionalPartTwoRootOrientation
#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies.exceptionalPartTwoRootOrientation_sideLoad_le
#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies.remainingPartOneRootOrientation
#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies.remainingPartOneRootOrientation_sideLoad_le
#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies.reservedPartOneRootOrientation
#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies.reservedPartOneRootOrientation_sideLoad_le
#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies.exceptionalPartThreeRootOrientation
