/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberMass

/-!
# Source-faithful Part-1 capacities on physical Claim-6.15 edges

The constant average capacities are not host-feasible edge by edge.  This
module instead rounds down Zhao's literal density capacity on each remaining
or reserved matching edge and constructs its canonical threshold certificate.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalPartOne

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
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

def remainingHighSide (e : K1 Q sourceDensity E0 Mb) : Fin 2 :=
  rootSide1 Q sourceDensity E0 Mb e

def remainingLowSide (e : K1 Q sourceDensity E0 Mb) : Fin 2 :=
  otherSide (remainingHighSide Q sourceDensity E0 Mb e)

def remainingLowDensity (e : K1 Q sourceDensity E0 Mb) : ℝ :=
  rawDensityA Q sourceDensity (edge1 Q sourceDensity E0 Mb e)
    (remainingLowSide Q sourceDensity E0 Mb e)

def remainingHighDensity (e : K1 Q sourceDensity E0 Mb) : ℝ :=
  rawDensityA Q sourceDensity (edge1 Q sourceDensity E0 Mb e)
    (remainingHighSide Q sourceDensity E0 Mb e)

/-- Literal Part-1 capacity on a remaining `A`-edge. -/
def remainingPartOneCapacity (gamma epsilon : ℝ)
    (e : K1 Q sourceDensity E0 Mb) : ℕ :=
  lowerScale ((remainingLowDensity Q sourceDensity E0 Mb e +
      remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
      3 * epsilon) * N)

theorem remainingLowDensity_le_highDensity
    (e : K1 Q sourceDensity E0 Mb) :
    remainingLowDensity Q sourceDensity E0 Mb e ≤
      remainingHighDensity Q sourceDensity E0 Mb e := by
  exact otherSide_largerSide_le
    (rawDensityA Q sourceDensity (edge1 Q sourceDensity E0 Mb e))

theorem remainingPartOneCapacity_cast_le
    (gamma epsilon : ℝ) (e : K1 Q sourceDensity E0 Mb)
    (hnonneg : 0 ≤
      (remainingLowDensity Q sourceDensity E0 Mb e +
        remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
        3 * epsilon) * N) :
    (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon e : ℝ) ≤
      (remainingLowDensity Q sourceDensity E0 Mb e +
        remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
        3 * epsilon) * N :=
  lowerScale_cast_le hnonneg

def reservedHighSide (e : Kb Q sourceDensity Mb) : Fin 2 :=
  rootSideb Q sourceDensity Mb e

def reservedLowSide (e : Kb Q sourceDensity Mb) : Fin 2 :=
  otherSide (reservedHighSide Q sourceDensity Mb e)

def reservedLowDensity (e : Kb Q sourceDensity Mb) : ℝ :=
  rawDensityB Q sourceDensity (edgeb Q sourceDensity Mb e)
    (reservedLowSide Q sourceDensity Mb e)

def reservedHighDensity (e : Kb Q sourceDensity Mb) : ℝ :=
  rawDensityB Q sourceDensity (edgeb Q sourceDensity Mb e)
    (reservedHighSide Q sourceDensity Mb e)

/-- Literal Part-1 capacity on a reserved `B`-edge. -/
def reservedPartOneCapacity (gamma epsilon : ℝ)
    (e : Kb Q sourceDensity Mb) : ℕ :=
  lowerScale ((reservedLowDensity Q sourceDensity Mb e +
      reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
      3 * epsilon) * N)

theorem reservedLowDensity_le_highDensity
    (e : Kb Q sourceDensity Mb) :
    reservedLowDensity Q sourceDensity Mb e ≤
      reservedHighDensity Q sourceDensity Mb e := by
  exact otherSide_largerSide_le
    (rawDensityB Q sourceDensity (edgeb Q sourceDensity Mb e))

theorem reservedPartOneCapacity_cast_le
    (gamma epsilon : ℝ) (e : Kb Q sourceDensity Mb)
    (hnonneg : 0 ≤
      (reservedLowDensity Q sourceDensity Mb e +
        reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
        3 * epsilon) * N) :
    (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon e : ℝ) ≤
      (reservedLowDensity Q sourceDensity Mb e +
        reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
        3 * epsilon) * N :=
  lowerScale_cast_le hnonneg

theorem remainingLow_add_high_eq_oriented
    (e : K1 Q sourceDensity E0 Mb) :
    remainingLowDensity Q sourceDensity E0 Mb e +
        remainingHighDensity Q sourceDensity E0 Mb e =
      sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L
            (edge1 Q sourceDensity E0 Mb e) 0) +
        sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L
            (edge1 Q sourceDensity E0 Mb e) 1) := by
  generalize hside : remainingHighSide Q sourceDensity E0 Mb e = side
  fin_cases side <;>
    by_cases hlarge : (edge1 Q sourceDensity E0 Mb e).1.out.1 ∈ L <;>
    simp [remainingLowDensity, remainingHighDensity, remainingLowSide,
      hside, rawDensityA, orientedEndpoint, rawEndpoint,
      matchingEdgeEndpoint, hlarge, add_comm]

theorem reservedLow_add_high_eq_oriented
    (e : Kb Q sourceDensity Mb) :
    reservedLowDensity Q sourceDensity Mb e +
        reservedHighDensity Q sourceDensity Mb e =
      sourceDensity (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M L
            (edgeb Q sourceDensity Mb e) 0) +
        sourceDensity (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M L
            (edgeb Q sourceDensity Mb e) 1) := by
  generalize hside : reservedHighSide Q sourceDensity Mb e = side
  fin_cases side <;>
    by_cases hlarge : (edgeb Q sourceDensity Mb e).1.out.1 ∈ L <;>
    simp [reservedLowDensity, reservedHighDensity, reservedLowSide,
      hside, rawDensityB, orientedEndpoint, rawEndpoint,
      matchingEdgeEndpoint, hlarge, add_comm]

/-- Exact sum of the remaining-family Part-1 real capacities. -/
theorem sum_remainingPartOneTarget_eq
    (gamma epsilon : ℝ) :
    ∑ e : K1 Q sourceDensity E0 Mb,
        (remainingLowDensity Q sourceDensity E0 Mb e +
          remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
          3 * epsilon) * N =
      sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.A)
          (positiveRemainingEdgesA Q sourceDensity L N
            (E0.selected ∪ Mb.selected)) -
        (Fintype.card (K1 Q sourceDensity E0 Mb) : ℝ) *
          ((2 * gamma + 3 * epsilon) * N) := by
  have hsource :
      sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.A)
          (positiveRemainingEdgesA Q sourceDensity L N
            (E0.selected ∪ Mb.selected)) =
        ∑ e : K1 Q sourceDensity E0 Mb,
          N * (sourceDensity (Sum.inl Q.A)
              (orientedEndpoint Q.claim67.M L e.1 0) +
            sourceDensity (Sum.inl Q.A)
              (orientedEndpoint Q.claim67.M L e.1 1)) := by
    rw [sourceDegree_eq_sum]
    exact (Finset.sum_attach
      (positiveRemainingEdgesA Q sourceDensity L N
        (E0.selected ∪ Mb.selected))
      (fun e ↦ N * (sourceDensity (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L e 0) +
        sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 1)))).symm
  calc
    ∑ e : K1 Q sourceDensity E0 Mb,
        (remainingLowDensity Q sourceDensity E0 Mb e +
          remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
          3 * epsilon) * N =
        ∑ e : K1 Q sourceDensity E0 Mb,
          (N * (sourceDensity (Sum.inl Q.A)
              (orientedEndpoint Q.claim67.M L e.1 0) +
            sourceDensity (Sum.inl Q.A)
              (orientedEndpoint Q.claim67.M L e.1 1)) -
            (2 * gamma + 3 * epsilon) * N) := by
      apply Finset.sum_congr rfl
      intro e _
      change (remainingLowDensity Q sourceDensity E0 Mb e +
          remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
          3 * epsilon) * N =
        N * (sourceDensity (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M L
              (edge1 Q sourceDensity E0 Mb e) 0) +
          sourceDensity (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M L
              (edge1 Q sourceDensity E0 Mb e) 1)) -
          (2 * gamma + 3 * epsilon) * N
      rw [← remainingLow_add_high_eq_oriented
        Q sourceDensity E0 Mb e]
      ring
    _ = (∑ e : K1 Q sourceDensity E0 Mb,
          N * (sourceDensity (Sum.inl Q.A)
              (orientedEndpoint Q.claim67.M L e.1 0) +
            sourceDensity (Sum.inl Q.A)
              (orientedEndpoint Q.claim67.M L e.1 1))) -
        ∑ _e : K1 Q sourceDensity E0 Mb,
          (2 * gamma + 3 * epsilon) * N := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ e : K1 Q sourceDensity E0 Mb,
          N * (sourceDensity (Sum.inl Q.A)
              (orientedEndpoint Q.claim67.M L e.1 0) +
            sourceDensity (Sum.inl Q.A)
              (orientedEndpoint Q.claim67.M L e.1 1))) -
        (Fintype.card (K1 Q sourceDensity E0 Mb) : ℝ) *
          ((2 * gamma + 3 * epsilon) * N) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = _ := by rw [← hsource]

/-- Exact sum of the reserved-family Part-1 real capacities. -/
theorem sum_reservedPartOneTarget_eq
    (gamma epsilon : ℝ) :
    ∑ e : Kb Q sourceDensity Mb,
        (reservedLowDensity Q sourceDensity Mb e +
          reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
          3 * epsilon) * N =
      sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.B) Mb.selected -
        (Fintype.card (Kb Q sourceDensity Mb) : ℝ) *
          ((2 * gamma + 3 * epsilon) * N) := by
  have hsource :
      sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.B) Mb.selected =
        ∑ e : Kb Q sourceDensity Mb,
          N * (sourceDensity (Sum.inl Q.B)
              (orientedEndpoint Q.claim67.M L e.1 0) +
            sourceDensity (Sum.inl Q.B)
              (orientedEndpoint Q.claim67.M L e.1 1)) := by
    rw [sourceDegree_eq_sum]
    exact (Finset.sum_attach Mb.selected
      (fun e ↦ N * (sourceDensity (Sum.inl Q.B)
        (orientedEndpoint Q.claim67.M L e 0) +
        sourceDensity (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M L e 1)))).symm
  calc
    ∑ e : Kb Q sourceDensity Mb,
        (reservedLowDensity Q sourceDensity Mb e +
          reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
          3 * epsilon) * N =
        ∑ e : Kb Q sourceDensity Mb,
          (N * (sourceDensity (Sum.inl Q.B)
              (orientedEndpoint Q.claim67.M L e.1 0) +
            sourceDensity (Sum.inl Q.B)
              (orientedEndpoint Q.claim67.M L e.1 1)) -
            (2 * gamma + 3 * epsilon) * N) := by
      apply Finset.sum_congr rfl
      intro e _
      change (reservedLowDensity Q sourceDensity Mb e +
          reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
          3 * epsilon) * N =
        N * (sourceDensity (Sum.inl Q.B)
            (orientedEndpoint Q.claim67.M L
              (edgeb Q sourceDensity Mb e) 0) +
          sourceDensity (Sum.inl Q.B)
            (orientedEndpoint Q.claim67.M L
              (edgeb Q sourceDensity Mb e) 1)) -
          (2 * gamma + 3 * epsilon) * N
      rw [← reservedLow_add_high_eq_oriented Q sourceDensity Mb e]
      ring
    _ = (∑ e : Kb Q sourceDensity Mb,
          N * (sourceDensity (Sum.inl Q.B)
              (orientedEndpoint Q.claim67.M L e.1 0) +
            sourceDensity (Sum.inl Q.B)
              (orientedEndpoint Q.claim67.M L e.1 1))) -
        ∑ _e : Kb Q sourceDensity Mb,
          (2 * gamma + 3 * epsilon) * N := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ e : Kb Q sourceDensity Mb,
          N * (sourceDensity (Sum.inl Q.B)
              (orientedEndpoint Q.claim67.M L e.1 0) +
            sourceDensity (Sum.inl Q.B)
              (orientedEndpoint Q.claim67.M L e.1 1))) -
        (Fintype.card (Kb Q sourceDensity Mb) : ℝ) *
          ((2 * gamma + 3 * epsilon) * N) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = _ := by rw [← hsource]

variable (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
variable {target slack : ℕ}
variable (S : SelectedF0 P available target slack)

/-- Construct the physical source allocation with literal Part-1 capacities
on the remaining and reserved families.  The real aggregate premises include
the unavoidable one-unit floor loss per matching edge. -/
theorem exists_sourceAllocation_partOne_physical
    (gamma epsilon : ℝ)
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (hcount : 0 < count) (htargetB : 0 < targetB)
    (hnonnegA : ∀ e ∈ allMatchingEdges Q.claim67.M,
      0 ≤ N * (sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 0) +
        sourceDensity (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 1)))
    (hremainingA : 0 < sourceDegree Q.claim67.M L sourceDensity N
      (Sum.inl Q.A) (allMatchingEdges Q.claim67.M \
        (E0.selected ∪ Mb.selected)))
    (hbudget0 : branchMass P S.selected +
      Fintype.card (K0 Q sourceDensity E0) * small ≤ ∑ e, cap0 e)
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
    Nonempty (PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon)) := by
  have hK0 : 0 < Fintype.card (K0 Q sourceDensity E0) := by
    simpa [K0, E0.selected_card] using hcount
  let _ : Nonempty (K0 Q sourceDensity E0) :=
    Fintype.card_pos_iff.mp hK0
  let _ : Nonempty (K1 Q sourceDensity E0 Mb) := by
    obtain ⟨e, he⟩ := positiveRemainingEdgesA_nonempty Q sourceDensity L N
      (E0.selected ∪ Mb.selected) hnonnegA hremainingA
    exact ⟨⟨e, he⟩⟩
  let _ : Nonempty (Kb Q sourceDensity Mb) := by
    obtain ⟨e, he⟩ := PreliminaryReservedEdges.selected_nonempty
      Q sourceDensity Mb htargetB
    exact ⟨⟨e, he⟩⟩
  apply exists_sourceAllocation P S
    (K0 Q sourceDensity E0) (K1 Q sourceDensity E0 Mb)
    (Kb Q sourceDensity Mb) cap0
    (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
    (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon)
  · exact hbudget0
  · have h := demand_add_slack_le_sum_lowerScale
      (fun e : K1 Q sourceDensity E0 Mb ↦
        (remainingLowDensity Q sourceDensity E0 Mb e +
          remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
          3 * epsilon) * N)
      (branchMass P (majorResidualBranches P S)) small hbudget1
    simpa only [remainingPartOneCapacity] using h
  · have h := demand_add_slack_le_sum_lowerScale
      (fun e : Kb Q sourceDensity Mb ↦
        (reservedLowDensity Q sourceDensity Mb e +
          reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
          3 * epsilon) * N)
      (branchMass P (minorBranches P)) small hbudgetb
    simpa only [reservedPartOneCapacity] using h

/-- Source-only canonical threshold numerics for a remaining Part-1 fiber. -/
theorem remainingPartOneSourceNumerics
    (gamma epsilon : ℝ)
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon) capb)
    (e : K1 Q sourceDensity E0 Mb)
    (hN : 0 < N) (hepsilon : 0 ≤ epsilon)
    (htarget : 0 ≤
      (remainingLowDensity Q sourceDensity E0 Mb e +
        remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
        3 * epsilon) * N)
    (hhigh : 0 ≤
      (remainingHighDensity Q sourceDensity E0 Mb e - gamma) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N)) :
    ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (remainingIndex Q sourceDensity E0 Mb e))
      0 (remainingLowDensity Q sourceDensity E0 Mb e)
        (remainingHighDensity Q sourceDensity E0 Mb e) gamma epsilon N
        small := by
  apply remainingFiber_partOneNumerics
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) e
    (remainingLowDensity Q sourceDensity E0 Mb e)
    (remainingHighDensity Q sourceDensity E0 Mb e) gamma epsilon N
  · exact remainingLowDensity_le_highDensity Q sourceDensity E0 Mb e
  · exact hN.le
  · exact hhigh
  · exact hepsilon
  · exact remainingPartOneCapacity_cast_le Q sourceDensity E0 Mb
      gamma epsilon e htarget
  · exact hround

/-- Source-only canonical threshold numerics for a reserved Part-1 fiber. -/
theorem reservedPartOneSourceNumerics
    (gamma epsilon : ℝ)
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (havailable : available ⊆ halfBranches P)
    (e : Kb Q sourceDensity Mb)
    (hN : 0 < N) (hepsilon : 0 ≤ epsilon)
    (htarget : 0 ≤
      (reservedLowDensity Q sourceDensity Mb e +
        reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
        3 * epsilon) * N)
    (hhigh : 0 ≤
      (reservedHighDensity Q sourceDensity Mb e - gamma) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N)) :
    ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (reservedIndex Q sourceDensity E0 Mb e))
      0 (reservedLowDensity Q sourceDensity Mb e)
        (reservedHighDensity Q sourceDensity Mb e) gamma epsilon N small := by
  apply reservedFiber_partOneNumerics
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) havailable e
    (reservedLowDensity Q sourceDensity Mb e)
    (reservedHighDensity Q sourceDensity Mb e) gamma epsilon N
  · exact reservedLowDensity_le_highDensity Q sourceDensity Mb e
  · exact hN.le
  · exact hhigh
  · exact hepsilon
  · exact reservedPartOneCapacity_cast_le Q sourceDensity Mb
      gamma epsilon e htarget
  · exact hround

/-- The density-rounded remaining capacity, together with the Part-1 scalar
display, gives the actual canonical threshold certificate on that fiber. -/
noncomputable def remainingPartOneCertificate
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
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
    (hmargin : ∀ c,
      (thresholdHighBudget
          (remainingHighDensity Q sourceDensity E0 Mb e) gamma N : ℝ) +
          small + 1 + removalBudget + 1 ≤
        physicalFiberRhs Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb rho pairDensity
          (remainingIndex Q sourceDensity E0 Mb e) c) :
    PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) rho pairDensity removalBudget
      (remainingIndex Q sourceDensity E0 Mb e) := by
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
      0 dx dy gamma epsilon N small :=
    remainingPartOneSourceNumerics Q sourceDensity E0 Mb P S gamma epsilon A e hN
      hepsilon htarget hhigh hround
  apply physicalClassifiedThresholdCertificate
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
    rho pairDensity removalBudget 0 dx dy gamma epsilon N
    (remainingIndex Q sourceDensity E0 Mb e) lowSide highSide D
  · exact (otherSide_ne highSide).symm
  · simpa only [physicalRootGood, physicalRootVertex_remainingIndex,
      indexedPhysicalEdge_remainingIndex, highSide, remainingHighSide] using
        rootSide1_adj_A Q sourceDensity E0 Mb hN hAdj e
  · intro hbudget
    have hdxpos : 0 < dx := by
      by_contra hdx
      have hdxGamma : dx - gamma ≤ 0 := by linarith
      have htargetLow : (dx - gamma) * N ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hdxGamma hN.le
      exact hbudget (thresholdLowBudget_eq_zero_of_nonpos htargetLow)
    have hadj := hAdj
      (matchingEdgeEndpoint (edge1 Q sourceDensity E0 Mb e).1 lowSide)
      (by
        change 0 < dx
        exact hdxpos)
    simpa only [physicalRootGood, physicalRootVertex_remainingIndex,
      indexedPhysicalEdge_remainingIndex] using hadj
  · exact hmargin

/-- Reserved `B`-family version of `remainingPartOneCertificate`. -/
noncomputable def reservedPartOneCertificate
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
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
    (hmargin : ∀ c,
      (thresholdHighBudget
          (reservedHighDensity Q sourceDensity Mb e) gamma N : ℝ) +
          small + 1 + removalBudget + 1 ≤
        physicalFiberRhs Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb rho pairDensity
          (reservedIndex Q sourceDensity E0 Mb e) c) :
    PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) rho pairDensity removalBudget
      (reservedIndex Q sourceDensity E0 Mb e) := by
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
      0 dx dy gamma epsilon N small :=
    reservedPartOneSourceNumerics Q sourceDensity E0 Mb P S gamma epsilon A
      havailable e hN
      hepsilon htarget hhigh hround
  apply physicalClassifiedThresholdCertificate
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
    rho pairDensity removalBudget 0 dx dy gamma epsilon N
    (reservedIndex Q sourceDensity E0 Mb e) lowSide highSide D
  · exact (otherSide_ne highSide).symm
  · simpa only [physicalRootGood, physicalRootVertex_reservedIndex,
      indexedPhysicalEdge_reservedIndex, highSide, reservedHighSide] using
        rootSideb_adj_B Q sourceDensity Mb hN hAdj e
  · intro hbudget
    have hdxpos : 0 < dx := by
      by_contra hdx
      have hdxGamma : dx - gamma ≤ 0 := by linarith
      have htargetLow : (dx - gamma) * N ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hdxGamma hN.le
      exact hbudget (thresholdLowBudget_eq_zero_of_nonpos htargetLow)
    have hadj := hAdj
      (matchingEdgeEndpoint (edgeb Q sourceDensity Mb e).1 lowSide)
      (by
        change 0 < dx
        exact hdxpos)
    simpa only [physicalRootGood, physicalRootVertex_reservedIndex,
      indexedPhysicalEdge_reservedIndex] using hadj
  · exact hmargin

end Erdos547b.ZhaoClaim615RichPhysicalPartOne

#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartOne.remainingPartOneCertificate
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartOne.reservedPartOneCertificate
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartOne.remainingPartOneSourceNumerics
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartOne.reservedPartOneSourceNumerics
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartOne.exists_sourceAllocation_partOne_physical
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartOne.sum_remainingPartOneTarget_eq
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartOne.sum_reservedPartOneTarget_eq
