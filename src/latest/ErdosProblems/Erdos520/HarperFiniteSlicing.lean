import ErdosProblems.Erdos520.HarperScheduledRelativeInterval
import ErdosProblems.Erdos520.HarperGaussianVaryingWalk

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Finite lattice slicing for the Harper block path

Half-open coordinate cells form a disjoint lattice partition.  A cell which
meets a partial-sum barrier lies wholly inside the barrier obtained by
expanding its two sides by the cumulative cell widths.  Finite additivity
then transports any cellwise product-law comparison to a finite union of
such cells without another cardinality loss.
-/

/-- A generic finite-disjoint-union comparison.  The first measure only
uses the union bound; disjointness under the second measure turns its sum
back into the measure of the same union. -/
theorem measureReal_biUnion_finset_le_const_mul_of_cellwise
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (C : ℝ) (s : Finset ι) (cell : ι → Set Ω)
    (hdisj : Set.PairwiseDisjoint (↑s : Set ι) cell)
    (hmeas : ∀ i ∈ s, MeasurableSet (cell i))
    (hcell : ∀ i ∈ s, P.real (cell i) ≤ C * Q.real (cell i)) :
    P.real (⋃ i ∈ s, cell i) ≤
      C * Q.real (⋃ i ∈ s, cell i) := by
  calc
    P.real (⋃ i ∈ s, cell i) ≤
        ∑ i ∈ s, P.real (cell i) :=
      measureReal_biUnion_finset_le s cell
    _ ≤ ∑ i ∈ s, C * Q.real (cell i) :=
      Finset.sum_le_sum hcell
    _ = C * ∑ i ∈ s, Q.real (cell i) := by
      rw [Finset.mul_sum]
    _ = C * Q.real (⋃ i ∈ s, cell i) := by
      rw [measureReal_biUnion_finset hdisj hmeas]

/-- A half-open coordinate rectangle with lower corner `a` and coordinate
widths `delta`. -/
def harperCoordinateIocCell {n : ℕ}
    (a delta : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i ↦ Ioc (a i) (a i + delta i))

@[simp] theorem mem_harperCoordinateIocCell
    {n : ℕ} {a delta omega : Fin n → ℝ} :
    omega ∈ harperCoordinateIocCell a delta ↔
      ∀ i, a i < omega i ∧ omega i ≤ a i + delta i := by
  simp [harperCoordinateIocCell]

theorem measurableSet_harperCoordinateIocCell
    {n : ℕ} (a delta : Fin n → ℝ) :
    MeasurableSet (harperCoordinateIocCell a delta) := by
  exact MeasurableSet.univ_pi fun i ↦ measurableSet_Ioc

/-- Product-law mass of a coordinate cell is the product of its marginal
interval masses. -/
theorem measureReal_pi_harperCoordinateIocCell
    {n : ℕ} (rho : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (rho i)] (a delta : Fin n → ℝ) :
    (Measure.pi rho).real (harperCoordinateIocCell a delta) =
      ∏ i : Fin n, (rho i).real (Ioc (a i) (a i + delta i)) := by
  rw [Measure.real, harperCoordinateIocCell, Measure.pi_pi,
    ENNReal.toReal_prod]
  rfl

/-- Coordinatewise interval domination multiplies exactly across a product
cell. -/
theorem measureReal_pi_coordinateCell_le_prod_mul
    {n : ℕ} (rho nu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (rho i)] [∀ i, SigmaFinite (nu i)]
    (C a delta : Fin n → ℝ)
    (hcoord : ∀ i,
      (rho i).real (Ioc (a i) (a i + delta i)) ≤
        C i * (nu i).real (Ioc (a i) (a i + delta i))) :
    (Measure.pi rho).real (harperCoordinateIocCell a delta) ≤
      (∏ i, C i) *
        (Measure.pi nu).real (harperCoordinateIocCell a delta) := by
  rw [measureReal_pi_harperCoordinateIocCell,
    measureReal_pi_harperCoordinateIocCell]
  calc
    (∏ i : Fin n, (rho i).real (Ioc (a i) (a i + delta i))) ≤
        ∏ i : Fin n,
          C i * (nu i).real (Ioc (a i) (a i + delta i)) := by
      exact Finset.prod_le_prod
        (fun i _hi ↦ measureReal_nonneg) (fun i _hi ↦ hcoord i)
    _ = (∏ i, C i) *
        ∏ i : Fin n, (nu i).real (Ioc (a i) (a i + delta i)) := by
      rw [Finset.prod_mul_distrib]

/-- Integer lattice cell with coordinate-dependent widths. -/
def harperLatticeIocCell {n : ℕ}
    (delta : Fin n → ℝ) (z : Fin n → ℤ) : Set (Fin n → ℝ) :=
  harperCoordinateIocCell
    (fun i ↦ (z i : ℝ) * delta i) delta

@[simp] theorem mem_harperLatticeIocCell
    {n : ℕ} {delta : Fin n → ℝ} {z : Fin n → ℤ}
    {omega : Fin n → ℝ} :
    omega ∈ harperLatticeIocCell delta z ↔
      ∀ i, (z i : ℝ) * delta i < omega i ∧
        omega i ≤ (z i : ℝ) * delta i + delta i := by
  simp [harperLatticeIocCell]

theorem measurableSet_harperLatticeIocCell
    {n : ℕ} (delta : Fin n → ℝ) (z : Fin n → ℤ) :
    MeasurableSet (harperLatticeIocCell delta z) :=
  measurableSet_harperCoordinateIocCell _ _

/-- The canonical lattice cell containing a point.  The subtraction by one
matches our convention that cells are open on the left and closed on the
right, including when the point lies exactly on a lattice boundary. -/
noncomputable def harperLatticeIndex {n : ℕ}
    (delta omega : Fin n → ℝ) : Fin n → ℤ :=
  fun i ↦ ⌈omega i / delta i⌉ - 1

theorem mem_harperLatticeIocCell_harperLatticeIndex
    {n : ℕ} {delta omega : Fin n → ℝ}
    (hdelta : ∀ i, 0 < delta i) :
    omega ∈ harperLatticeIocCell delta
      (harperLatticeIndex delta omega) := by
  rw [mem_harperLatticeIocCell]
  intro i
  let q : ℝ := omega i / delta i
  have hleft : (((⌈q⌉ - 1 : ℤ) : ℝ)) < q := by
    simpa only [Int.cast_sub, Int.cast_one] using!
      (Int.le_ceil_iff.mp (le_refl ⌈q⌉))
  have hright : q ≤ ((⌈q⌉ : ℤ) : ℝ) := Int.le_ceil q
  have hmulLeft := mul_lt_mul_of_pos_right hleft (hdelta i)
  have hmulRight := mul_le_mul_of_nonneg_right hright (hdelta i).le
  constructor
  · simpa only [harperLatticeIndex, q, div_mul_cancel₀ _ (hdelta i).ne']
      using! hmulLeft
  · simpa only [harperLatticeIndex, q, Int.cast_sub, Int.cast_one,
      sub_mul, one_mul, sub_add_cancel, div_mul_cancel₀ _ (hdelta i).ne']
      using! hmulRight

/-- A coordinatewise symmetric box. -/
def harperCoordinateBox {n : ℕ} (R : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i ↦ Icc (-R i) (R i))

@[simp] theorem mem_harperCoordinateBox
    {n : ℕ} {R omega : Fin n → ℝ} :
    omega ∈ harperCoordinateBox R ↔ ∀ i, |omega i| ≤ R i := by
  simp only [harperCoordinateBox, Set.mem_pi, mem_univ, forall_const,
    Set.mem_Icc, abs_le, and_comm]

theorem measurableSet_harperCoordinateBox
    {n : ℕ} (R : Fin n → ℝ) :
    MeasurableSet (harperCoordinateBox R) := by
  exact MeasurableSet.univ_pi fun i ↦ measurableSet_Icc

/-- The finite set of lattice indices which can contain a point of the
coordinate box. -/
noncomputable def harperLatticeIndexFinset {n : ℕ}
    (delta R : Fin n → ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i ↦
    Finset.Icc (⌈-R i / delta i⌉ - 1) (⌈R i / delta i⌉ - 1)

theorem harperLatticeIndex_mem_finset_of_mem_box
    {n : ℕ} {delta R omega : Fin n → ℝ}
    (hdelta : ∀ i, 0 < delta i) (homega : omega ∈ harperCoordinateBox R) :
    harperLatticeIndex delta omega ∈
      harperLatticeIndexFinset delta R := by
  rw [harperLatticeIndexFinset, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hbox := (mem_harperCoordinateBox.mp homega) i
  have hlow : -R i / delta i ≤ omega i / delta i := by
    exact (div_le_div_iff_of_pos_right (hdelta i)).2 (abs_le.mp hbox).1
  have hupp : omega i / delta i ≤ R i / delta i := by
    exact (div_le_div_iff_of_pos_right (hdelta i)).2 (abs_le.mp hbox).2
  constructor
  · exact sub_le_sub_right (Int.ceil_le_ceil hlow) 1
  · exact sub_le_sub_right (Int.ceil_le_ceil hupp) 1

/-- The finite lattice family really covers the entire coordinate box. -/
theorem harperCoordinateBox_subset_biUnion_latticeIndexFinset
    {n : ℕ} {delta R : Fin n → ℝ} (hdelta : ∀ i, 0 < delta i) :
    harperCoordinateBox R ⊆
      ⋃ z ∈ harperLatticeIndexFinset delta R,
        harperLatticeIocCell delta z := by
  intro omega homega
  simp only [mem_iUnion]
  exact ⟨harperLatticeIndex delta omega,
    harperLatticeIndex_mem_finset_of_mem_box hdelta homega,
    mem_harperLatticeIocCell_harperLatticeIndex hdelta⟩

/-- Positive-width lattice cells are pairwise disjoint. -/
theorem pairwiseDisjoint_harperLatticeIocCell
    {n : ℕ} {delta : Fin n → ℝ} (hdelta : ∀ i, 0 < delta i) :
    Pairwise (fun z w : Fin n → ℤ ↦
      Disjoint (harperLatticeIocCell delta z)
        (harperLatticeIocCell delta w)) := by
  intro z w hzw
  rw [harperLatticeIocCell, harperLatticeIocCell,
    harperCoordinateIocCell, harperCoordinateIocCell,
    disjoint_univ_pi]
  have hcoord : ∃ i, z i ≠ w i := Function.ne_iff.mp hzw
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨i, ?_⟩
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · apply Set.Ioc_disjoint_Ioc_of_le
    have hint : z i + 1 ≤ w i := by omega
    have hcast : ((z i + 1 : ℤ) : ℝ) ≤ (w i : ℝ) := by
      exact_mod_cast hint
    calc
      (z i : ℝ) * delta i + delta i =
          ((z i + 1 : ℤ) : ℝ) * delta i := by
        push_cast
        ring
      _ ≤ (w i : ℝ) * delta i :=
        mul_le_mul_of_nonneg_right hcast (hdelta i).le
  · apply Disjoint.symm
    apply Set.Ioc_disjoint_Ioc_of_le
    have hint : w i + 1 ≤ z i := by omega
    have hcast : ((w i + 1 : ℤ) : ℝ) ≤ (z i : ℝ) := by
      exact_mod_cast hint
    calc
      (w i : ℝ) * delta i + delta i =
          ((w i + 1 : ℤ) : ℝ) * delta i := by
        push_cast
        ring
      _ ≤ (z i : ℝ) * delta i :=
        mul_le_mul_of_nonneg_right hcast (hdelta i).le

/-- Partial sum through coordinate `k`. -/
def harperPathPartialSum {n : ℕ} (omega : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ i ∈ Finset.Iic k, omega i

theorem harperPathPartialSum_zero
    (n : ℕ) (omega : Fin (n + 1) → ℝ) :
    harperPathPartialSum omega 0 = omega 0 := by
  have hset : Finset.Iic (0 : Fin (n + 1)) = {0} := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_singleton]
    constructor
    · intro hi
      apply Fin.eq_of_val_eq
      exact Nat.eq_zero_of_le_zero hi
    · rintro rfl
      exact le_rfl
  simp [harperPathPartialSum, hset]

theorem harperPathPartialSum_succ
    (n : ℕ) (omega : Fin (n + 1) → ℝ) (k : Fin n) :
    harperPathPartialSum omega k.succ =
      omega 0 + harperPathPartialSum (fun i ↦ omega i.succ) k := by
  have hset : Finset.Iic k.succ =
      insert 0 ((Finset.Iic k).map (Fin.succEmb n)) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  have hzero : (0 : Fin (n + 1)) ∉
      (Finset.Iic k).map (Fin.succEmb n) := by simp
  simp only [harperPathPartialSum, hset, Finset.sum_insert hzero,
    Finset.sum_map]
  congr 2

/-- The recursive upper-barrier predicate is implied by the equivalent
family of deterministic partial-sum inequalities. -/
theorem gaussianWalkTimeBarrierSurvives_of_partialSum_le
    (n : ℕ) (s : ℝ) (b omega : Fin n → ℝ)
    (h : ∀ k, s + harperPathPartialSum omega k ≤ b k) :
    gaussianWalkTimeBarrierSurvives n s b omega := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
      constructor
      · simpa only [harperPathPartialSum_zero, zero_add] using! h 0
      · apply ih (s := s + omega 0)
        intro k
        have hk := h k.succ
        rw [harperPathPartialSum_succ] at hk
        simpa only [add_assoc] using! hk

/-- Two-sided deterministic partial-sum barrier. -/
def harperPartialSumBarrierSet {n : ℕ}
    (lower upper : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {omega | ∀ k,
    lower k ≤ harperPathPartialSum omega k ∧
      harperPathPartialSum omega k ≤ upper k}

@[simp] theorem mem_harperPartialSumBarrierSet
    {n : ℕ} {lower upper omega : Fin n → ℝ} :
    omega ∈ harperPartialSumBarrierSet lower upper ↔
      ∀ k, lower k ≤ harperPathPartialSum omega k ∧
        harperPathPartialSum omega k ≤ upper k := Iff.rfl

/-- Cumulative mesh error through coordinate `k`. -/
def harperCumulativeCellWidth {n : ℕ}
    (delta : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ i ∈ Finset.Iic k, delta i

/-- The barrier with both sides enlarged by cumulative cell widths. -/
def harperExpandedPartialSumBarrierSet {n : ℕ}
    (lower upper delta : Fin n → ℝ) : Set (Fin n → ℝ) :=
  harperPartialSumBarrierSet
    (fun k ↦ lower k - harperCumulativeCellWidth delta k)
    (fun k ↦ upper k + harperCumulativeCellWidth delta k)

theorem harperPartialSumBarrierSet_subset_gaussianWalkTimeBarrierSet
    {n : ℕ} (lower upper : Fin n → ℝ) :
    harperPartialSumBarrierSet lower upper ⊆
      gaussianWalkTimeBarrierSet n 0 upper := by
  intro omega homega
  apply gaussianWalkTimeBarrierSurvives_of_partialSum_le
  intro k
  simpa only [zero_add] using!
    (mem_harperPartialSumBarrierSet.mp homega k).2

/-- If the expanded upper barrier is bounded by `B`, the expanded
two-sided event is contained in the usual flat upper-barrier survival
event. -/
theorem harperExpandedPartialSumBarrierSet_subset_gaussianWalkSurvivalSet
    {n : ℕ} {lower upper delta : Fin n → ℝ} {B : ℝ}
    (hB : ∀ k, upper k + harperCumulativeCellWidth delta k ≤ B) :
    harperExpandedPartialSumBarrierSet lower upper delta ⊆
      gaussianWalkSurvivalSet n B := by
  intro omega homega
  have htime : gaussianWalkTimeBarrierSurvives n 0
      (fun k ↦ upper k + harperCumulativeCellWidth delta k) omega :=
    harperPartialSumBarrierSet_subset_gaussianWalkTimeBarrierSet
      (fun k ↦ lower k - harperCumulativeCellWidth delta k)
      (fun k ↦ upper k + harperCumulativeCellWidth delta k) homega
  have hflat := gaussianWalkTimeBarrierSurvives_mono n 0 hB htime
  simpa only [sub_zero] using!
    (gaussianWalkTimeBarrierSurvives_const_iff n 0 B omega).mp hflat

/-- Varying-variance Gaussian bound for an expanded lattice barrier. -/
theorem measureReal_pi_gaussian_expandedBarrier_le
    {n : ℕ} (hn : 0 < n) (variance : Fin n → NNReal)
    (lower upper delta : Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ k, upper k + harperCumulativeCellWidth delta k ≤ B)
    (hlower : ∀ i, (1 / 3 : NNReal) ≤ variance i)
    (hupper : ∀ i, variance i ≤ (3 / 8 : NNReal)) :
    (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
        (harperExpandedPartialSumBarrierSet lower upper delta) ≤
      64 * (B + 2) / Real.sqrt (n : ℝ) := by
  have hsubset :=
    harperExpandedPartialSumBarrierSet_subset_gaussianWalkSurvivalSet
      (lower := lower) hB
  exact (measureReal_mono hsubset
      (measure_ne_top
        (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))) _)).trans
    (gaussianVarianceWalk_third_threeEighths_probability_le_fin
      n hn variance hB0 hlower hupper)

/-- Among the finitely many cells meeting the box, retain exactly those
which also meet the target partial-sum barrier inside the box. -/
noncomputable def harperBarrierBoxLatticeSlice {n : ℕ}
    (delta R lower upper : Fin n → ℝ) : Finset (Fin n → ℤ) := by
  classical
  exact (harperLatticeIndexFinset delta R).filter fun z ↦
    ((harperLatticeIocCell delta z ∩
      harperPartialSumBarrierSet lower upper) ∩
        harperCoordinateBox R).Nonempty

theorem mem_harperBarrierBoxLatticeSlice
    {n : ℕ} {delta R lower upper : Fin n → ℝ} {z : Fin n → ℤ} :
    z ∈ harperBarrierBoxLatticeSlice delta R lower upper ↔
      z ∈ harperLatticeIndexFinset delta R ∧
        ((harperLatticeIocCell delta z ∩
          harperPartialSumBarrierSet lower upper) ∩
            harperCoordinateBox R).Nonempty := by
  classical
  simp only [harperBarrierBoxLatticeSlice, Finset.mem_filter]

/-- The target barrier restricted to the moderate box is covered by its
finite active lattice slice. -/
theorem inter_barrier_box_subset_biUnion_activeLatticeSlice
    {n : ℕ} {delta R lower upper : Fin n → ℝ}
    (hdelta : ∀ i, 0 < delta i) :
    harperPartialSumBarrierSet lower upper ∩ harperCoordinateBox R ⊆
      ⋃ z ∈ harperBarrierBoxLatticeSlice delta R lower upper,
        harperLatticeIocCell delta z := by
  intro omega homega
  rcases homega with ⟨hbarrier, hbox⟩
  let z := harperLatticeIndex delta omega
  have hzcell : omega ∈ harperLatticeIocCell delta z :=
    mem_harperLatticeIocCell_harperLatticeIndex hdelta
  have hzfinite : z ∈ harperLatticeIndexFinset delta R :=
    harperLatticeIndex_mem_finset_of_mem_box hdelta hbox
  have hzactive : z ∈
      harperBarrierBoxLatticeSlice delta R lower upper := by
    rw [mem_harperBarrierBoxLatticeSlice]
    exact ⟨hzfinite, ⟨omega, ⟨hzcell, hbarrier⟩, hbox⟩⟩
  simp only [mem_iUnion]
  exact ⟨z, hzactive, hzcell⟩

/-- An active cell in a box of radius `R` has a lower corner of size at
most `R + 1`; the extra `+1` in the conclusion is the convention used by
the scheduled moderate-range theorem. -/
theorem abs_latticeCell_lowerCorner_add_one_le_of_mem_activeSlice
    {n : ℕ} {delta R lower upper K : Fin n → ℝ}
    (hdeltaOne : ∀ i, delta i ≤ 1)
    (hRK : ∀ i, R i + 2 ≤ K i)
    {z : Fin n → ℤ}
    (hz : z ∈ harperBarrierBoxLatticeSlice delta R lower upper)
    (i : Fin n) :
    |(z i : ℝ) * delta i| + 1 ≤ K i := by
  obtain ⟨x, ⟨hxcell, _hxbarrier⟩, hxbox⟩ :=
    (mem_harperBarrierBoxLatticeSlice.mp hz).2
  have hcell := (mem_harperLatticeIocCell.mp hxcell) i
  have hbox := (mem_harperCoordinateBox.mp hxbox) i
  let a : ℝ := (z i : ℝ) * delta i
  have hdiffNonneg : 0 ≤ x i - a := by
    dsimp only [a]
    exact sub_nonneg.mpr hcell.1.le
  have hdiffLe : x i - a ≤ delta i := by
    dsimp only [a]
    linarith [hcell.2]
  have habsDiff : |x i - a| ≤ delta i := by
    rw [abs_of_nonneg hdiffNonneg]
    exact hdiffLe
  have ha : |a| ≤ |x i| + |x i - a| := by
    calc
      |a| = |x i - (x i - a)| := by congr 1; ring
      _ ≤ |x i| + |x i - a| := abs_sub _ _
  linarith [ha, habsDiff, hbox, hdeltaOne i, hRK i]

theorem harperCumulativeCellWidth_nonneg
    {n : ℕ} {delta : Fin n → ℝ} (hdelta : ∀ i, 0 ≤ delta i)
    (k : Fin n) :
    0 ≤ harperCumulativeCellWidth delta k := by
  exact Finset.sum_nonneg fun i _hi ↦ hdelta i

/-- Two points in the same coordinate cell differ by at most that
coordinate's width. -/
theorem abs_sub_le_of_mem_harperCoordinateIocCell
    {n : ℕ} {a delta x y : Fin n → ℝ}
    (hx : x ∈ harperCoordinateIocCell a delta)
    (hy : y ∈ harperCoordinateIocCell a delta) (i : Fin n) :
    |y i - x i| ≤ delta i := by
  have hxi := (mem_harperCoordinateIocCell.mp hx) i
  have hyi := (mem_harperCoordinateIocCell.mp hy) i
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Consequently, every partial sum changes by at most the cumulative cell
width. -/
theorem abs_harperPathPartialSum_sub_le_of_mem_coordinateCell
    {n : ℕ} {a delta x y : Fin n → ℝ}
    (hx : x ∈ harperCoordinateIocCell a delta)
    (hy : y ∈ harperCoordinateIocCell a delta) (k : Fin n) :
    |harperPathPartialSum y k - harperPathPartialSum x k| ≤
      harperCumulativeCellWidth delta k := by
  calc
    |harperPathPartialSum y k - harperPathPartialSum x k| =
        |∑ i ∈ Finset.Iic k, (y i - x i)| := by
      simp only [harperPathPartialSum, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.Iic k, |y i - x i| :=
      Finset.abs_sum_le_sum_abs (fun i ↦ y i - x i) (Finset.Iic k)
    _ ≤ ∑ i ∈ Finset.Iic k, delta i := by
      exact Finset.sum_le_sum fun i _hi ↦
        abs_sub_le_of_mem_harperCoordinateIocCell hx hy i
    _ = harperCumulativeCellWidth delta k := rfl

/-- If a coordinate cell meets a two-sided partial-sum barrier, the whole
cell lies in the barrier expanded by `±` the cumulative coordinate widths. -/
theorem harperCoordinateIocCell_subset_expandedBarrier_of_intersects
    {n : ℕ} {a delta lower upper : Fin n → ℝ}
    (hintersects :
      (harperCoordinateIocCell a delta ∩
        harperPartialSumBarrierSet lower upper).Nonempty) :
    harperCoordinateIocCell a delta ⊆
      harperExpandedPartialSumBarrierSet lower upper delta := by
  obtain ⟨x, hxcell, hxbarrier⟩ := hintersects
  intro y hycell
  change ∀ k,
    lower k - harperCumulativeCellWidth delta k ≤
        harperPathPartialSum y k ∧
      harperPathPartialSum y k ≤
        upper k + harperCumulativeCellWidth delta k
  intro k
  have hclose :=
    abs_harperPathPartialSum_sub_le_of_mem_coordinateCell
      hxcell hycell k
  have hdiff := (abs_le.mp hclose)
  have hxbar := (mem_harperPartialSumBarrierSet.mp hxbarrier) k
  constructor <;> linarith

/-- Lattice-cell specialization of the preceding geometric inclusion. -/
theorem harperLatticeIocCell_subset_expandedBarrier_of_intersects
    {n : ℕ} {delta : Fin n → ℝ} {z : Fin n → ℤ}
    {lower upper : Fin n → ℝ}
    (hintersects :
      (harperLatticeIocCell delta z ∩
        harperPartialSumBarrierSet lower upper).Nonempty) :
    harperLatticeIocCell delta z ⊆
      harperExpandedPartialSumBarrierSet lower upper delta := by
  exact harperCoordinateIocCell_subset_expandedBarrier_of_intersects
    hintersects

/-- A finite family of lattice cells which each meets the original barrier
is contained in the same cumulatively expanded barrier. -/
theorem biUnion_harperLatticeIocCell_subset_expandedBarrier
    {n : ℕ} (s : Finset (Fin n → ℤ))
    {delta lower upper : Fin n → ℝ}
    (hintersects : ∀ z ∈ s,
      (harperLatticeIocCell delta z ∩
        harperPartialSumBarrierSet lower upper).Nonempty) :
    (⋃ z ∈ s, harperLatticeIocCell delta z) ⊆
      harperExpandedPartialSumBarrierSet lower upper delta := by
  intro omega homega
  simp only [mem_iUnion] at homega
  obtain ⟨z, hz, hzcell⟩ := homega
  exact harperLatticeIocCell_subset_expandedBarrier_of_intersects
    (hintersects z hz) hzcell

theorem harperLatticeIocCell_intersects_barrier_of_mem_activeSlice
    {n : ℕ} {delta R lower upper : Fin n → ℝ} {z : Fin n → ℤ}
    (hz : z ∈ harperBarrierBoxLatticeSlice delta R lower upper) :
    (harperLatticeIocCell delta z ∩
      harperPartialSumBarrierSet lower upper).Nonempty := by
  obtain ⟨x, ⟨hxcell, hxbarrier⟩, _hxbox⟩ :=
    (mem_harperBarrierBoxLatticeSlice.mp hz).2
  exact ⟨x, hxcell, hxbarrier⟩

/-- The active finite slice lies inside the cumulatively expanded barrier. -/
theorem biUnion_activeLatticeSlice_subset_expandedBarrier
    {n : ℕ} {delta R lower upper : Fin n → ℝ} :
    (⋃ z ∈ harperBarrierBoxLatticeSlice delta R lower upper,
      harperLatticeIocCell delta z) ⊆
        harperExpandedPartialSumBarrierSet lower upper delta := by
  apply biUnion_harperLatticeIocCell_subset_expandedBarrier
  intro z hz
  exact harperLatticeIocCell_intersects_barrier_of_mem_activeSlice hz

/-- Finite Harper slicing: a cellwise comparison for two finite measures
passes to any finite lattice slice, and the Gaussian union can then be
enlarged to the cumulative-width barrier. -/
theorem measureReal_biUnion_harperLatticeIocCell_le_expandedBarrier
    {n : ℕ} (P Q : Measure (Fin n → ℝ))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (C : ℝ) (hC : 0 ≤ C) (s : Finset (Fin n → ℤ))
    {delta lower upper : Fin n → ℝ}
    (hdelta : ∀ i, 0 < delta i)
    (hintersects : ∀ z ∈ s,
      (harperLatticeIocCell delta z ∩
        harperPartialSumBarrierSet lower upper).Nonempty)
    (hcell : ∀ z ∈ s,
      P.real (harperLatticeIocCell delta z) ≤
        C * Q.real (harperLatticeIocCell delta z)) :
    P.real (⋃ z ∈ s, harperLatticeIocCell delta z) ≤
      C * Q.real
        (harperExpandedPartialSumBarrierSet lower upper delta) := by
  have hdisj : Set.PairwiseDisjoint (↑s : Set (Fin n → ℤ))
      (harperLatticeIocCell delta) := by
    intro z _hz w _hw hzw
    exact pairwiseDisjoint_harperLatticeIocCell hdelta hzw
  have hslice := measureReal_biUnion_finset_le_const_mul_of_cellwise
    P Q C s (harperLatticeIocCell delta) hdisj
      (fun z _hz ↦ measurableSet_harperLatticeIocCell delta z) hcell
  have hsubset :=
    biUnion_harperLatticeIocCell_subset_expandedBarrier s hintersects
  exact hslice.trans
    (mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hC)

/-- Complete finite-slicing sandwich: the original barrier inside the box
is covered by active cells, and those cells are compared to the expanded
barrier under the reference law. -/
theorem measureReal_inter_barrier_box_le_expandedBarrier
    {n : ℕ} (P Q : Measure (Fin n → ℝ))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (C : ℝ) (hC : 0 ≤ C)
    {delta R lower upper : Fin n → ℝ}
    (hdelta : ∀ i, 0 < delta i)
    (hcell : ∀ z ∈ harperBarrierBoxLatticeSlice delta R lower upper,
      P.real (harperLatticeIocCell delta z) ≤
        C * Q.real (harperLatticeIocCell delta z)) :
    P.real (harperPartialSumBarrierSet lower upper ∩
        harperCoordinateBox R) ≤
      C * Q.real
        (harperExpandedPartialSumBarrierSet lower upper delta) := by
  have hcover := inter_barrier_box_subset_biUnion_activeLatticeSlice
    (delta := delta) (R := R) (lower := lower) (upper := upper) hdelta
  exact (measureReal_mono hcover (measure_ne_top P _)).trans
    (measureReal_biUnion_harperLatticeIocCell_le_expandedBarrier
      P Q C hC (harperBarrierBoxLatticeSlice delta R lower upper)
      hdelta
      (fun z hz ↦
        harperLatticeIocCell_intersects_barrier_of_mem_activeSlice hz)
      hcell)

/-- Product-law version with hypotheses stated coordinate by coordinate.
The multiplicative comparison constant is exactly the product of the
coordinate constants, and no factor depending on the number of selected
cells is introduced. -/
theorem measureReal_pi_biUnion_harperLatticeIocCell_le_expandedBarrier
    {n : ℕ} (rho nu : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (rho i)]
    [∀ i, IsProbabilityMeasure (nu i)]
    (C delta lower upper : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hdelta : ∀ i, 0 < delta i)
    (s : Finset (Fin n → ℤ))
    (hintersects : ∀ z ∈ s,
      (harperLatticeIocCell delta z ∩
        harperPartialSumBarrierSet lower upper).Nonempty)
    (hcoord : ∀ z ∈ s, ∀ i,
      (rho i).real
          (Ioc ((z i : ℝ) * delta i)
            ((z i : ℝ) * delta i + delta i)) ≤
        C i * (nu i).real
          (Ioc ((z i : ℝ) * delta i)
            ((z i : ℝ) * delta i + delta i))) :
    (Measure.pi rho).real
        (⋃ z ∈ s, harperLatticeIocCell delta z) ≤
      (∏ i, C i) *
        (Measure.pi nu).real
          (harperExpandedPartialSumBarrierSet lower upper delta) := by
  apply measureReal_biUnion_harperLatticeIocCell_le_expandedBarrier
    (Measure.pi rho) (Measure.pi nu) (∏ i, C i)
      (Finset.prod_nonneg fun i _hi ↦ hC i) s hdelta hintersects
  intro z hz
  simpa only [harperLatticeIocCell] using!
    measureReal_pi_coordinateCell_le_prod_mul rho nu C
      (fun i ↦ (z i : ℝ) * delta i) delta (hcoord z hz)

/-- Product-law form of the complete finite-slicing sandwich. -/
theorem measureReal_pi_inter_barrier_box_le_expandedBarrier
    {n : ℕ} (rho nu : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (rho i)]
    [∀ i, IsProbabilityMeasure (nu i)]
    (C delta R lower upper : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hdelta : ∀ i, 0 < delta i)
    (hcoord :
      ∀ z ∈ harperBarrierBoxLatticeSlice delta R lower upper, ∀ i,
        (rho i).real
            (Ioc ((z i : ℝ) * delta i)
              ((z i : ℝ) * delta i + delta i)) ≤
          C i * (nu i).real
            (Ioc ((z i : ℝ) * delta i)
              ((z i : ℝ) * delta i + delta i))) :
    (Measure.pi rho).real
        (harperPartialSumBarrierSet lower upper ∩
          harperCoordinateBox R) ≤
      (∏ i, C i) *
        (Measure.pi nu).real
          (harperExpandedPartialSumBarrierSet lower upper delta) := by
  apply measureReal_inter_barrier_box_le_expandedBarrier
    (Measure.pi rho) (Measure.pi nu) (∏ i, C i)
      (Finset.prod_nonneg fun i _hi ↦ hC i) hdelta
  intro z hz
  simpa only [harperLatticeIocCell] using!
    measureReal_pi_coordinateCell_le_prod_mul rho nu C
      (fun i ↦ (z i : ℝ) * delta i) delta (hcoord z hz)

/-- Specializing every coordinate constant to `2` exposes the exact loss
of the current relative-interval input: it is `2^n`, not a cell-count
factor. -/
theorem measureReal_pi_inter_barrier_box_le_two_pow_mul_expandedBarrier
    {n : ℕ} (rho nu : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (rho i)]
    [∀ i, IsProbabilityMeasure (nu i)]
    (delta R lower upper : Fin n → ℝ)
    (hdelta : ∀ i, 0 < delta i)
    (hcoord :
      ∀ z ∈ harperBarrierBoxLatticeSlice delta R lower upper, ∀ i,
        (rho i).real
            (Ioc ((z i : ℝ) * delta i)
              ((z i : ℝ) * delta i + delta i)) ≤
          2 * (nu i).real
            (Ioc ((z i : ℝ) * delta i)
              ((z i : ℝ) * delta i + delta i))) :
    (Measure.pi rho).real
        (harperPartialSumBarrierSet lower upper ∩
          harperCoordinateBox R) ≤
      (2 : ℝ) ^ n *
        (Measure.pi nu).real
          (harperExpandedPartialSumBarrierSet lower upper delta) := by
  simpa only [Fin.prod_const, Fintype.card_fin] using!
    measureReal_pi_inter_barrier_box_le_expandedBarrier rho nu
      (fun _ ↦ (2 : ℝ)) delta R lower upper (fun _ ↦ by norm_num)
      hdelta hcoord

/-! ## Scheduled moderate-box specialization -/

noncomputable def harperScheduledRelativeCellWidth
    (start n : ℕ) : Fin n → ℝ :=
  fun i ↦ harperScheduledRelativeIntervalWidth (start + (i : ℕ))

noncomputable def harperScheduledModerateThreshold
    (start n : ℕ) : Fin n → ℝ :=
  fun i ↦ (1 / 4 : ℝ) *
    Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ))

/-- Shrinking the coordinate radius by `2` leaves room for the width-≤1
cell displacement and for the `|a|+1` convention in the local comparison. -/
noncomputable def harperScheduledModerateRadius
    (start n : ℕ) : Fin n → ℝ :=
  fun i ↦ harperScheduledModerateThreshold start n i - 2

theorem harperScheduledRelativeCellWidth_pos
    (start n : ℕ) (i : Fin n) :
    0 < harperScheduledRelativeCellWidth start n i :=
  harperScheduledRelativeIntervalWidth_pos _

theorem harperScheduledRelativeCellWidth_le_one
    (start n : ℕ) (i : Fin n) :
    harperScheduledRelativeCellWidth start n i ≤ 1 :=
  harperScheduledRelativeIntervalWidth_le_one _

theorem abs_scheduledLatticeCell_lowerCorner_add_one_le_of_mem_activeSlice
    {start n : ℕ} {lower upper : Fin n → ℝ} {z : Fin n → ℤ}
    (hz : z ∈ harperBarrierBoxLatticeSlice
      (harperScheduledRelativeCellWidth start n)
      (harperScheduledModerateRadius start n) lower upper)
    (i : Fin n) :
    |(z i : ℝ) * harperScheduledRelativeCellWidth start n i| + 1 ≤
      harperScheduledModerateThreshold start n i := by
  apply abs_latticeCell_lowerCorner_add_one_le_of_mem_activeSlice
    (delta := harperScheduledRelativeCellWidth start n)
    (R := harperScheduledModerateRadius start n)
    (lower := lower) (upper := upper)
    (K := harperScheduledModerateThreshold start n)
  · exact harperScheduledRelativeCellWidth_le_one start n
  · intro k
    unfold harperScheduledModerateRadius
    linarith
  · exact hz

/-- Unconditional scheduled finite slicing on the full moderate-box piece.
The local comparison is fully proved, but multiplying its coarse constant
`2` across `n` independent coordinates gives the displayed `2^n` loss. -/
theorem exists_eventually_harperScheduledModerateBoxBarrierProbability_le_two_pow_mul_gaussian
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ lower upper : Fin n → ℝ,
            (Measure.pi (fun i : Fin n ↦
              harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)).real
                (harperPartialSumBarrierSet lower upper ∩
                  harperCoordinateBox
                    (harperScheduledModerateRadius start n)) ≤
              (2 : ℝ) ^ n *
                (Measure.pi (fun i : Fin n ↦
                  harperGaussianBlockLaw y
                    (harperScheduledPrimeBlock y
                      (start + (i : ℕ))) t t)).real
                    (harperExpandedPartialSumBarrierSet lower upper
                      (harperScheduledRelativeCellWidth start n)) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledRelativeIntervalProbability_le_two_mul_gaussian M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper lower upper
  apply measureReal_pi_inter_barrier_box_le_two_pow_mul_expandedBarrier
    (rho := fun i : Fin n ↦
      harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)
    (nu := fun i : Fin n ↦
      harperGaussianBlockLaw y
        (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)
    (delta := harperScheduledRelativeCellWidth start n)
    (R := harperScheduledModerateRadius start n)
    (lower := lower) (upper := upper)
  · exact harperScheduledRelativeCellWidth_pos start n
  · intro z hz i
    have hindex : J ≤ start + (i : ℕ) :=
      hstart.trans (Nat.le_add_right start i)
    have hendpoint :
        harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
      exact (monotone_harperBlockEndpoint (by omega)).trans hy
    have hmoderate :=
      abs_scheduledLatticeCell_lowerCorner_add_one_le_of_mem_activeSlice
        hz i
    simpa only [harperScheduledRelativeCellWidth,
      harperScheduledModerateThreshold] using!
      hJ (start + (i : ℕ)) hindex y hendpoint t htLower htUpper
        ((z i : ℝ) *
          harperScheduledRelativeIntervalWidth (start + (i : ℕ)))
        hmoderate

/-- The same unconditional scheduled comparison with the varying-Gaussian
walk estimate applied to the expanded upper barrier.  This closes the
finite geometry and Gaussian-probability parts of the route; the remaining
quantitative defect is explicitly the leading `2^n`. -/
theorem exists_eventually_harperScheduledModerateBoxBarrierProbability_le_two_pow_mul_walkBound
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ, 0 < n →
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ B : ℝ, 0 ≤ B → ∀ lower upper : Fin n → ℝ,
            (∀ k, upper k + harperCumulativeCellWidth
              (harperScheduledRelativeCellWidth start n) k ≤ B) →
            (Measure.pi (fun i : Fin n ↦
              harperCenteredLinearBlockLaw y
                (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)).real
                (harperPartialSumBarrierSet lower upper ∩
                  harperCoordinateBox
                    (harperScheduledModerateRadius start n)) ≤
              (2 : ℝ) ^ n *
                (64 * (B + 2) / Real.sqrt (n : ℝ)) := by
  obtain ⟨Jslice, hJslice⟩ :=
    exists_eventually_harperScheduledModerateBoxBarrierProbability_le_two_pow_mul_gaussian M
  obtain ⟨Jvar, hJvar⟩ :=
    exists_eventually_harperScheduledDiagonalVariance_third_threeEighths M
  refine ⟨max Jslice Jvar, ?_⟩
  intro start hstart n y hn hy t htLower htUpper B hB0 lower upper hB
  have hstartSlice : Jslice ≤ start :=
    (le_max_left Jslice Jvar).trans hstart
  have hstartVar : Jvar ≤ start :=
    (le_max_right Jslice Jvar).trans hstart
  have hslice := hJslice start hstartSlice n y hy t htLower htUpper
    lower upper
  let variance : Fin n → NNReal := fun i ↦
    harperLinearBlockVarianceNNReal y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t t
  have hlower : ∀ i, (1 / 3 : NNReal) ≤ variance i := by
    intro i
    have hindex : Jvar ≤ start + (i : ℕ) :=
      hstartVar.trans (Nat.le_add_right start i)
    have hendpoint :
        harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
      exact (monotone_harperBlockEndpoint (by omega)).trans hy
    have hv :=
      (hJvar (start + (i : ℕ)) hindex y hendpoint t
        htLower htUpper).1.le
    exact_mod_cast hv
  have hupper : ∀ i, variance i ≤ (3 / 8 : NNReal) := by
    intro i
    have hindex : Jvar ≤ start + (i : ℕ) :=
      hstartVar.trans (Nat.le_add_right start i)
    have hendpoint :
        harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
      exact (monotone_harperBlockEndpoint (by omega)).trans hy
    have hv :=
      (hJvar (start + (i : ℕ)) hindex y hendpoint t
        htLower htUpper).2.le
    exact_mod_cast hv
  have hgaussian :
      (Measure.pi (fun i : Fin n ↦
        harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)).real
          (harperExpandedPartialSumBarrierSet lower upper
            (harperScheduledRelativeCellWidth start n)) ≤
        64 * (B + 2) / Real.sqrt (n : ℝ) := by
    simpa only [harperGaussianBlockLaw, variance] using!
      measureReal_pi_gaussian_expandedBarrier_le hn variance lower upper
        (harperScheduledRelativeCellWidth start n) hB0 hB hlower hupper
  exact hslice.trans
    (mul_le_mul_of_nonneg_left hgaussian (by positivity))

end Problem520
end Erdos
