import ErdosProblems.Erdos1002.FiniteShotConvergence
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit finite grids on the compact marked annulus

This file constructs the finite partition required by
`FiniteShotConvergence`.  In one real coordinate we use the genuinely
disjoint convention

`[x_i,x_{i+1})` for `i<n`, together with the terminal singleton `{b}`.

Taking products gives measurable rectangular cells with no ambiguity at a
grid boundary.  The signed `x` annulus is treated as two disjoint copies of
the interval grid.  Cell representatives are their lower-left corners (and
the right endpoint in a terminal coordinate), so their membership and the
mesh estimate are exact rather than almost-everywhere statements.
-/

open MeasureTheory Set
open scoped Topology

namespace Erdos1002

noncomputable section

/-! ## A one-dimensional half-open grid -/

/-- The `k`-th grid point in the subdivision of `[a,b]` into `n` equal
pieces.  It is defined for every natural `k`; the partition only uses
`k ≤ n`. -/
def intervalGridPoint (a b : ℝ) (n k : ℕ) : ℝ :=
  a + (k : ℝ) * (b - a) / (n : ℝ)

/-- There are `n` half-open intervals and one terminal singleton. -/
abbrev IntervalGridIndex (n : ℕ) := Fin (n + 1)

/-- The explicit cell convention: nonterminal cells are left closed and
right open, while the final cell consists of the right endpoint. -/
def intervalGridCell (a b : ℝ) (n : ℕ) (i : IntervalGridIndex n) : Set ℝ :=
  if i.1 < n then
    Ico (intervalGridPoint a b n i.1)
      (intervalGridPoint a b n (i.1 + 1))
  else
    {b}

/-- We use the left endpoint as representative; for the terminal singleton
this is exactly `b`. -/
def intervalGridCenter (a b : ℝ) (n : ℕ) (i : IntervalGridIndex n) : ℝ :=
  intervalGridPoint a b n i.1

theorem measurableSet_intervalGridCell
    (a b : ℝ) (n : ℕ) (i : IntervalGridIndex n) :
    MeasurableSet (intervalGridCell a b n i) := by
  unfold intervalGridCell
  split_ifs
  · exact measurableSet_Ico
  · exact MeasurableSet.singleton _

theorem intervalGridPoint_mem_Icc
    {a b : ℝ} {n k : ℕ} (hab : a ≤ b) (hn : 0 < n) (hk : k ≤ n) :
    intervalGridPoint a b n k ∈ Icc a b := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hratio0 : 0 ≤ (k : ℝ) / (n : ℝ) := div_nonneg hk0 hnR.le
  have hratio1 : (k : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hnR).2 hkR
  have hmul0 : 0 ≤ ((k : ℝ) / (n : ℝ)) * (b - a) :=
    mul_nonneg hratio0 hd
  have hmul1 : ((k : ℝ) / (n : ℝ)) * (b - a) ≤ b - a := by
    simpa using! mul_le_mul_of_nonneg_right hratio1 hd
  have hreassoc : (k : ℝ) * (b - a) / (n : ℝ) =
      ((k : ℝ) / (n : ℝ)) * (b - a) := by ring
  rw [intervalGridPoint]
  rw [hreassoc]
  constructor <;> nlinarith

theorem intervalGridPoint_succ_sub
    {a b : ℝ} {n k : ℕ} (hn : 0 < n) :
    intervalGridPoint a b n (k + 1) - intervalGridPoint a b n k =
      (b - a) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold intervalGridPoint
  push_cast
  field_simp
  ring

theorem intervalGridPoint_strictMono_step
    {a b : ℝ} {n k : ℕ} (hab : a < b) (hn : 0 < n) :
    intervalGridPoint a b n k < intervalGridPoint a b n (k + 1) := by
  have hwidth : 0 < (b - a) / (n : ℝ) := by
    exact div_pos (sub_pos.mpr hab) (by exact_mod_cast hn)
  linarith [intervalGridPoint_succ_sub (a := a) (b := b) (k := k) hn]

theorem intervalGridPoint_eq_right_of_not_lt
    {a b : ℝ} {n : ℕ} (hn : 0 < n) (i : IntervalGridIndex n)
    (hi : ¬ i.1 < n) :
    intervalGridPoint a b n i.1 = b := by
  have hin : i.1 = n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [intervalGridPoint, hin]
  field_simp
  ring

theorem intervalGridCell_subset_Icc
    {a b : ℝ} {n : ℕ} (hab : a < b) (hn : 0 < n)
    (i : IntervalGridIndex n) :
    intervalGridCell a b n i ⊆ Icc a b := by
  intro x hx
  unfold intervalGridCell at hx
  split_ifs at hx with hi
  · have hi1 : i.1 + 1 ≤ n := by omega
    have hleft := intervalGridPoint_mem_Icc hab.le hn (Nat.le_of_lt hi)
    have hright := intervalGridPoint_mem_Icc hab.le hn hi1
    exact ⟨hleft.1.trans hx.1, hx.2.le.trans hright.2⟩
  · have hxEq : x = b := by simpa only [mem_singleton_iff] using! hx
    subst x
    exact ⟨hab.le, le_rfl⟩

theorem intervalGridCenter_mem_cell
    {a b : ℝ} {n : ℕ} (hab : a < b) (hn : 0 < n)
    (i : IntervalGridIndex n) :
    intervalGridCenter a b n i ∈ intervalGridCell a b n i := by
  unfold intervalGridCenter intervalGridCell
  split_ifs with hi
  · exact ⟨le_rfl, intervalGridPoint_strictMono_step hab hn⟩
  · rw [intervalGridPoint_eq_right_of_not_lt hn i hi]
    rfl

/-- Membership in a nonterminal cell determines the natural floor of the
normalized coordinate. -/
theorem natFloor_normalized_eq_of_mem_intervalGridCell
    {a b x : ℝ} {n : ℕ} (hab : a < b) (hn : 0 < n)
    (i : IntervalGridIndex n) (hx : x ∈ intervalGridCell a b n i) :
    ⌊(n : ℝ) * (x - a) / (b - a)⌋₊ = i.1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < b - a := sub_pos.mpr hab
  have hxIcc := intervalGridCell_subset_Icc hab hn i hx
  have hy0 : 0 ≤ (n : ℝ) * (x - a) / (b - a) :=
    div_nonneg (mul_nonneg hnR.le (sub_nonneg.mpr hxIcc.1)) hd.le
  unfold intervalGridCell at hx
  split_ifs at hx with hi
  · apply (Nat.floor_eq_iff hy0).2
    constructor
    · apply (le_div_iff₀ hd).2
      have := hx.1
      unfold intervalGridPoint at this
      have hscaled : (i.1 : ℝ) * (b - a) / (n : ℝ) ≤ x - a := by
        linarith
      have hmul := (div_le_iff₀ hnR).1 hscaled
      simpa [mul_comm] using! hmul
    · apply (div_lt_iff₀ hd).2
      have := hx.2
      unfold intervalGridPoint at this
      push_cast at this
      have hscaled : x - a < ((i.1 : ℝ) + 1) * (b - a) / (n : ℝ) := by
        linarith
      have hmul := (lt_div_iff₀ hnR).1 hscaled
      simpa [mul_comm] using! hmul
  · have hiEq : i.1 = n := by omega
    have hxEq : x = b := by simpa only [mem_singleton_iff] using! hx
    subst x
    rw [hiEq]
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    have hd0 : b - a ≠ 0 := hd.ne'
    have hnormalized : (n : ℝ) * (b - a) / (b - a) = (n : ℝ) := by
      exact mul_div_cancel_right₀ (n : ℝ) hd0
    rw [hnormalized]
    exact Nat.floor_natCast n

/-- Every point of `[a,b]` lies in exactly one explicit cell. -/
theorem existsUnique_mem_intervalGridCell
    {a b x : ℝ} {n : ℕ} (hab : a < b) (hn : 0 < n)
    (hx : x ∈ Icc a b) :
    ∃! i : IntervalGridIndex n, x ∈ intervalGridCell a b n i := by
  let y : ℝ := (n : ℝ) * (x - a) / (b - a)
  let q : ℕ := ⌊y⌋₊
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < b - a := sub_pos.mpr hab
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (mul_nonneg hnR.le (sub_nonneg.mpr hx.1)) hd.le
  have hyN : y ≤ (n : ℝ) := by
    dsimp [y]
    apply (div_le_iff₀ hd).2
    have hxa : x - a ≤ b - a := sub_le_sub_right hx.2 a
    exact mul_le_mul_of_nonneg_left hxa hnR.le
  have hqle : q ≤ n := by
    have hfloor : (q : ℝ) ≤ y := by
      exact Nat.floor_le hy0
    exact_mod_cast hfloor.trans hyN
  let i : IntervalGridIndex n := ⟨q, Nat.lt_succ_of_le hqle⟩
  have hiMem : x ∈ intervalGridCell a b n i := by
    by_cases hq : q < n
    · unfold intervalGridCell
      change x ∈ if q < n then
        Ico (intervalGridPoint a b n q) (intervalGridPoint a b n (q + 1)) else {b}
      rw [if_pos hq]
      constructor
      · have hfloor : (q : ℝ) ≤ y := Nat.floor_le hy0
        dsimp [y] at hfloor
        unfold intervalGridPoint
        have hmul := (le_div_iff₀ hd).1 hfloor
        have hscaled : (q : ℝ) * (b - a) / (n : ℝ) ≤ x - a := by
          apply (div_le_iff₀ hnR).2
          simpa [mul_comm] using! hmul
        linarith
      · have hfloor : y < (q : ℝ) + 1 := Nat.lt_floor_add_one y
        dsimp [y] at hfloor
        unfold intervalGridPoint
        push_cast
        have hmul := (div_lt_iff₀ hd).1 hfloor
        have hscaled : x - a < ((q : ℝ) + 1) * (b - a) / (n : ℝ) := by
          apply (lt_div_iff₀ hnR).2
          simpa [mul_comm] using! hmul
        linarith
    · have hqEq : q = n := by omega
      have hyEq : y = (n : ℝ) := by
        apply le_antisymm hyN
        have hfloor : (q : ℝ) ≤ y := Nat.floor_le hy0
        simpa [hqEq] using! hfloor
      have hxEq : x = b := by
        dsimp [y] at hyEq
        have heq := (div_eq_iff hd.ne').1 hyEq
        nlinarith
      unfold intervalGridCell
      change x ∈ if q < n then
        Ico (intervalGridPoint a b n q) (intervalGridPoint a b n (q + 1)) else {b}
      rw [if_neg hq]
      simpa only [mem_singleton_iff]
  refine ⟨i, hiMem, ?_⟩
  intro j hj
  apply Fin.ext
  have hiFloor := natFloor_normalized_eq_of_mem_intervalGridCell hab hn i hiMem
  have hjFloor := natFloor_normalized_eq_of_mem_intervalGridCell hab hn j hj
  exact hjFloor.symm.trans hiFloor

/-- A cell point is strictly less than one grid width from its representative.
The terminal singleton has distance zero. -/
theorem dist_intervalGridCenter_lt_width
    {a b x : ℝ} {n : ℕ} (hab : a < b) (hn : 0 < n)
    (i : IntervalGridIndex n) (hx : x ∈ intervalGridCell a b n i) :
    dist x (intervalGridCenter a b n i) < (b - a) / (n : ℝ) := by
  have hwidth : 0 < (b - a) / (n : ℝ) :=
    div_pos (sub_pos.mpr hab) (by exact_mod_cast hn)
  unfold intervalGridCell at hx
  unfold intervalGridCenter
  split_ifs at hx with hi
  · rw [Real.dist_eq]
    have hnonneg : 0 ≤ x - intervalGridPoint a b n i.1 := sub_nonneg.mpr hx.1
    rw [abs_of_nonneg hnonneg]
    linarith [hx.2,
      intervalGridPoint_succ_sub (a := a) (b := b) (k := i.1) hn]
  · have hxEq : x = b := by simpa only [mem_singleton_iff] using! hx
    rw [hxEq, intervalGridPoint_eq_right_of_not_lt hn i hi, dist_self]
    exact hwidth

/-! ## The signed three-coordinate annular grid -/

/-- A finite index consists of the time cell, a sign, the signed-coordinate
cell, and the torus-coordinate cell. -/
structure AnnularGridIndex (n : ℕ) where
  time : IntervalGridIndex n
  sign : Bool
  signed : IntervalGridIndex n
  torus : IntervalGridIndex n
deriving DecidableEq, Fintype

def signedGridLower (ε A : ℝ) (s : Bool) : ℝ :=
  if s then ε else -A

def signedGridUpper (ε A : ℝ) (s : Bool) : ℝ :=
  if s then A else -ε

theorem signedGridLower_lt_upper
    {ε A : ℝ} (hεA : ε < A) (s : Bool) :
    signedGridLower ε A s < signedGridUpper ε A s := by
  cases s <;> simp [signedGridLower, signedGridUpper, hεA]

/-- The actual rectangular marked-state cell. -/
def annularGridCell (ε A : ℝ) (n : ℕ) (i : AnnularGridIndex n) :
    Set (ℝ × ℝ × ℝ) :=
  intervalGridCell 0 1 n i.time ×ˢ
    (intervalGridCell (signedGridLower ε A i.sign)
        (signedGridUpper ε A i.sign) n i.signed ×ˢ
      intervalGridCell 0 1 n i.torus)

/-- The lower-left representative of a rectangular cell. -/
def annularGridCenter (ε A : ℝ) (n : ℕ) (i : AnnularGridIndex n) :
    ℝ × ℝ × ℝ :=
  (intervalGridCenter 0 1 n i.time,
    intervalGridCenter (signedGridLower ε A i.sign)
      (signedGridUpper ε A i.sign) n i.signed,
    intervalGridCenter 0 1 n i.torus)

theorem measurableSet_annularGridCell
    (ε A : ℝ) (n : ℕ) (i : AnnularGridIndex n) :
    MeasurableSet (annularGridCell ε A n i) := by
  exact (measurableSet_intervalGridCell 0 1 n i.time).prod
    ((measurableSet_intervalGridCell _ _ n i.signed).prod
      (measurableSet_intervalGridCell 0 1 n i.torus))

/-! The following two lemmas record the continuity-set property needed by
point-process convergence.  They apply to the actual topological boundary,
not merely to the finitely many endpoints listed informally. -/

theorem volume_frontier_intervalGridCell_eq_zero
    {a b : ℝ} {n : ℕ} (hab : a < b) (hn : 0 < n)
    (i : IntervalGridIndex n) :
    volume (frontier (intervalGridCell a b n i)) = 0 := by
  unfold intervalGridCell
  split_ifs with hi
  · rw [frontier_Ico (intervalGridPoint_strictMono_step hab hn)]
    exact ((Set.finite_singleton _).insert _).measure_zero volume
  · apply MeasureTheory.measure_mono_null frontier_subset_closure
    rw [closure_singleton, Real.volume_singleton]

theorem volume_frontier_prod_eq_zero
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasureSpace X] [MeasureSpace Y] [SFinite (volume : Measure Y)]
    {s : Set X} {t : Set Y}
    (hs : volume (frontier s) = 0) (ht : volume (frontier t) = 0) :
    volume (frontier (s ×ˢ t)) = 0 := by
  rw [frontier_prod_eq]
  apply MeasureTheory.measure_union_null
  · rw [Measure.volume_eq_prod, Measure.prod_prod, ht, mul_zero]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, hs, zero_mul]

/-- Every explicit three-dimensional cell is a Lebesgue continuity set. -/
theorem volume_frontier_annularGridCell_eq_zero
    {ε A : ℝ} (hεA : ε < A) {n : ℕ} (hn : 0 < n)
    (i : AnnularGridIndex n) :
    volume (frontier (annularGridCell ε A n i)) = 0 := by
  apply volume_frontier_prod_eq_zero
  · exact volume_frontier_intervalGridCell_eq_zero zero_lt_one hn i.time
  · apply volume_frontier_prod_eq_zero
    · exact volume_frontier_intervalGridCell_eq_zero
        (signedGridLower_lt_upper hεA i.sign) hn i.signed
    · exact volume_frontier_intervalGridCell_eq_zero zero_lt_one hn i.torus

/-- Hence the cells are continuity sets for every limiting intensity which
is absolutely continuous with respect to three-dimensional Lebesgue measure
(in particular for any intensity given by a Lebesgue density). -/
theorem measure_frontier_annularGridCell_eq_zero_of_absolutelyContinuous
    {ε A : ℝ} (hεA : ε < A) {n : ℕ} (hn : 0 < n)
    (i : AnnularGridIndex n) (μ : Measure (ℝ × ℝ × ℝ))
    (hμ : μ.AbsolutelyContinuous volume) :
    μ (frontier (annularGridCell ε A n i)) = 0 :=
  hμ (volume_frontier_annularGridCell_eq_zero hεA hn i)

theorem annularGridCell_subset_compactAnnularMarkedRegion
    {ε A : ℝ} (hεA : ε < A) {n : ℕ} (hn : 0 < n)
    (i : AnnularGridIndex n) :
    annularGridCell ε A n i ⊆ compactAnnularMarkedRegion ε A := by
  intro z hz
  refine ⟨intervalGridCell_subset_Icc zero_lt_one hn i.time hz.1, ?_,
    intervalGridCell_subset_Icc zero_lt_one hn i.torus hz.2.2⟩
  cases hs : i.sign
  · left
    simpa [signedGridLower, signedGridUpper, hs] using!
      intervalGridCell_subset_Icc (signedGridLower_lt_upper hεA i.sign) hn
        i.signed hz.2.1
  · right
    simpa [signedGridLower, signedGridUpper, hs] using!
      intervalGridCell_subset_Icc (signedGridLower_lt_upper hεA i.sign) hn
        i.signed hz.2.1

theorem annularGridCenter_mem_cell
    {ε A : ℝ} (hεA : ε < A) {n : ℕ} (hn : 0 < n)
    (i : AnnularGridIndex n) :
    annularGridCenter ε A n i ∈ annularGridCell ε A n i := by
  exact ⟨intervalGridCenter_mem_cell zero_lt_one hn i.time,
    intervalGridCenter_mem_cell (signedGridLower_lt_upper hεA i.sign) hn i.signed,
    intervalGridCenter_mem_cell zero_lt_one hn i.torus⟩

theorem annularGridCenter_mem_compactAnnularMarkedRegion
    {ε A : ℝ} (hεA : ε < A) {n : ℕ} (hn : 0 < n)
    (i : AnnularGridIndex n) :
    annularGridCenter ε A n i ∈ compactAnnularMarkedRegion ε A :=
  annularGridCell_subset_compactAnnularMarkedRegion hεA hn i
    (annularGridCenter_mem_cell hεA hn i)

theorem existsUnique_mem_annularGridCell
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A) {n : ℕ} (hn : 0 < n)
    {z : ℝ × ℝ × ℝ} (hz : z ∈ compactAnnularMarkedRegion ε A) :
    ∃! i : AnnularGridIndex n, z ∈ annularGridCell ε A n i := by
  obtain ⟨it, hit, hitUnique⟩ :=
    existsUnique_mem_intervalGridCell zero_lt_one hn hz.1
  obtain ⟨iu, hiu, hiuUnique⟩ :=
    existsUnique_mem_intervalGridCell zero_lt_one hn hz.2.2
  rcases hz.2.1 with hxneg | hxpos
  · obtain ⟨ix, hix, hixUnique⟩ :=
      existsUnique_mem_intervalGridCell (by linarith : -A < -ε) hn hxneg
    let i : AnnularGridIndex n := ⟨it, false, ix, iu⟩
    refine ⟨i, ?_, ?_⟩
    · exact ⟨hit, hix, hiu⟩
    · intro j hj
      have ht : j.time = it := hitUnique j.time hj.1
      have hu : j.torus = iu := hiuUnique j.torus hj.2.2
      have hs : j.sign = false := by
        cases hjs : j.sign
        · rfl
        · have hxj := intervalGridCell_subset_Icc
            (signedGridLower_lt_upper hεA j.sign) hn j.signed hj.2.1
          simp only [Bool.true_eq_false] at hxj
          have hneg : z.2.1 < 0 :=
            lt_of_le_of_lt hxneg.2 (neg_lt_zero.mpr hε)
          have hpos : 0 < z.2.1 := lt_of_lt_of_le hε hxj.1
          exact (not_lt_of_ge hpos.le hneg).elim
      have hx : j.signed = ix := by
        apply hixUnique
        simpa [hs, signedGridLower, signedGridUpper] using! hj.2.1
      cases j
      simp_all [i]
  · obtain ⟨ix, hix, hixUnique⟩ :=
      existsUnique_mem_intervalGridCell hεA hn hxpos
    let i : AnnularGridIndex n := ⟨it, true, ix, iu⟩
    refine ⟨i, ?_, ?_⟩
    · exact ⟨hit, hix, hiu⟩
    · intro j hj
      have ht : j.time = it := hitUnique j.time hj.1
      have hu : j.torus = iu := hiuUnique j.torus hj.2.2
      have hs : j.sign = true := by
        cases hjs : j.sign
        · have hxj := intervalGridCell_subset_Icc
            (signedGridLower_lt_upper hεA j.sign) hn j.signed hj.2.1
          simp only [Bool.false_eq_true] at hxj
          have hneg : z.2.1 < 0 :=
            lt_of_le_of_lt hxj.2 (neg_lt_zero.mpr hε)
          have hpos : 0 < z.2.1 := lt_of_lt_of_le hε hxpos.1
          exact (not_lt_of_ge hpos.le hneg).elim
        · rfl
      have hx : j.signed = ix := by
        apply hixUnique
        simpa [hs, signedGridLower, signedGridUpper] using! hj.2.1
      cases j
      simp_all [i]

/-- Coordinatewise mesh control implies the product-metric mesh control. -/
theorem dist_annularGridCenter_lt
    {ε A δ : ℝ} (hεA : ε < A) {n : ℕ} (hn : 0 < n)
    (htime : (1 : ℝ) / n < δ) (hsigned : (A - ε) / n < δ)
    (i : AnnularGridIndex n) {z : ℝ × ℝ × ℝ}
    (hz : z ∈ annularGridCell ε A n i) :
    dist z (annularGridCenter ε A n i) < δ := by
  have ht := dist_intervalGridCenter_lt_width zero_lt_one hn i.time hz.1
  have hu := dist_intervalGridCenter_lt_width zero_lt_one hn i.torus hz.2.2
  have hx := dist_intervalGridCenter_lt_width
    (signedGridLower_lt_upper hεA i.sign) hn i.signed hz.2.1
  have hwidth : (signedGridUpper ε A i.sign - signedGridLower ε A i.sign) /
      (n : ℝ) = (A - ε) / n := by
    cases i.sign
    · simp [signedGridLower, signedGridUpper]
      ring
    · simp [signedGridLower, signedGridUpper]
  rw [hwidth] at hx
  norm_num at ht hu
  have htime' : (n : ℝ)⁻¹ < δ := by simpa [one_div] using! htime
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_lt (lt_trans ht htime')
    (max_lt (lt_trans hx hsigned) (lt_trans hu htime'))

/-- Arbitrarily fine explicit annular grids exist. -/
theorem exists_annularGrid_mesh_lt
    {ε A δ : ℝ} (hεA : ε < A) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧
      ∀ (i : AnnularGridIndex n) (z : ℝ × ℝ × ℝ),
        z ∈ annularGridCell ε A n i →
          dist z (annularGridCenter ε A n i) < δ := by
  let M : ℝ := max 1 (A - ε)
  obtain ⟨n, hnLarge⟩ := exists_nat_gt (M / δ)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left 1 (A - ε))
  have hnR : (0 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le (div_pos hM hδ) hnLarge.le
  have hn : 0 < n := by exact_mod_cast hnR
  have hMnd : M < (n : ℝ) * δ := by
    exact (div_lt_iff₀ hδ).1 hnLarge
  have htime : (1 : ℝ) / n < δ := by
    apply (div_lt_iff₀ hnR).2
    nlinarith [le_max_left (1 : ℝ) (A - ε)]
  have hsigned : (A - ε) / n < δ := by
    apply (div_lt_iff₀ hnR).2
    nlinarith [le_max_right (1 : ℝ) (A - ε)]
  refine ⟨n, hn, ?_⟩
  intro i z hz
  exact dist_annularGridCenter_lt hεA hn htime hsigned i hz

/-! ## Direct closure of the finite-shot approximation input -/

/-- The abstract cell-radius statement from `FiniteShotConvergence` can be
instantiated by the explicit measurable rectangular grid constructed above.
Thus no partition or representative remains to be chosen externally. -/
theorem exists_explicit_annularGrid_shot_approximation
    {N : ℕ} (hN : 2 ≤ N) {ε A η : ℝ}
    (hε : 0 < ε) (hεA : ε < A) (hη : 0 < η) :
    ∃ n : ℕ, 0 < n ∧
      ∀ α,
        |annularMarkedShotFunctional N ε A α -
            finiteCellMarkedShotApproximation N N
              (annularGridCell ε A n)
              (fun i ↦ markedShotKernel (annularGridCenter ε A n i)) α| ≤
          η * (markedResonanceCount N N
            (compactAnnularMarkedRegion ε A) α : ℝ) := by
  obtain ⟨δ, hδ, hkernel⟩ :=
    exists_uniform_cell_radius_markedShotKernel hε hη
  obtain ⟨n, hn, hmesh⟩ := exists_annularGrid_mesh_lt hεA hδ
  refine ⟨n, hn, ?_⟩
  intro α
  apply abs_annularMarkedShotFunctional_sub_finiteCellApproximation_le_count
    hN hε.le (annularGridCell ε A n)
      (fun i ↦ markedShotKernel (annularGridCenter ε A n i))
    (annularGridCell_subset_compactAnnularMarkedRegion hεA hn)
    (fun z hz ↦ existsUnique_mem_annularGridCell hε hεA hn hz)
  intro i z hz
  exact (hkernel z
    (annularGridCell_subset_compactAnnularMarkedRegion hεA hn i hz)
    (annularGridCenter ε A n i)
    (annularGridCenter_mem_compactAnnularMarkedRegion hεA hn i)
    (hmesh i z hz)).le

end

end Erdos1002
