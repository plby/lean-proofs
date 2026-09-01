/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos989.UpperGeometry
import ErdosProblems.Erdos989.UpperPeriodic

/-!
# A finite net of disk centres for the fixed-radius upper construction

For a prescribed radius `r`, put `q = ⌈r⌉` and `L = ⌈2r+4⌉`.  The
period square is sampled on the mesh `1/q`; both the inner and outer disk in
the deterministic sandwich are retained as events.  Thus the event family is

`(Fin (L*q) × Fin (L*q)) × Bool`.

This file proves its exact cardinality and the convenient bound
`#events ≤ 196 r⁴` for `r ≥ 2`.  It also proves that, after translation by
an integral multiple of the period, every centre lies within `√2/q` of one
of the mesh centres.  The last theorem combines this with the disk sandwich
from `UpperGeometry`.
-/

namespace Erdos989
namespace FixedRadiusUpper

open GlobalSelection UpperGeometry

noncomputable section

/-- Number of subdivisions of each unit interval at radius `r`. -/
def radiusGridSize (r : ℝ) : ℕ := ⌈r⌉₊

/-- Side length of the square period used at radius `r`. -/
def radiusPeriodLength (r : ℝ) : ℕ := ⌈2 * r + 4⌉₊

/-- Mesh points in one square period. -/
abbrev CenterNetIndex (L q : ℕ) := Fin (L * q) × Fin (L * q)

/-- The two events at a mesh centre: the inner and outer sandwich disks. -/
abbrev CenterNetEvent (L q : ℕ) := CenterNetIndex L q × Bool

/-- A mesh index interpreted as a point in the Euclidean plane. -/
def centerNetPoint (q : ℕ) {N : ℕ} (u : Fin N × Fin N) : Plane :=
  pairToEuclideanPlane (((u.1 : ℝ) / q), ((u.2 : ℝ) / q))

/-- Centre attached to an inner/outer event. -/
def centerNetEventCenter (q : ℕ) {L : ℕ} (e : CenterNetEvent L q) : Plane :=
  centerNetPoint q e.1

/-- Radius attached to an inner/outer event.  `false` is the inner disk and
`true` is the outer disk. -/
def centerNetEventRadius (r : ℝ) (q : ℕ) {L : ℕ}
    (e : CenterNetEvent L q) : ℝ :=
  if e.2 then r + Real.sqrt 2 / q else r - Real.sqrt 2 / q

@[simp] theorem centerNetPoint_apply_zero (q : ℕ) {N : ℕ}
    (u : Fin N × Fin N) : centerNetPoint q u 0 = (u.1 : ℝ) / q := by
  rfl

@[simp] theorem centerNetPoint_apply_one (q : ℕ) {N : ℕ}
    (u : Fin N × Fin N) : centerNetPoint q u 1 = (u.2 : ℝ) / q := by
  rfl

/-- Exact size of the inner/outer event family. -/
theorem card_centerNetEvent (L q : ℕ) :
    Fintype.card (CenterNetEvent L q) = 2 * (L * q) ^ 2 := by
  simp [CenterNetEvent, CenterNetIndex, Fintype.card_prod]
  ring

theorem radiusGridSize_pos {r : ℝ} (hr : 0 < r) :
    0 < radiusGridSize r := by
  exact Nat.ceil_pos.mpr hr

theorem radiusPeriodLength_pos {r : ℝ} (hr : 0 ≤ r) :
    0 < radiusPeriodLength r := by
  apply Nat.ceil_pos.mpr
  linarith

theorem radius_le_radiusGridSize (r : ℝ) :
    r ≤ (radiusGridSize r : ℝ) :=
  Nat.le_ceil r

/-- At radii at least two the centre-net error is at most one. -/
theorem sqrt_two_div_radiusGridSize_le_one {r : ℝ} (hr : 2 ≤ r) :
    Real.sqrt 2 / radiusGridSize r ≤ 1 := by
  have hq : 0 < (radiusGridSize r : ℝ) := by
    exact_mod_cast radiusGridSize_pos (by linarith : 0 < r)
  apply (div_le_one hq).2
  calc
    Real.sqrt 2 ≤ 2 := by norm_num
    _ ≤ r := hr
    _ ≤ radiusGridSize r := radius_le_radiusGridSize r

/-- Both sandwich disks have diameter strictly below the period. -/
theorem centerNetEventRadius_diameter_lt_period {r : ℝ} (hr : 2 ≤ r)
    (e : CenterNetEvent (radiusPeriodLength r) (radiusGridSize r)) :
    2 * centerNetEventRadius r (radiusGridSize r) e <
      (radiusPeriodLength r : ℝ) := by
  have heta := sqrt_two_div_radiusGridSize_le_one hr
  have hperiod : 2 * r + 4 ≤ (radiusPeriodLength r : ℝ) :=
    Nat.le_ceil (2 * r + 4)
  have heta0 : 0 ≤ Real.sqrt 2 / (radiusGridSize r : ℝ) :=
    div_nonneg (Real.sqrt_nonneg _) (by positivity)
  simp only [centerNetEventRadius]
  split_ifs <;> nlinarith

/-- The mesh has at most `3r/2` subdivisions per unit interval when `r ≥ 2`. -/
theorem radiusGridSize_le_three_halves_mul {r : ℝ} (hr : 2 ≤ r) :
    (radiusGridSize r : ℝ) ≤ (3 / 2 : ℝ) * r := by
  have hr0 : 0 ≤ r := by linarith
  have hceil : (radiusGridSize r : ℝ) < r + 1 :=
    Nat.ceil_lt_add_one hr0
  linarith

/-- The chosen period is at most `9r/2` when `r ≥ 2`. -/
theorem radiusPeriodLength_le_nine_halves_mul {r : ℝ} (hr : 2 ≤ r) :
    (radiusPeriodLength r : ℝ) ≤ (9 / 2 : ℝ) * r := by
  have harg : 0 ≤ 2 * r + 4 := by linarith
  have hceil : (radiusPeriodLength r : ℝ) < (2 * r + 4) + 1 :=
    Nat.ceil_lt_add_one harg
  linarith

/-- The finite family used in the union bound has polynomial size.  The
constant `196` leaves ample room for all rounding at the endpoint `r = 2`. -/
theorem card_centerNetEvent_radius_le {r : ℝ} (hr : 2 ≤ r) :
    (Fintype.card
        (CenterNetEvent (radiusPeriodLength r) (radiusGridSize r)) : ℝ)
      ≤ 196 * r ^ 4 := by
  rw [card_centerNetEvent]
  push_cast
  have hq := radiusGridSize_le_three_halves_mul hr
  have hL := radiusPeriodLength_le_nine_halves_mul hr
  have hr0 : 0 ≤ r := by linarith
  have hq0 : 0 ≤ (radiusGridSize r : ℝ) := by positivity
  have hL0 : 0 ≤ (radiusPeriodLength r : ℝ) := by positivity
  have hprod :
      (radiusPeriodLength r : ℝ) * radiusGridSize r ≤
        (27 / 4 : ℝ) * r ^ 2 := by
    calc
      (radiusPeriodLength r : ℝ) * radiusGridSize r ≤
          ((9 / 2 : ℝ) * r) * ((3 / 2 : ℝ) * r) :=
        mul_le_mul hL hq hq0 (mul_nonneg (by norm_num) hr0)
      _ = (27 / 4 : ℝ) * r ^ 2 := by ring
  have hsquare :
      ((radiusPeriodLength r : ℝ) * radiusGridSize r) ^ 2 ≤
        ((27 / 4 : ℝ) * r ^ 2) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hL0 hq0)
      (mul_nonneg (by norm_num) (sq_nonneg r))).2 hprod
  nlinarith [sq_nonneg (r ^ 2)]

/-! ## Reducing an arbitrary centre to one period -/

/-- Translation by the integral period vector `L * k`. -/
def periodTranslation (L : ℕ) (k : PlaneCell) : Plane :=
  pairToEuclideanPlane ((L : ℝ) * k.1, (L : ℝ) * k.2)

/-- The integer period quotient of a point, coordinate by coordinate. -/
def centerPeriodQuotient (L : ℕ) (x : Plane) : PlaneCell :=
  (⌊x 0 / (L : ℝ)⌋, ⌊x 1 / (L : ℝ)⌋)

/-- The representative of `x` in the half-open period square `[0,L)²`. -/
def reduceCenter (L : ℕ) (x : Plane) : Plane :=
  x - periodTranslation L (centerPeriodQuotient L x)

@[simp] theorem periodTranslation_apply_zero (L : ℕ) (k : PlaneCell) :
    periodTranslation L k 0 = (L : ℝ) * k.1 := by
  rfl

@[simp] theorem periodTranslation_apply_one (L : ℕ) (k : PlaneCell) :
    periodTranslation L k 1 = (L : ℝ) * k.2 := by
  rfl

@[simp] theorem reduceCenter_apply_zero (L : ℕ) (x : Plane) :
    reduceCenter L x 0 = x 0 - (L : ℝ) * ⌊x 0 / (L : ℝ)⌋ := by
  rfl

@[simp] theorem reduceCenter_apply_one (L : ℕ) (x : Plane) :
    reduceCenter L x 1 = x 1 - (L : ℝ) * ⌊x 1 / (L : ℝ)⌋ := by
  rfl

/-- Exact decomposition into a fundamental-domain representative and a
period translation. -/
theorem reduceCenter_add_periodTranslation (L : ℕ) (x : Plane) :
    reduceCenter L x + periodTranslation L (centerPeriodQuotient L x) = x := by
  ext i
  fin_cases i <;> simp [reduceCenter]

/-- Coordinate bounds for the half-open fundamental-domain representative. -/
theorem reduceCenter_mem_fundamentalSquare {L : ℕ} (hL : 0 < L) (x : Plane) :
    0 ≤ reduceCenter L x 0 ∧ reduceCenter L x 0 < L ∧
      0 ≤ reduceCenter L x 1 ∧ reduceCenter L x 1 < L := by
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have coord (t : ℝ) :
      0 ≤ t - (L : ℝ) * ⌊t / (L : ℝ)⌋ ∧
        t - (L : ℝ) * ⌊t / (L : ℝ)⌋ < L := by
    have hlo := Int.floor_le (t / (L : ℝ))
    have hhi := Int.lt_floor_add_one (t / (L : ℝ))
    have hlo' : (L : ℝ) * (⌊t / (L : ℝ)⌋ : ℝ) ≤ t := by
      have := (le_div_iff₀ hLR).mp hlo
      nlinarith
    have hhi' : t < (L : ℝ) * ((⌊t / (L : ℝ)⌋ : ℝ) + 1) := by
      have := (div_lt_iff₀ hLR).mp hhi
      nlinarith
    constructor <;> nlinarith
  have h0 := coord (x 0)
  have h1 := coord (x 1)
  exact ⟨by simpa only [reduceCenter_apply_zero] using h0.1,
    by simpa only [reduceCenter_apply_zero, Nat.cast_ofNat] using h0.2,
    by simpa only [reduceCenter_apply_one] using h1.1,
    by simpa only [reduceCenter_apply_one, Nat.cast_ofNat] using h1.2⟩

/-! ## Approximation by the `1/q` mesh -/

/-- Every point of `[0,L)²` is within `√2/q` of a mesh point indexed by
`Fin (L*q) × Fin (L*q)`. -/
theorem exists_centerNetPoint_near_of_mem_fundamentalSquare
    {L q : ℕ} (hq : 0 < q) (x : Plane)
    (hx : 0 ≤ x 0 ∧ x 0 < L ∧ 0 ≤ x 1 ∧ x 1 < L) :
    ∃ u : CenterNetIndex L q,
      dist x (centerNetPoint q u) ≤ Real.sqrt 2 / q := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let za : ℤ := ⌊(q : ℝ) * x 0⌋
  let zb : ℤ := ⌊(q : ℝ) * x 1⌋
  have hza0 : 0 ≤ za := by
    change 0 ≤ ⌊(q : ℝ) * x 0⌋
    rw [Int.floor_nonneg]
    exact mul_nonneg (by positivity) hx.1
  have hzb0 : 0 ≤ zb := by
    change 0 ≤ ⌊(q : ℝ) * x 1⌋
    rw [Int.floor_nonneg]
    exact mul_nonneg (by positivity) hx.2.2.1
  have hzaN : za < (L * q : ℕ) := by
    change ⌊(q : ℝ) * x 0⌋ < (L * q : ℕ)
    rw [Int.floor_lt]
    push_cast
    nlinarith [mul_lt_mul_of_pos_left hx.2.1 hqR]
  have hzbN : zb < (L * q : ℕ) := by
    change ⌊(q : ℝ) * x 1⌋ < (L * q : ℕ)
    rw [Int.floor_lt]
    push_cast
    nlinarith [mul_lt_mul_of_pos_left hx.2.2.2 hqR]
  let a : Fin (L * q) := ⟨za.toNat, (Int.toNat_lt hza0).2 hzaN⟩
  let b : Fin (L * q) := ⟨zb.toNat, (Int.toNat_lt hzb0).2 hzbN⟩
  let u : CenterNetIndex L q := (a, b)
  have ha_cast : (a : ℝ) = (za : ℝ) := by
    change (za.toNat : ℝ) = (za : ℝ)
    exact_mod_cast Int.toNat_of_nonneg hza0
  have hb_cast : (b : ℝ) = (zb : ℝ) := by
    change (zb.toNat : ℝ) = (zb : ℝ)
    exact_mod_cast Int.toNat_of_nonneg hzb0
  have hq_div_a : (q : ℝ) * ((a : ℝ) / q) = a := by
    field_simp
  have hq_div_b : (q : ℝ) * ((b : ℝ) / q) = b := by
    field_simp
  have hq_inv : (q : ℝ) * (1 / (q : ℝ)) = 1 := by
    field_simp
  have ha_floor := Int.floor_le ((q : ℝ) * x 0)
  have hb_floor := Int.floor_le ((q : ℝ) * x 1)
  have ha_next := Int.lt_floor_add_one ((q : ℝ) * x 0)
  have hb_next := Int.lt_floor_add_one ((q : ℝ) * x 1)
  have ha_le : (a : ℝ) / q ≤ x 0 := by
    rw [ha_cast]
    have hfloor : (za : ℝ) ≤ (q : ℝ) * x 0 := by
      simpa [za] using ha_floor
    have hdiv : (q : ℝ) * ((za : ℝ) / q) = za := by field_simp
    nlinarith
  have hb_le : (b : ℝ) / q ≤ x 1 := by
    rw [hb_cast]
    have hfloor : (zb : ℝ) ≤ (q : ℝ) * x 1 := by
      simpa [zb] using hb_floor
    have hdiv : (q : ℝ) * ((zb : ℝ) / q) = zb := by field_simp
    nlinarith
  have ha_lt : x 0 < (a : ℝ) / q + 1 / q := by
    have hnext : (q : ℝ) * x 0 < (za : ℝ) + 1 := by
      dsimp [za]
      exact ha_next
    nlinarith
  have hb_lt : x 1 < (b : ℝ) / q + 1 / q := by
    have hnext : (q : ℝ) * x 1 < (zb : ℝ) + 1 := by
      dsimp [zb]
      exact hb_next
    nlinarith
  have ha_abs : |x 0 - (a : ℝ) / q| ≤ 1 / q := by
    rw [abs_of_nonneg (sub_nonneg.mpr ha_le)]
    linarith
  have hb_abs : |x 1 - (b : ℝ) / q| ≤ 1 / q := by
    rw [abs_of_nonneg (sub_nonneg.mpr hb_le)]
    linarith
  have hinv0 : 0 ≤ 1 / (q : ℝ) := by positivity
  have ha_sq : |x 0 - (a : ℝ) / q| ^ 2 ≤ (1 / (q : ℝ)) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hinv0).2 ha_abs
  have hb_sq : |x 1 - (b : ℝ) / q| ^ 2 ≤ (1 / (q : ℝ)) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hinv0).2 hb_abs
  refine ⟨u, ?_⟩
  rw [EuclideanSpace.dist_eq]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact div_nonneg (Real.sqrt_nonneg _) (by positivity)
  · simp only [Fin.sum_univ_two, Real.dist_eq, centerNetPoint_apply_zero,
      centerNetPoint_apply_one, u]
    calc
      |x 0 - (a : ℝ) / q| ^ 2 + |x 1 - (b : ℝ) / q| ^ 2 ≤
          2 * (1 / (q : ℝ)) ^ 2 := by linarith
      _ = (Real.sqrt 2 / q) ^ 2 := by
        rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        ring

/-- Every centre becomes close to a mesh centre after an integral period
translation. -/
theorem exists_centerNetPoint_add_periodTranslation_near
    {L q : ℕ} (hL : 0 < L) (hq : 0 < q) (x : Plane) :
    ∃ u : CenterNetIndex L q, ∃ k : PlaneCell,
      dist x (centerNetPoint q u + periodTranslation L k) ≤
        Real.sqrt 2 / q := by
  let k := centerPeriodQuotient L x
  obtain ⟨u, hu⟩ := exists_centerNetPoint_near_of_mem_fundamentalSquare hq
    (reduceCenter L x) (reduceCenter_mem_fundamentalSquare hL x)
  refine ⟨u, k, ?_⟩
  have hx : reduceCenter L x + periodTranslation L k = x :=
    reduceCenter_add_periodTranslation L x
  rw [← hx, dist_add_right]
  exact hu

/-- Deterministic transfer from the nearby net centre to inner and outer
disks.  This is the exact squeeze used after controlling the two net events. -/
theorem closedBall_centerNet_sandwich
    {L q : ℕ} (hL : 0 < L) (hq : 0 < q)
    (x : Plane) (r : ℝ) :
    ∃ u : CenterNetIndex L q, ∃ k : PlaneCell,
      Metric.closedBall (centerNetPoint q u + periodTranslation L k)
          (r - Real.sqrt 2 / q) ⊆ Metric.closedBall x r ∧
        Metric.closedBall x r ⊆
          Metric.closedBall (centerNetPoint q u + periodTranslation L k)
            (r + Real.sqrt 2 / q) := by
  obtain ⟨u, k, huk⟩ := exists_centerNetPoint_add_periodTranslation_near hL hq x
  exact ⟨u, k, closedBall_net_sandwich huk⟩

/-! ## Period invariance of the selected count -/

/-- Shift an integer cell by an integral multiple of the period. -/
def periodShiftCell (L : ℕ) (k cell : PlaneCell) : PlaneCell :=
  (cell.1 + (L : ℤ) * k.1, cell.2 + (L : ℤ) * k.2)

@[simp] theorem periodShiftCell_neg (L : ℕ) (k cell : PlaneCell) :
    periodShiftCell L (-k.1, -k.2) (periodShiftCell L k cell) = cell := by
  apply Prod.ext <;> simp [periodShiftCell]

@[simp] theorem periodClass_periodShiftCell (L : ℕ) (k cell : PlaneCell) :
    periodClass L (periodShiftCell L k cell) = periodClass L cell := by
  apply Prod.ext <;> simp [periodClass, periodShiftCell]

/-- A periodic selected point shifts by exactly the corresponding geometric
period vector. -/
theorem periodicPoint_periodShiftCell
    (L q : ℕ) (omega : PeriodCell L → GridCandidate q)
    (k cell : PlaneCell) :
    periodicPoint L q omega (periodShiftCell L k cell) =
      periodicPoint L q omega cell + periodTranslation L k := by
  have hclass : periodClass L (periodShiftCell L k cell) = periodClass L cell :=
    periodClass_periodShiftCell L k cell
  ext i
  fin_cases i
  · change
      ((periodShiftCell L k cell).1 : ℝ) +
          (midpointOffset q (omega (periodClass L (periodShiftCell L k cell)))).1 =
        (cell.1 : ℝ) + (midpointOffset q (omega (periodClass L cell))).1 +
          (L : ℝ) * (k.1 : ℝ)
    rw [hclass]
    simp only [periodShiftCell, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring
  · change
      ((periodShiftCell L k cell).2 : ℝ) +
          (midpointOffset q (omega (periodClass L (periodShiftCell L k cell)))).2 =
        (cell.2 : ℝ) + (midpointOffset q (omega (periodClass L cell))).2 +
          (L : ℝ) * (k.2 : ℝ)
    rw [hclass]
    simp only [periodShiftCell, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring

/-- The infinite periodic disk count is invariant when its centre is shifted
by an integral period vector. -/
theorem selectedDiskCount_periodTranslation
    (L q : ℕ) (omega : PeriodCell L → GridCandidate q)
    (center : Plane) (radius : ℝ) (k : PlaneCell) :
    selectedDiskCount (latticeLocation (midpointOffset q))
        (periodicSelection L q omega)
        (center + periodTranslation L k) radius =
      selectedDiskCount (latticeLocation (midpointOffset q))
        (periodicSelection L q omega) center radius := by
  let S : Set PlaneCell :=
    {cell | periodicPoint L q omega cell ∈ Metric.closedBall center radius}
  let T : Set PlaneCell :=
    {cell | periodicPoint L q omega cell ∈
      Metric.closedBall (center + periodTranslation L k) radius}
  have hmap : ∀ cell, cell ∈ S → periodShiftCell L k cell ∈ T := by
    intro cell hcell
    rw [Set.mem_ofPred_eq, periodicPoint_periodShiftCell, Metric.mem_closedBall]
    rw [dist_add_right]
    exact hcell
  have hinj : Function.Injective (periodShiftCell L k) := by
    intro a b hab
    have := congrArg (periodShiftCell L (-k.1, -k.2)) hab
    simpa using this
  have hsurj : ∀ cell, cell ∈ T →
      ∃ pre, ∃ hpre : pre ∈ S, periodShiftCell L k pre = cell := by
    intro cell hcell
    let pre := periodShiftCell L (-k.1, -k.2) cell
    have hpreShift : periodShiftCell L k pre = cell := by
      apply Prod.ext <;> simp [pre, periodShiftCell]
    refine ⟨pre, ?_, hpreShift⟩
    have hp := hcell
    rw [Set.mem_ofPred_eq, ← hpreShift, periodicPoint_periodShiftCell,
      Metric.mem_closedBall, dist_add_right] at hp
    exact hp
  change T.ncard = S.ncard
  symm
  exact Set.ncard_congr (fun cell _ ↦ periodShiftCell L k cell)
    hmap (fun _ _ _ _ h ↦ hinj h) hsurj

/-! ## Transferring two net estimates to the original centre -/

/-- Inclusion of disks gives monotonicity of their point counts for an
admissible set. -/
theorem diskCount_le_of_closedBall_subset {A : Set Plane} (hA : IsAdmissible A)
    {x y : Plane} {s t : ℝ}
    (hsub : Metric.closedBall x s ⊆ Metric.closedBall y t) :
    diskCount A x s ≤ diskCount A y t := by
  apply Set.ncard_le_ncard
  · intro p hp
    exact ⟨hp.1, hsub hp.2⟩
  · exact hA.inter_closedBall_finite y t

/-- If the discrepancy is bounded for the inner and outer net disks, the
same is true at the original centre, up to the area of the outer shell.

The deliberately symmetric shell bound `π(2rη+η²)` dominates both the
inner and outer area changes. -/
theorem diskError_le_of_nearby_inner_outer
    {A : Set Plane} (hA : IsAdmissible A)
    {x y : Plane} {r η D : ℝ}
    (_hη0 : 0 ≤ η) (_hηr : η ≤ r) (hxy : dist x y ≤ η)
    (hinner : diskError A y (r - η) ≤ D)
    (houter : diskError A y (r + η) ≤ D) :
    diskError A x r ≤ D + Real.pi * (2 * r * η + η ^ 2) := by
  have hsandwich := closedBall_net_sandwich (r := r) hxy
  have hcountLowerNat :
      diskCount A y (r - η) ≤ diskCount A x r :=
    diskCount_le_of_closedBall_subset hA hsandwich.1
  have hcountUpperNat :
      diskCount A x r ≤ diskCount A y (r + η) :=
    diskCount_le_of_closedBall_subset hA hsandwich.2
  have hcountLower :
      (diskCount A y (r - η) : ℝ) ≤ diskCount A x r := by
    exact_mod_cast hcountLowerNat
  have hcountUpper :
      (diskCount A x r : ℝ) ≤ diskCount A y (r + η) := by
    exact_mod_cast hcountUpperNat
  change |(diskCount A y (r - η) : ℝ) - Real.pi * (r - η) ^ 2| ≤ D at hinner
  change |(diskCount A y (r + η) : ℝ) - Real.pi * (r + η) ^ 2| ≤ D at houter
  rcases abs_le.mp hinner with ⟨hinnerLower, hinnerUpper⟩
  rcases abs_le.mp houter with ⟨houterLower, houterUpper⟩
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hinnerShell :
      Real.pi * r ^ 2 - Real.pi * (r - η) ^ 2 ≤
        Real.pi * (2 * r * η + η ^ 2) := by
    have hsq : 0 ≤ η ^ 2 := sq_nonneg η
    nlinarith
  have houterShell :
      Real.pi * (r + η) ^ 2 - Real.pi * r ^ 2 =
        Real.pi * (2 * r * η + η ^ 2) := by
    ring
  change |(diskCount A x r : ℝ) - Real.pi * r ^ 2| ≤
    D + Real.pi * (2 * r * η + η ^ 2)
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

/-- Radius-specialized error transfer for the explicit centre net. -/
theorem diskError_le_of_centerNet_inner_outer
    {A : Set Plane} (hA : IsAdmissible A)
    {L q : ℕ} (hq : 0 < q) {x : Plane} {r D : ℝ}
    {u : CenterNetIndex L q} {k : PlaneCell}
    (hr : Real.sqrt 2 / q ≤ r)
    (hnear : dist x (centerNetPoint q u + periodTranslation L k) ≤
      Real.sqrt 2 / q)
    (hinner : diskError A (centerNetPoint q u + periodTranslation L k)
      (r - Real.sqrt 2 / q) ≤ D)
    (houter : diskError A (centerNetPoint q u + periodTranslation L k)
      (r + Real.sqrt 2 / q) ≤ D) :
    diskError A x r ≤
      D + Real.pi *
        (2 * r * (Real.sqrt 2 / q) + (Real.sqrt 2 / q) ^ 2) := by
  apply diskError_le_of_nearby_inner_outer hA
  · exact div_nonneg (Real.sqrt_nonneg _) (by positivity)
  · exact hr
  · exact hnear
  · exact hinner
  · exact houter

end

end FixedRadiusUpper
end Erdos989
