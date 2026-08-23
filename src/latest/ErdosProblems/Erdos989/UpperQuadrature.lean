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

import ErdosProblems.Erdos989.Upper
import ErdosProblems.Erdos989.UpperGeometry

/-!
# Midpoint-grid quadrature for disks

The deterministic expectation in the fixed-radius jitter construction is the normalized number
of points of the `1/q` midpoint grid in a disk.  After dilation by `q`, this is the number of
half-integer lattice points in a disk of radius `q * r`.  The unit squares centred at those points
sandwich the disk between radii differing by `sqrt 2 / 2`, which gives an explicit quadrature
error of order `r / q`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos989
namespace FixedRadiusUpper

open GlobalSelection UpperGeometry

noncomputable section

/-! ## Half-integer lattice cells -/

/-- The centre of the half-open unit square indexed by `cell`. -/
def unitMidpoint (cell : PlaneCell) : Plane :=
  latticeLocation (fun _ : Unit ↦ (1 / 2, 1 / 2)) cell ()

@[simp] theorem unitMidpoint_apply_zero (cell : PlaneCell) :
    unitMidpoint cell 0 = (cell.1 : ℝ) + 1 / 2 := by
  rfl

@[simp] theorem unitMidpoint_apply_one (cell : PlaneCell) :
    unitMidpoint cell 1 = (cell.2 : ℝ) + 1 / 2 := by
  rfl

theorem unitMidpoint_mem_unitCell (cell : PlaneCell) :
    unitMidpoint cell ∈ unitCell cell := by
  apply Set.mem_pi.mpr
  intro i hi
  fin_cases i <;> simp [unitMidpoint, cellLower] <;> norm_num

/-- The unit square indexed by the coordinatewise floors contains a given point. -/
theorem exists_mem_unitCell (p : Plane) :
    ∃ cell : PlaneCell, p ∈ unitCell cell := by
  let cell : PlaneCell := (⌊p 0⌋, ⌊p 1⌋)
  refine ⟨cell, ?_⟩
  apply Set.mem_pi.mpr
  intro i hi
  fin_cases i
  · change (⌊p 0⌋ : ℝ) ≤ p 0 ∧ p 0 < (⌊p 0⌋ : ℝ) + 1
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  · change (⌊p 1⌋ : ℝ) ≤ p 1 ∧ p 1 < (⌊p 1⌋ : ℝ) + 1
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- Every point of a unit square is within half its diagonal of the square midpoint. -/
theorem dist_unitMidpoint_le {cell : PlaneCell} {p : Plane}
    (hp : p ∈ unitCell cell) :
    dist p (unitMidpoint cell) ≤ Real.sqrt 2 / 2 := by
  rcases unitCell_coordinate_bounds hp with ⟨hp0l, hp0u, hp1l, hp1u⟩
  rw [EuclideanSpace.dist_eq]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simp only [Fin.sum_univ_two, Real.dist_eq, unitMidpoint_apply_zero,
      unitMidpoint_apply_one]
    have h0 : |p 0 - ((cell.1 : ℝ) + 1 / 2)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have h1 : |p 1 - ((cell.2 : ℝ) + 1 / 2)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have h0sq : |p 0 - ((cell.1 : ℝ) + 1 / 2)| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ (1 / 2 : ℝ) by norm_num)).2 h0
    have h1sq : |p 1 - ((cell.2 : ℝ) + 1 / 2)| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ (1 / 2 : ℝ) by norm_num)).2 h1
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    nlinarith

/-- Integer cells whose half-integer midpoint is in the specified disk. -/
def midpointCellSet (center : Plane) (radius : ℝ) : Set PlaneCell :=
  {cell | unitMidpoint cell ∈ Metric.closedBall center radius}

theorem midpointCellSet_finite (center : Plane) (radius : ℝ) :
    (midpointCellSet center radius).Finite := by
  have htable : CandidateTableLocallyFinite
      (latticeLocation (fun _ : Unit ↦ (1 / 2, 1 / 2))) :=
    latticeLocation_candidateTableLocallyFinite (fun _ ↦ by norm_num)
  apply (htable center radius).subset
  intro cell hcell
  exact ⟨(), hcell⟩

/-- Union of the unit cells selected by the half-integer midpoint rule. -/
def midpointCellUnion (center : Plane) (radius : ℝ) : Set Plane :=
  ⋃ cell ∈ (midpointCellSet_finite center radius).toFinset, unitCell cell

theorem measurableSet_midpointCellUnion (center : Plane) (radius : ℝ) :
    MeasurableSet (midpointCellUnion center radius) := by
  simp only [midpointCellUnion]
  exact Finset.measurableSet_biUnion _ (fun cell _ ↦ measurableSet_unitCell cell)

/-- The area of the selected-cell union is its number of midpoints. -/
theorem volumeReal_midpointCellUnion (center : Plane) (radius : ℝ) :
    volume.real (midpointCellUnion center radius) =
      ((midpointCellSet center radius).ncard : ℕ) := by
  rw [midpointCellUnion,
    measureReal_biUnion_finset
      (pairwiseDisjoint_unitCell (midpointCellSet_finite center radius).toFinset)
      (fun cell _ ↦ measurableSet_unitCell cell)
      (fun cell _ ↦ by rw [volume_unitCell]; norm_num)]
  simp [Set.ncard_eq_toFinset_card _ (midpointCellSet_finite center radius)]

/-- Midpoint cells contain the disk with radius decreased by half a unit-square diagonal. -/
theorem closedBall_sub_halfDiagonal_subset_midpointCellUnion
    (center : Plane) (radius : ℝ) :
    Metric.closedBall center (radius - Real.sqrt 2 / 2) ⊆
      midpointCellUnion center radius := by
  intro p hp
  obtain ⟨cell, hpcell⟩ := exists_mem_unitCell p
  have hmid : unitMidpoint cell ∈ Metric.closedBall center radius := by
    rw [Metric.mem_closedBall] at hp ⊢
    calc
      dist (unitMidpoint cell) center ≤
          dist (unitMidpoint cell) p + dist p center := dist_triangle _ _ _
      _ = dist p (unitMidpoint cell) + dist p center := by
        rw [dist_comm (unitMidpoint cell) p]
      _ ≤ Real.sqrt 2 / 2 + (radius - Real.sqrt 2 / 2) :=
        add_le_add (dist_unitMidpoint_le hpcell) hp
      _ = radius := by ring
  simp only [midpointCellUnion, Set.mem_iUnion]
  refine ⟨cell, ?_⟩
  refine ⟨?_, hpcell⟩
  exact (midpointCellSet_finite center radius).mem_toFinset.mpr hmid

/-- Midpoint cells are contained in the disk with radius increased by half a unit-square
diagonal. -/
theorem midpointCellUnion_subset_closedBall_add_halfDiagonal
    (center : Plane) (radius : ℝ) :
    midpointCellUnion center radius ⊆
      Metric.closedBall center (radius + Real.sqrt 2 / 2) := by
  intro p hp
  simp only [midpointCellUnion, Set.mem_iUnion] at hp
  obtain ⟨cell, hcell, hpcell⟩ := hp
  have hmid : unitMidpoint cell ∈ Metric.closedBall center radius :=
    (midpointCellSet_finite center radius).mem_toFinset.mp hcell
  rw [Metric.mem_closedBall] at hmid ⊢
  calc
    dist p center ≤ dist p (unitMidpoint cell) + dist (unitMidpoint cell) center :=
      dist_triangle _ _ _
    _ ≤ Real.sqrt 2 / 2 + radius := add_le_add (dist_unitMidpoint_le hpcell) hmid
    _ = radius + Real.sqrt 2 / 2 := add_comm _ _

/-- Half-integer midpoint quadrature for a disk.  The deliberately generous constants make the
result convenient downstream and avoid carrying `pi` and `sqrt 2` through the probability proof. -/
theorem halfInteger_midpoint_disk_quadrature {center : Plane} {radius : ℝ}
    (hr : Real.sqrt 2 / 2 ≤ radius) :
    |(((midpointCellSet center radius).ncard : ℕ) : ℝ) - Real.pi * radius ^ 2| ≤
      16 * radius + 16 := by
  let U := midpointCellUnion center radius
  have hr0 : 0 ≤ radius :=
    (div_nonneg (Real.sqrt_nonneg _) (by norm_num)).trans hr
  have hinner0 : 0 ≤ radius - Real.sqrt 2 / 2 := sub_nonneg.mpr hr
  have houter0 : 0 ≤ radius + Real.sqrt 2 / 2 := by
    exact add_nonneg hr0 (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
  have hUfinite : volume U ≠ ∞ := by
    apply measure_ne_top_of_subset
      (midpointCellUnion_subset_closedBall_add_halfDiagonal center radius)
    exact measure_closedBall_lt_top.ne
  have hlower : Real.pi * (radius - Real.sqrt 2 / 2) ^ 2 ≤
      ((midpointCellSet center radius).ncard : ℕ) := by
    rw [← volumeReal_midpointCellUnion center radius,
      ← volume_closedBall_plane center hinner0]
    exact measureReal_mono
      (closedBall_sub_halfDiagonal_subset_midpointCellUnion center radius) hUfinite
  have hupper : (((midpointCellSet center radius).ncard : ℕ) : ℝ) ≤
      Real.pi * (radius + Real.sqrt 2 / 2) ^ 2 := by
    rw [← volumeReal_midpointCellUnion center radius,
      ← volume_closedBall_plane center houter0]
    exact measureReal_mono
      (midpointCellUnion_subset_closedBall_add_halfDiagonal center radius)
      measure_closedBall_lt_top.ne
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_le_two : Real.sqrt 2 ≤ 2 := by norm_num
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hpisqrt : Real.pi * Real.sqrt 2 ≤ 8 :=
    (mul_le_mul hpi4 hsqrt_le_two hsqrt0 (by norm_num)).trans_eq (by norm_num)
  have hpisqrt_r : Real.pi * Real.sqrt 2 * radius ≤ 8 * radius :=
    mul_le_mul_of_nonneg_right hpisqrt hr0
  have hpi_half : Real.pi / 2 ≤ 2 := by linarith
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  rw [abs_le]
  constructor <;> nlinarith

/-! ## Rescaling the `q × q` candidate grid -/

/-- Reindex a unit cell together with one of its `q × q` candidates as a single cell of the
fine grid.  Coordinatewise this is `(cell, residue) ↦ q * cell + residue`. -/
def fineIndex (q : ℕ) [NeZero q] :
    PlaneCell × GridCandidate q → PlaneCell :=
  fun a ↦
    ((Int.divModEquiv q).symm (a.1.1, a.2.1),
      (Int.divModEquiv q).symm (a.1.2, a.2.2))

theorem fineIndex_injective (q : ℕ) [NeZero q] :
    Function.Injective (fineIndex q) := by
  rintro ⟨cell, u⟩ ⟨cell', u'⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hx' := (Int.divModEquiv q).symm.injective hx
  have hy' := (Int.divModEquiv q).symm.injective hy
  have hcell : cell = cell' :=
    Prod.ext
      (congrArg (fun z : ℤ × Fin q ↦ z.1) hx')
      (congrArg (fun z : ℤ × Fin q ↦ z.1) hy')
  have hu : u = u' :=
    Prod.ext
      (congrArg (fun z : ℤ × Fin q ↦ z.2) hx')
      (congrArg (fun z : ℤ × Fin q ↦ z.2) hy')
  exact Prod.ext hcell hu

theorem fineIndex_surjective (q : ℕ) [NeZero q] :
    Function.Surjective (fineIndex q) := by
  intro cell
  let x := Int.divModEquiv q cell.1
  let y := Int.divModEquiv q cell.2
  refine ⟨((x.1, y.1), (x.2, y.2)), ?_⟩
  apply Prod.ext
  · exact (Int.divModEquiv q).symm_apply_apply cell.1
  · exact (Int.divModEquiv q).symm_apply_apply cell.2

theorem smul_candidateMidpoint_eq_unitMidpoint_fineIndex
    (q : ℕ) [NeZero q] (a : PlaneCell × GridCandidate q) :
    (q : ℝ) • latticeLocation (midpointOffset q) a.1 a.2 =
      unitMidpoint (fineIndex q a) := by
  ext i
  fin_cases i <;>
    simp [fineIndex, unitMidpoint, midpointOffset, Int.divModEquiv_symm_apply]
  <;> field_simp [NeZero.ne q]
  <;> ring

/-- All `(integer cell, candidate)` pairs whose candidate midpoint lies in a disk. -/
def candidateMidpointHitSet (q : ℕ) (center : Plane) (radius : ℝ) :
    Set (PlaneCell × GridCandidate q) :=
  {a | latticeLocation (midpointOffset q) a.1 a.2 ∈
    Metric.closedBall center radius}

theorem candidateMidpoint_mem_closedBall_iff_fineIndex
    {q : ℕ} [NeZero q] (hq : 0 < q) (a : PlaneCell × GridCandidate q)
    (center : Plane) (radius : ℝ) :
    a ∈ candidateMidpointHitSet q center radius ↔
      fineIndex q a ∈ midpointCellSet ((q : ℝ) • center) ((q : ℝ) * radius) := by
  change latticeLocation (midpointOffset q) a.1 a.2 ∈ Metric.closedBall center radius ↔
    unitMidpoint (fineIndex q a) ∈
      Metric.closedBall ((q : ℝ) • center) ((q : ℝ) * radius)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  rw [Metric.mem_closedBall, Metric.mem_closedBall,
    ← smul_candidateMidpoint_eq_unitMidpoint_fineIndex q a, dist_smul₀,
    Real.norm_eq_abs, abs_of_pos hqR]
  exact (mul_le_mul_iff_of_pos_left hqR).symm

theorem candidateMidpointHitSet_eq_preimage_fineIndex
    {q : ℕ} [NeZero q] (hq : 0 < q) (center : Plane) (radius : ℝ) :
    candidateMidpointHitSet q center radius =
      fineIndex q ⁻¹'
        midpointCellSet ((q : ℝ) • center) ((q : ℝ) * radius) := by
  ext a
  exact candidateMidpoint_mem_closedBall_iff_fineIndex hq a center radius

theorem candidateMidpointHitSet_finite
    {q : ℕ} [NeZero q] (hq : 0 < q) (center : Plane) (radius : ℝ) :
    (candidateMidpointHitSet q center radius).Finite := by
  rw [candidateMidpointHitSet_eq_preimage_fineIndex hq center radius]
  exact (midpointCellSet_finite ((q : ℝ) • center) ((q : ℝ) * radius)).preimage
    (fineIndex_injective q).injOn

/-- Dilation by `q` is a bijection from candidate midpoints in a disk to half-integer lattice
midpoints in the dilated disk. -/
theorem ncard_candidateMidpointHitSet_eq
    {q : ℕ} [NeZero q] (hq : 0 < q) (center : Plane) (radius : ℝ) :
    (candidateMidpointHitSet q center radius).ncard =
      (midpointCellSet ((q : ℝ) • center) ((q : ℝ) * radius)).ncard := by
  apply Set.ncard_congr (fun a _ ↦ fineIndex q a)
  · intro a ha
    exact (candidateMidpoint_mem_closedBall_iff_fineIndex hq a center radius).mp ha
  · intro a b ha hb hab
    exact fineIndex_injective q hab
  · intro cell hcell
    obtain ⟨a, ha⟩ := fineIndex_surjective q cell
    refine ⟨a, ?_, ha⟩
    exact (candidateMidpoint_mem_closedBall_iff_fineIndex hq a center radius).mpr (ha ▸ hcell)

/-- Explicit disk quadrature for the full `q × q` midpoint grid. -/
theorem midpoint_grid_disk_quadrature
    {q : ℕ} (hq : 0 < q) (center : Plane) {radius : ℝ}
    (hr : Real.sqrt 2 / (2 * q) ≤ radius) :
    |(((candidateMidpointHitSet q center radius).ncard : ℕ) : ℝ) / (q : ℝ) ^ 2 -
        Real.pi * radius ^ 2| ≤
      16 * radius / q + 16 / (q : ℝ) ^ 2 := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hscaled : Real.sqrt 2 / 2 ≤ (q : ℝ) * radius := by
    rw [div_le_iff₀ (by positivity : 0 < (2 : ℝ) * q)] at hr
    nlinarith
  have hhalf := halfInteger_midpoint_disk_quadrature
    (center := (q : ℝ) • center) (radius := (q : ℝ) * radius) hscaled
  rw [← ncard_candidateMidpointHitSet_eq hq center radius] at hhalf
  have hq2 : 0 < (q : ℝ) ^ 2 := sq_pos_of_pos hqR
  calc
    |(((candidateMidpointHitSet q center radius).ncard : ℕ) : ℝ) / (q : ℝ) ^ 2 -
        Real.pi * radius ^ 2| =
        |(((candidateMidpointHitSet q center radius).ncard : ℕ) : ℝ) -
          Real.pi * ((q : ℝ) * radius) ^ 2| / (q : ℝ) ^ 2 := by
            have heq :
                (((candidateMidpointHitSet q center radius).ncard : ℕ) : ℝ) /
                    (q : ℝ) ^ 2 - Real.pi * radius ^ 2 =
                  ((((candidateMidpointHitSet q center radius).ncard : ℕ) : ℝ) -
                    Real.pi * ((q : ℝ) * radius) ^ 2) / (q : ℝ) ^ 2 := by
              field_simp
            rw [heq, abs_div, abs_of_pos hq2]
    _ ≤ (16 * ((q : ℝ) * radius) + 16) / (q : ℝ) ^ 2 :=
      (div_le_div_iff_of_pos_right hq2).2 hhalf
    _ = 16 * radius / q + 16 / (q : ℝ) ^ 2 := by
      field_simp

end

end FixedRadiusUpper
end Erdos989
