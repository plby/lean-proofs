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

import ErdosProblems.Erdos989.Core
import ErdosProblems.Erdos989.GlobalSelection

/-!
# Geometry for the fixed-scale upper construction in Erdős problem 989

This file contains the deterministic geometry used by a jittered-sampling proof.  There are
two ingredients.

* If a centre is replaced by a nearby point of a finite net, its disk is squeezed between
  disks with the net centre and slightly smaller/larger radii.
* A unit integer cell on which membership in a disk is not constant is a boundary cell.  The
  half-open unit cells are pairwise disjoint, have area one, and their union is contained in a
  fixed-width annulus.  Comparing areas therefore bounds the number of boundary cells linearly
  in the radius.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos989
namespace UpperGeometry

open GlobalSelection

/-! ## Moving the centre of a disk -/

/-- A disk about `x` with its radius decreased by the centre displacement is contained in the
disk of the original radius about `y`.  No sign assumption on the radii is needed. -/
theorem closedBall_sub_dist_subset (x y : Plane) (r : ℝ) :
    Metric.closedBall x (r - dist x y) ⊆ Metric.closedBall y r := by
  intro z hz
  rw [Metric.mem_closedBall] at hz ⊢
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ ≤ r := by linarith

/-- Moving a disk centre by `d` enlarges the required radius by at most `d`. -/
theorem closedBall_subset_add_dist (x y : Plane) (r : ℝ) :
    Metric.closedBall y r ⊆ Metric.closedBall x (r + dist x y) := by
  intro z hz
  rw [Metric.mem_closedBall] at hz ⊢
  calc
    dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ = dist z y + dist x y := by rw [dist_comm y x]
    _ ≤ r + dist x y := add_le_add hz (le_refl _)

/-- The form of the disk sandwich used with an `η`-net of centres. -/
theorem closedBall_net_sandwich {x y : Plane} {r η : ℝ} (hxy : dist x y ≤ η) :
    Metric.closedBall y (r - η) ⊆ Metric.closedBall x r ∧
      Metric.closedBall x r ⊆ Metric.closedBall y (r + η) := by
  constructor
  · intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ = dist z y + dist x y := by rw [dist_comm y x]
      _ ≤ (r - η) + η := add_le_add hz hxy
      _ = r := by ring
  · intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc
      dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
      _ ≤ r + η := add_le_add hz hxy

/-! ## Half-open integer cells -/

/-- The lower-left corner of an integer cell, in coordinate form. -/
def cellLower (cell : PlaneCell) : Fin 2 → ℝ :=
  ![(cell.1 : ℝ), (cell.2 : ℝ)]

/-- The coordinate half-open unit box belonging to an integer cell. -/
def coordinateUnitCell (cell : PlaneCell) : Set (Fin 2 → ℝ) :=
  Set.pi Set.univ fun i ↦ Set.Ico (cellLower cell i) (cellLower cell i + 1)

/-- The half-open unit box, transported to the Euclidean plane. -/
def unitCell (cell : PlaneCell) : Set Plane :=
  WithLp.ofLp ⁻¹' coordinateUnitCell cell

/-- A cell on which closed-disk membership is not constant. -/
def IsDiskBoundaryCell (center : Plane) (radius : ℝ) (cell : PlaneCell) : Prop :=
  ∃ p ∈ unitCell cell, ∃ q ∈ unitCell cell,
    p ∈ Metric.closedBall center radius ∧ q ∉ Metric.closedBall center radius

/-- Any jittered candidate whose offset belongs to the half-open unit square lies in our
geometric half-open unit cell. -/
theorem latticeLocation_mem_unitCell_of_offset
    {Candidate : Type*} {offset : Candidate → ℝ × ℝ}
    (hoffset : OffsetsInHalfOpenUnitSquare offset) (cell : PlaneCell) (q : Candidate) :
    latticeLocation offset cell q ∈ unitCell cell := by
  rcases hoffset q with ⟨hx0, hx1, hy0, hy1⟩
  apply Set.mem_pi.mpr
  intro i hi
  fin_cases i
  · change (cell.1 : ℝ) ≤ latticeLocation offset cell q 0 ∧
      latticeLocation offset cell q 0 < (cell.1 : ℝ) + 1
    simp only [latticeLocation_apply_zero]
    constructor <;> linarith
  · change (cell.2 : ℝ) ≤ latticeLocation offset cell q 1 ∧
      latticeLocation offset cell q 1 < (cell.2 : ℝ) + 1
    simp only [latticeLocation_apply_one]
    constructor <;> linarith

/-- If two allowed candidates of a cell disagree on disk membership, that cell is a geometric
boundary cell. -/
theorem isDiskBoundaryCell_of_candidates
    {Candidate : Type*} {offset : Candidate → ℝ × ℝ}
    (hoffset : OffsetsInHalfOpenUnitSquare offset)
    {center : Plane} {radius : ℝ} {cell : PlaneCell} {q q' : Candidate}
    (hq : latticeLocation offset cell q ∈ Metric.closedBall center radius)
    (hq' : latticeLocation offset cell q' ∉ Metric.closedBall center radius) :
    IsDiskBoundaryCell center radius cell :=
  ⟨latticeLocation offset cell q,
    latticeLocation_mem_unitCell_of_offset hoffset cell q,
    latticeLocation offset cell q',
    latticeLocation_mem_unitCell_of_offset hoffset cell q', hq, hq'⟩

theorem unitCell_coordinate_bounds {cell : PlaneCell} {p : Plane} (hp : p ∈ unitCell cell) :
    (cell.1 : ℝ) ≤ p 0 ∧ p 0 < (cell.1 : ℝ) + 1 ∧
      (cell.2 : ℝ) ≤ p 1 ∧ p 1 < (cell.2 : ℝ) + 1 := by
  have hp' := Set.mem_pi.mp hp
  have hp0 := hp' 0 (Set.mem_univ 0)
  have hp1 := hp' 1 (Set.mem_univ 1)
  simpa [unitCell, coordinateUnitCell, cellLower] using
    (show (cell.1 : ℝ) ≤ p 0 ∧ p 0 < (cell.1 : ℝ) + 1 ∧
        (cell.2 : ℝ) ≤ p 1 ∧ p 1 < (cell.2 : ℝ) + 1 from
      ⟨hp0.1, hp0.2, hp1.1, hp1.2⟩)

/-- The Euclidean diameter of a half-open unit cell is at most `√2`. -/
theorem dist_le_sqrt_two_of_mem_unitCell {cell : PlaneCell} {p q : Plane}
    (hp : p ∈ unitCell cell) (hq : q ∈ unitCell cell) :
    dist p q ≤ Real.sqrt 2 := by
  rcases unitCell_coordinate_bounds hp with ⟨hp0l, hp0u, hp1l, hp1u⟩
  rcases unitCell_coordinate_bounds hq with ⟨hq0l, hq0u, hq1l, hq1u⟩
  rw [EuclideanSpace.dist_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_two, Real.dist_eq]
  have h0 : |p 0 - q 0| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have h1 : |p 1 - q 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have h0sq : |p 0 - q 0| ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h0)
      (add_nonneg (by norm_num : 0 ≤ (1 : ℝ)) (abs_nonneg (p 0 - q 0)))]
  have h1sq : |p 1 - q 1| ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1)
      (add_nonneg (by norm_num : 0 ≤ (1 : ℝ)) (abs_nonneg (p 1 - q 1)))]
  linarith

theorem measurableSet_coordinateUnitCell (cell : PlaneCell) :
    MeasurableSet (coordinateUnitCell cell) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i hi
  exact measurableSet_Ico

theorem measurableSet_unitCell (cell : PlaneCell) : MeasurableSet (unitCell cell) :=
  (measurableSet_coordinateUnitCell cell).preimage
    (PiLp.volume_preserving_ofLp (Fin 2)).measurable

/-- Every half-open integer cell has Lebesgue area one. -/
@[simp] theorem volume_unitCell (cell : PlaneCell) : volume (unitCell cell) = 1 := by
  rw [unitCell,
    (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      (measurableSet_coordinateUnitCell cell).nullMeasurableSet,
    coordinateUnitCell, Real.volume_pi_Ico]
  simp

@[simp] theorem volumeReal_unitCell (cell : PlaneCell) : volume.real (unitCell cell) = 1 := by
  simp [Measure.real]

/-- Distinct integer cells give disjoint half-open unit boxes. -/
theorem disjoint_unitCell {cell cell' : PlaneCell} (hne : cell ≠ cell') :
    Disjoint (unitCell cell) (unitCell cell') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  rcases unitCell_coordinate_bounds hp with ⟨hp0l, hp0u, hp1l, hp1u⟩
  rcases unitCell_coordinate_bounds hp' with ⟨hp0l', hp0u', hp1l', hp1u'⟩
  apply hne
  apply Prod.ext
  · by_contra hfirst
    rcases lt_or_gt_of_ne hfirst with hlt | hgt
    · have hint : cell.1 + 1 ≤ cell'.1 := by omega
      have hcast : (cell.1 : ℝ) + 1 ≤ (cell'.1 : ℝ) := by exact_mod_cast hint
      linarith
    · have hint : cell'.1 + 1 ≤ cell.1 := by omega
      have hcast : (cell'.1 : ℝ) + 1 ≤ (cell.1 : ℝ) := by exact_mod_cast hint
      linarith
  · by_contra hsecond
    rcases lt_or_gt_of_ne hsecond with hlt | hgt
    · have hint : cell.2 + 1 ≤ cell'.2 := by omega
      have hcast : (cell.2 : ℝ) + 1 ≤ (cell'.2 : ℝ) := by exact_mod_cast hint
      linarith
    · have hint : cell'.2 + 1 ≤ cell.2 := by omega
      have hcast : (cell'.2 : ℝ) + 1 ≤ (cell.2 : ℝ) := by exact_mod_cast hint
      linarith

theorem pairwiseDisjoint_unitCell (s : Finset PlaneCell) :
    Set.PairwiseDisjoint (↑s : Set PlaneCell) unitCell := by
  intro cell hcell cell' hcell' hne
  exact disjoint_unitCell hne

/-- The half-open integer cells tile the whole Euclidean plane. -/
theorem iUnion_unitCell : (⋃ cell : PlaneCell, unitCell cell) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  let cell : PlaneCell := (⌊p 0⌋, ⌊p 1⌋)
  apply Set.mem_iUnion.mpr
  refine ⟨cell, ?_⟩
  apply Set.mem_pi.mpr
  intro i hi
  fin_cases i
  · exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  · exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- Consequently every point belongs to a unique half-open integer cell. -/
theorem existsUnique_mem_unitCell (p : Plane) : ∃! cell : PlaneCell, p ∈ unitCell cell := by
  have hp : p ∈ (⋃ cell : PlaneCell, unitCell cell) := by rw [iUnion_unitCell]; trivial
  rcases Set.mem_iUnion.mp hp with ⟨cell, hcell⟩
  refine ⟨cell, hcell, ?_⟩
  intro cell' hcell'
  by_contra hne
  exact Set.disjoint_left.mp (disjoint_unitCell hne) hcell' hcell

/-- The lower-left integer corner of a cell. -/
def cellCorner (cell : PlaneCell) : Plane :=
  latticeLocation (fun _ : Unit ↦ (0, 0)) cell ()

theorem cellCorner_mem_unitCell (cell : PlaneCell) : cellCorner cell ∈ unitCell cell := by
  apply Set.mem_pi.mpr
  intro i hi
  fin_cases i <;> simp [cellCorner, cellLower]

theorem boundaryCellSet_finite (center : Plane) (radius : ℝ) :
    {cell : PlaneCell | IsDiskBoundaryCell center radius cell}.Finite := by
  have htable : CandidateTableLocallyFinite
      (latticeLocation (fun _ : Unit ↦ (0, 0))) :=
    latticeLocation_candidateTableLocallyFinite (fun _ ↦ by norm_num)
  apply (htable center (radius + Real.sqrt 2)).subset
  intro cell hcell
  rcases hcell with ⟨p, hpCell, q, hqCell, hp, hq⟩
  refine ⟨(), ?_⟩
  rw [Metric.mem_closedBall] at hp ⊢
  change dist (cellCorner cell) center ≤ radius + Real.sqrt 2
  calc
    dist (cellCorner cell) center ≤ dist (cellCorner cell) p + dist p center :=
      dist_triangle _ _ _
    _ ≤ Real.sqrt 2 + radius :=
      add_le_add
        (dist_le_sqrt_two_of_mem_unitCell (cellCorner_mem_unitCell cell) hpCell) hp
    _ = radius + Real.sqrt 2 := add_comm _ _

/-- Outside the boundary-cell set, disk membership is constant throughout the cell. -/
theorem mem_closedBall_iff_of_not_boundary {center : Plane} {radius : ℝ}
    {cell : PlaneCell} (hcell : ¬ IsDiskBoundaryCell center radius cell)
    {p q : Plane} (hpCell : p ∈ unitCell cell) (hqCell : q ∈ unitCell cell) :
    p ∈ Metric.closedBall center radius ↔ q ∈ Metric.closedBall center radius := by
  constructor
  · intro hp
    by_contra hq
    exact hcell ⟨p, hpCell, q, hqCell, hp, hq⟩
  · intro hq
    by_contra hp
    exact hcell ⟨q, hqCell, p, hpCell, hq, hp⟩

/-- Equivalently, each non-boundary cell is wholly inside or wholly outside the disk. -/
theorem all_mem_or_all_not_mem_of_not_boundary {center : Plane} {radius : ℝ}
    {cell : PlaneCell} (hcell : ¬ IsDiskBoundaryCell center radius cell) :
    (∀ p ∈ unitCell cell, p ∈ Metric.closedBall center radius) ∨
      (∀ p ∈ unitCell cell, p ∉ Metric.closedBall center radius) := by
  by_cases hcorner : cellCorner cell ∈ Metric.closedBall center radius
  · left
    intro p hp
    exact (mem_closedBall_iff_of_not_boundary hcell
      (cellCorner_mem_unitCell cell) hp).mp hcorner
  · right
    intro p hp hpmem
    exact hcorner ((mem_closedBall_iff_of_not_boundary hcell hp
      (cellCorner_mem_unitCell cell)).mp hpmem)

/-! ## Boundary cells occupy a fixed-width annulus -/

/-- The entire half-open cell of a mixed cell lies between the two concentric circles whose
radii differ from the disk radius by `√2`. -/
theorem unitCell_subset_annulus_of_boundary {center : Plane} {radius : ℝ}
    {cell : PlaneCell} (hcell : IsDiskBoundaryCell center radius cell) :
    unitCell cell ⊆
      Metric.closedBall center (radius + Real.sqrt 2) \
        Metric.closedBall center (radius - Real.sqrt 2) := by
  rcases hcell with ⟨p, hpCell, q, hqCell, hp, hq⟩
  intro u hu
  constructor
  · rw [Metric.mem_closedBall] at hp ⊢
    calc
      dist u center ≤ dist u p + dist p center := dist_triangle _ _ _
      _ ≤ Real.sqrt 2 + radius :=
        add_le_add (dist_le_sqrt_two_of_mem_unitCell hu hpCell) hp
      _ = radius + Real.sqrt 2 := add_comm _ _
  · rw [Metric.mem_closedBall, not_le] at hq ⊢
    have htri : dist q center ≤ dist q u + dist u center := dist_triangle _ _ _
    have hqu : dist q u ≤ Real.sqrt 2 :=
      dist_le_sqrt_two_of_mem_unitCell hqCell hu
    linarith

/-- A finite family of boundary cells has cardinality at most the area of the width-`√2`
annulus which contains its unit boxes. -/
theorem card_boundaryCells_le_annulus_area {center : Plane} {radius : ℝ}
    (s : Finset PlaneCell)
    (hs : ∀ cell ∈ s, IsDiskBoundaryCell center radius cell)
    (hr : Real.sqrt 2 ≤ radius) :
    (s.card : ℝ) ≤ 4 * Real.pi * Real.sqrt 2 * radius := by
  let U : Set Plane := ⋃ cell ∈ s, unitCell cell
  let A : Set Plane :=
    Metric.closedBall center (radius + Real.sqrt 2) \
      Metric.closedBall center (radius - Real.sqrt 2)
  have hUA : U ⊆ A := by
    intro p hp
    simp only [U, Set.mem_iUnion] at hp
    rcases hp with ⟨cell, hp⟩
    rcases hp with ⟨hcell, hp⟩
    exact unitCell_subset_annulus_of_boundary (hs cell hcell) hp
  have hUvol : volume.real U = s.card := by
    simp only [U]
    rw [measureReal_biUnion_finset (pairwiseDisjoint_unitCell s)
      (fun cell _ ↦ measurableSet_unitCell cell)
      (fun cell _ ↦ by rw [volume_unitCell]; norm_num)]
    simp
  have hinner_nonneg : 0 ≤ radius - Real.sqrt 2 := sub_nonneg.mpr hr
  have houter_nonneg : 0 ≤ radius + Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hinner_outer : radius - Real.sqrt 2 ≤ radius + Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have houter_finite :
      volume (Metric.closedBall center (radius + Real.sqrt 2)) ≠ ∞ := by
    rw [EuclideanSpace.volume_closedBall_fin_two]
    finiteness
  have hAfinite : volume A ≠ ∞ :=
    measure_ne_top_of_subset Set.sdiff_subset houter_finite
  have hAvol : volume.real A = 4 * Real.pi * Real.sqrt 2 * radius := by
    change volume.real
      (Metric.closedBall center (radius + Real.sqrt 2) \
        Metric.closedBall center (radius - Real.sqrt 2)) = _
    rw [measureReal_sdiff
      (Metric.closedBall_subset_closedBall hinner_outer) measurableSet_closedBall houter_finite,
      volume_closedBall_plane center houter_nonneg,
      volume_closedBall_plane center hinner_nonneg]
    ring
  rw [← hUvol, ← hAvol]
  exact measureReal_mono hUA hAfinite

/-- The same linear estimate for the complete set of mixed cells. -/
theorem ncard_boundaryCellSet_le {center : Plane} {radius : ℝ}
    (hr : Real.sqrt 2 ≤ radius) :
    (({cell : PlaneCell | IsDiskBoundaryCell center radius cell}.ncard : ℕ) : ℝ) ≤
      4 * Real.pi * Real.sqrt 2 * radius := by
  let hfinite := boundaryCellSet_finite center radius
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  apply card_boundaryCells_le_annulus_area (center := center) (radius := radius) hfinite.toFinset
  · intro cell hcell
    exact hfinite.mem_toFinset.mp hcell
  · exact hr

/-- A convenient integer-constant version of the boundary-cell estimate.  The deliberately
generous constant `48` is useful when the radius in a net sandwich is allowed to vary slightly. -/
theorem ncard_boundaryCellSet_le_48_mul {center : Plane} {radius : ℝ}
    (hr : Real.sqrt 2 ≤ radius) :
    (({cell : PlaneCell | IsDiskBoundaryCell center radius cell}.ncard : ℕ) : ℝ) ≤
      48 * radius := by
  refine (ncard_boundaryCellSet_le (center := center) hr).trans ?_
  have hr0 : 0 ≤ radius := (Real.sqrt_nonneg 2).trans hr
  apply mul_le_mul_of_nonneg_right _ hr0
  have hsqrt : Real.sqrt 2 ≤ 2 := by norm_num
  have hprod : Real.pi * Real.sqrt 2 ≤ 4 * 2 :=
    mul_le_mul Real.pi_le_four hsqrt (Real.sqrt_nonneg 2) (by norm_num)
  nlinarith

end UpperGeometry
end Erdos989
