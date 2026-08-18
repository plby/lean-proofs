/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.AxisBoxes
import ErdosProblems.Erdos186.PZ.ConvexDensity.DyadicCells

/-!
# A finite axis grid on the normalized cube

This file supplies the geometric assignment used by the abstract counting
lemmas in `DyadicCells`.  For mesh `r > 0`, a point `x` is assigned the
coordinatewise natural-floor index

`i |-> floor ((x_i + 1) / r)`.

On the cube `[-1,1]^d`, every coordinate of this index is at most
`ceil (2 / r)`.  Thus all assignments lie in an explicit finite family of at
most `(ceil (2 / r) + 1)^d` indices.  The geometric cell belonging to an
index is the closed box with lower corner `-1 + r k` and side length `r`.
Closed boxes can overlap on their boundaries; the assignment fibres, which
are what the occupancy argument counts, are proved pairwise disjoint.
-/

open Set
open scoped BigOperators

namespace Erdos186.PZ.ConvexDensity.GridPartition

open Erdos186.PZ.ConvexDensity

noncomputable section

/-! ## The cube, the floor assignment, and its cells -/

/-- The normalized coordinate cube `[-1,1]^d`. -/
def normalizedCube (d : ℕ) : Set (EuclideanPoint d) :=
  closedAxisBox (fun _ ↦ -1) (fun _ ↦ 1)

@[simp]
theorem mem_normalizedCube_iff {d : ℕ} {x : EuclideanPoint d} :
    x ∈ normalizedCube d ↔ ∀ i, -1 ≤ coordinate x i ∧ coordinate x i ≤ 1 :=
  Iff.rfl

/-- The global coordinatewise floor assignment.  It is defined on the whole
Euclidean space; nonnegativity is needed only when proving the cube bound. -/
def gridIndex {d : ℕ} (r : ℝ) (x : EuclideanPoint d) : Fin d → ℕ :=
  fun i ↦ ⌊(coordinate x i + 1) / r⌋₊

/-- Lower corner of the closed cell with index `k`. -/
def cellLower {d : ℕ} (r : ℝ) (k : Fin d → ℕ) : Fin d → ℝ :=
  fun i ↦ -1 + r * (k i : ℝ)

/-- Upper corner of the closed cell with index `k`. -/
def cellUpper {d : ℕ} (r : ℝ) (k : Fin d → ℕ) : Fin d → ℝ :=
  fun i ↦ -1 + r * ((k i : ℝ) + 1)

/-- The closed geometric grid cell belonging to `k`. -/
def gridCell {d : ℕ} (r : ℝ) (k : Fin d → ℕ) :
    Set (EuclideanPoint d) :=
  closedAxisBox (cellLower r k) (cellUpper r k)

/-- Center of a grid cell. -/
def gridCenter {d : ℕ} (r : ℝ) (k : Fin d → ℕ) :
    EuclideanPoint d :=
  WithLp.toLp 2 (fun i ↦ -1 + r * ((k i : ℝ) + 1 / 2))

@[simp]
theorem coordinate_gridCenter {d : ℕ} (r : ℝ) (k : Fin d → ℕ)
    (i : Fin d) :
    coordinate (gridCenter r k) i = -1 + r * ((k i : ℝ) + 1 / 2) := by
  rfl

/-- A point lies in the closed cell indexed by its floor assignment. -/
theorem mem_gridCell_gridIndex {d : ℕ} {r : ℝ} (hr : 0 < r)
    (x : EuclideanPoint d) (hx : x ∈ normalizedCube d) :
    x ∈ gridCell r (gridIndex r x) := by
  intro i
  have hcoord := hx i
  have hq : 0 ≤ (coordinate x i + 1) / r :=
    div_nonneg (by linarith [hcoord.1]) hr.le
  have hfloor :
      ((⌊(coordinate x i + 1) / r⌋₊ : ℕ) : ℝ) ≤
        (coordinate x i + 1) / r :=
    Nat.floor_le hq
  have hlower := mul_le_mul_of_nonneg_left hfloor hr.le
  have hupper0 :
      (coordinate x i + 1) / r <
        ((⌊(coordinate x i + 1) / r⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hupper := mul_lt_mul_of_pos_left hupper0 hr
  rw [mul_div_cancel₀ _ hr.ne'] at hlower hupper
  constructor
  · change -1 + r * ((⌊(coordinate x i + 1) / r⌋₊ : ℕ) : ℝ) ≤
      coordinate x i
    linarith
  · change coordinate x i ≤
      -1 + r * (((⌊(coordinate x i + 1) / r⌋₊ : ℕ) : ℝ) + 1)
    linarith

/-! ## The explicit finite candidate family -/

/-- Embed a bounded finite-valued index into a natural-valued index. -/
def forgetGridBound {d n : ℕ} (k : Fin d → Fin (n + 1)) : Fin d → ℕ :=
  fun i ↦ k i

/-- All natural-valued indices whose coordinates are at most `ceil (2/r)`.
The image presentation gives a literal finite set with the desired function
type, so it can be passed directly to `DyadicCells`. -/
def candidateGridIndices (d : ℕ) (r : ℝ) : Finset (Fin d → ℕ) :=
  Finset.univ.image
    (forgetGridBound : (Fin d → Fin (⌈2 / r⌉₊ + 1)) → (Fin d → ℕ))

theorem card_candidateGridIndices_le (d : ℕ) (r : ℝ) :
    (candidateGridIndices d r).card ≤ (⌈2 / r⌉₊ + 1) ^ d := by
  calc
    (candidateGridIndices d r).card ≤
        (Finset.univ : Finset (Fin d → Fin (⌈2 / r⌉₊ + 1))).card :=
      Finset.card_image_le
    _ = (⌈2 / r⌉₊ + 1) ^ d := by simp

/-- An index belongs to the candidate family exactly when each coordinate is
at most `ceil (2/r)`. -/
theorem mem_candidateGridIndices_iff {d : ℕ} {r : ℝ} {k : Fin d → ℕ} :
    k ∈ candidateGridIndices d r ↔ ∀ i, k i ≤ ⌈2 / r⌉₊ := by
  rw [candidateGridIndices, Finset.mem_image]
  constructor
  · rintro ⟨j, -, rfl⟩ i
    exact Nat.le_of_lt_succ (j i).isLt
  · intro hk
    let j : Fin d → Fin (⌈2 / r⌉₊ + 1) :=
      fun i ↦ ⟨k i, Nat.lt_succ_iff.mpr (hk i)⟩
    refine ⟨j, Finset.mem_univ _, ?_⟩
    funext i
    rfl

/-- Every point of the normalized cube maps to the finite candidate family. -/
theorem gridIndex_mem_candidateGridIndices {d : ℕ} {r : ℝ} (hr : 0 < r)
    {x : EuclideanPoint d} (hx : x ∈ normalizedCube d) :
    gridIndex r x ∈ candidateGridIndices d r := by
  rw [mem_candidateGridIndices_iff]
  intro i
  have hqle : (coordinate x i + 1) / r ≤ 2 / r := by
    apply (div_le_div_iff_of_pos_right hr).mpr
    linarith [(hx i).2]
  exact (Nat.floor_le_floor hqle).trans (Nat.floor_le_ceil _)

/-- The map-to-candidates hypothesis in exactly the form consumed by
`DyadicCells.sum_occupancy_eq_card`. -/
theorem gridIndex_maps_finset_to_candidates {d : ℕ} {r : ℝ} (hr : 0 < r)
    (X : Finset (EuclideanPoint d))
    (hX : ↑X ⊆ normalizedCube d) :
    ∀ x ∈ X, gridIndex r x ∈ candidateGridIndices d r := by
  intro x hx
  exact gridIndex_mem_candidateGridIndices hr (hX hx)

/-! ## Geometry of one cell -/

theorem convex_gridCell {d : ℕ} (r : ℝ) (k : Fin d → ℕ) :
    Convex ℝ (gridCell r k) :=
  convex_closedAxisBox _ _

theorem isClosed_gridCell {d : ℕ} (r : ℝ) (k : Fin d → ℕ) :
    IsClosed (gridCell r k) :=
  isClosed_closedAxisBox _ _

theorem isCompact_gridCell {d : ℕ} (r : ℝ) (k : Fin d → ℕ) :
    IsCompact (gridCell r k) := by
  rw [gridCell, closedAxisBox_eq_preimage_Icc]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)).toHomeomorph.isCompact_preimage.mpr
    isCompact_Icc

theorem measurableSet_gridCell {d : ℕ} (r : ℝ) (k : Fin d → ℕ) :
    MeasurableSet (gridCell r k) :=
  measurableSet_closedAxisBox _ _

theorem gridCenter_mem_gridCell {d : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (k : Fin d → ℕ) : gridCenter r k ∈ gridCell r k := by
  intro i
  change
    -1 + r * (k i : ℝ) ≤ -1 + r * ((k i : ℝ) + 1 / 2) ∧
      -1 + r * ((k i : ℝ) + 1 / 2) ≤ -1 + r * ((k i : ℝ) + 1)
  constructor <;> nlinarith

/-- Coordinate displacement from the center is at most half the mesh. -/
theorem abs_coordinate_sub_center_le {d : ℕ} {r : ℝ} (_hr : 0 ≤ r)
    {k : Fin d → ℕ} {x : EuclideanPoint d} (hx : x ∈ gridCell r k)
    (i : Fin d) :
    |coordinate x i - coordinate (gridCenter r k) i| ≤ r / 2 := by
  rw [abs_le]
  have hi := hx i
  change
    -1 + r * (k i : ℝ) ≤ coordinate x i ∧
      coordinate x i ≤ -1 + r * ((k i : ℝ) + 1) at hi
  rw [coordinate_gridCenter]
  constructor <;> nlinarith [_hr]

/-- Every point of a cell lies within Euclidean distance
`sqrt(d) * (r/2)` of its center. -/
theorem norm_sub_gridCenter_le {d : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {k : Fin d → ℕ} {x : EuclideanPoint d} (hx : x ∈ gridCell r k) :
    ‖x - gridCenter r k‖ ≤ Real.sqrt (d : ℝ) * (r / 2) := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hr (by norm_num)))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, ((x - gridCenter r k) i) ^ 2 ≤
        ∑ _i : Fin d, (r / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have habs := abs_coordinate_sub_center_le hr hx i
      change |(x - gridCenter r k) i| ≤ r / 2 at habs
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _)
        (div_nonneg hr (by norm_num))).mpr habs
    _ = (Real.sqrt (d : ℝ) * (r / 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      simp

/-- Cell radius in the slightly looser form `sqrt(d) * r`. -/
theorem norm_sub_gridCenter_le_sqrt_mul {d : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {k : Fin d → ℕ} {x : EuclideanPoint d} (hx : x ∈ gridCell r k) :
    ‖x - gridCenter r k‖ ≤ Real.sqrt (d : ℝ) * r := by
  calc
    ‖x - gridCenter r k‖ ≤ Real.sqrt (d : ℝ) * (r / 2) :=
      norm_sub_gridCenter_le hr hx
    _ ≤ Real.sqrt (d : ℝ) * r := by
      gcongr
      linarith

/-- The Euclidean diameter bound for a mesh cell. -/
theorem dist_le_sqrt_mul_of_mem_gridCell {d : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {k : Fin d → ℕ} {x y : EuclideanPoint d}
    (hx : x ∈ gridCell r k) (hy : y ∈ gridCell r k) :
    dist x y ≤ Real.sqrt (d : ℝ) * r := by
  calc
    dist x y ≤ dist x (gridCenter r k) + dist (gridCenter r k) y :=
      dist_triangle _ _ _
    _ ≤ Real.sqrt (d : ℝ) * (r / 2) +
        Real.sqrt (d : ℝ) * (r / 2) := by
      gcongr
      · simpa [dist_eq_norm] using norm_sub_gridCenter_le hr hx
      · rw [dist_comm]
        simpa [dist_eq_norm] using norm_sub_gridCenter_le hr hy
    _ = Real.sqrt (d : ℝ) * r := by ring

/-! ## Disjoint assignment fibres and occupancy interface -/

/-- The actual assignment fibre.  These, unlike the closed cells, form a
literal partition. -/
def assignmentFiber {d : ℕ} (r : ℝ) (k : Fin d → ℕ) :
    Set (EuclideanPoint d) :=
  {x | gridIndex r x = k}

@[simp]
theorem mem_assignmentFiber_iff {d : ℕ} {r : ℝ} {k : Fin d → ℕ}
    {x : EuclideanPoint d} : x ∈ assignmentFiber r k ↔ gridIndex r x = k :=
  Iff.rfl

theorem disjoint_assignmentFiber {d : ℕ} {r : ℝ} {k l : Fin d → ℕ}
    (hkl : k ≠ l) : Disjoint (assignmentFiber r k) (assignmentFiber r l) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  exact hkl (hxk.symm.trans hxl)

/-- Every cube point belongs to exactly one candidate assignment fibre. -/
theorem existsUnique_candidate_assignmentFiber {d : ℕ} {r : ℝ} (hr : 0 < r)
    {x : EuclideanPoint d} (hx : x ∈ normalizedCube d) :
    ∃! k, k ∈ candidateGridIndices d r ∧ x ∈ assignmentFiber r k := by
  refine ⟨gridIndex r x, ⟨gridIndex_mem_candidateGridIndices hr hx, rfl⟩, ?_⟩
  intro k hk
  exact hk.2.symm

/-- Exact occupancy sum for a finite point set in the normalized cube. -/
theorem sum_grid_occupancy_eq_card {d : ℕ} {r : ℝ} (hr : 0 < r)
    (X : Finset (EuclideanPoint d)) (hX : ↑X ⊆ normalizedCube d) :
    (∑ k ∈ candidateGridIndices d r,
      DyadicCells.occupancy X (gridIndex r) k) = X.card := by
  exact DyadicCells.sum_occupancy_eq_card X (candidateGridIndices d r)
    (gridIndex r) (gridIndex_maps_finset_to_candidates hr X hX)

end

end Erdos186.PZ.ConvexDensity.GridPartition
