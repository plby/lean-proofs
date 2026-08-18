/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.ConvexGeometry
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Separation of heavy cells in a set in delta-convex position

This file formalizes the supporting-hyperplane step surrounding (3) in
Pham--Zakharov's convex-density argument.  Suppose that finitely many cells
have radius at most `r`, and that each contains a fiber of `X` having more
than `delta * |X|` points.  A supporting functional at a point in one cell
cannot put any heavy fiber entirely on its upper side.  Consequently every
other cell lies strictly below the level

`ell (a i) + 2 * ‖ell‖ * r`.

In a real Hilbert space, the Riesz representative of `ell` supplies a unit
normal direction.  Moving three radii from the center of the distinguished
cell in that direction reaches the displayed level.  Thus the closed ball
of radius `3 * r` about that center is not contained in the convex hull of
the other cells.  The constant three is the transparent diameter bookkeeping
used in the paper: one radius from the chosen point to its center and two
radii across any other cell.

The fibers are explicit finite sets.  This avoids measurability or decidable
membership assumptions on the geometric cells, and is the form needed after
the dyadic mass pigeonhole step.
-/

open Set

namespace Erdos186.PZ.ConvexDensity

open ConvexGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {ι : Type*} [DecidableEq ι]

/-- The union of the cells indexed by `I`, except for the distinguished
index `i`. -/
def otherCells (I : Finset ι) (C : ι → Set E) (i : ι) : Set E :=
  ⋃ j : {j // j ∈ I.erase i}, C j

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem mem_otherCells_iff {I : Finset ι} {C : ι → Set E} {i : ι} {x : E} :
    x ∈ otherCells I C i ↔ ∃ j ∈ I, j ≠ i ∧ x ∈ C j := by
  classical
  simp only [otherCells, mem_iUnion]
  constructor
  · rintro ⟨j, hx⟩
    exact ⟨j, Finset.mem_of_mem_erase j.property, Finset.ne_of_mem_erase j.property, hx⟩
  · rintro ⟨j, hjI, hji, hx⟩
    exact ⟨⟨j, Finset.mem_erase.mpr ⟨hji, hjI⟩⟩, hx⟩

/-- Pairwise disjointness of the cells whose indices lie in `I`.  The
separation argument below is in fact stronger and does not use disjointness;
the named predicate is provided so the final corollary can state the cell
decomposition exactly as it occurs in the application. -/
def PairwiseDisjointCellsOn (I : Finset ι) (C : ι → Set E) : Prop :=
  (I : Set ι).PairwiseDisjoint C

omit [CompleteSpace E] in
/-- Lipschitz control of a continuous linear functional, in the one-sided
form used for the cell-radius bookkeeping. -/
theorem apply_le_apply_add_opNorm_mul_of_dist_le
    (ell : E →L[ℝ] ℝ) {x y : E} {r : ℝ} (hxy : dist x y ≤ r) :
    ell x ≤ ell y + ‖ell‖ * r := by
  have hop : |ell x - ell y| ≤ ‖ell‖ * dist x y := by
    simpa [Real.dist_eq] using ell.dist_le_opNorm x y
  have hnorm : 0 ≤ ‖ell‖ := norm_nonneg _
  calc
    ell x = (ell x - ell y) + ell y := by ring
    _ ≤ |ell x - ell y| + ell y := by
      simpa [add_comm] using add_le_add_right (le_abs_self (ell x - ell y)) (ell y)
    _ ≤ (‖ell‖ * dist x y) + ell y := by
      simpa [add_comm] using add_le_add_right hop (ell y)
    _ ≤ (‖ell‖ * r) + ell y := by
      gcongr
    _ = ell y + ‖ell‖ * r := add_comm _ _

omit [CompleteSpace E] in
/-- A point in a radius-`r` cell is at functional height at most one
operator-norm radius above the center. -/
theorem apply_le_center_add_opNorm_mul
    (ell : E →L[ℝ] ℝ) {x center : E} {r : ℝ}
    (hx : x ∈ Metric.closedBall center r) :
    ell x ≤ ell center + ‖ell‖ * r :=
  apply_le_apply_add_opNorm_mul_of_dist_le ell (Metric.mem_closedBall.mp hx)

omit [CompleteSpace E] in
/-- The center is at functional height at most one operator-norm radius
above any point in its radius-`r` cell. -/
theorem center_apply_le_apply_add_opNorm_mul
    (ell : E →L[ℝ] ℝ) {x center : E} {r : ℝ}
    (hx : x ∈ Metric.closedBall center r) :
    ell center ≤ ell x + ‖ell‖ * r := by
  apply apply_le_apply_add_opNorm_mul_of_dist_le ell
  simpa [dist_comm] using Metric.mem_closedBall.mp hx

omit [CompleteSpace E] in
/-- A fixed supporting functional with the delta-convex counting bound
must take a strictly smaller value somewhere in every fiber heavier than
`delta * |X|`.  This is the literal finite counting assertion immediately
preceding the geometric cell separation. -/
theorem exists_mem_strictly_below_of_support_count
    {X Y : Finset E} {delta : ℝ} {a : E} (ell : E →L[ℝ] ℝ)
    (hcount : (halfspaceCount X ell (ell a) : ℝ) ≤ delta * X.card)
    (hYX : Y ⊆ X) (hheavy : delta * X.card < Y.card) :
    ∃ y ∈ Y, ell y < ell a := by
  classical
  by_contra hnone
  have hall : ∀ y ∈ Y, ell a ≤ ell y := by
    intro y hy
    exact le_of_not_gt (fun hylt ↦ hnone ⟨y, hy, hylt⟩)
  have hsub : Y ⊆ X.filter fun x ↦ ell a ≤ ell x := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨hYX hy, hall y hy⟩
  have hcardNat : Y.card ≤ halfspaceCount X ell (ell a) := by
    simpa only [halfspaceCount_eq_card_filter] using Finset.card_le_card hsub
  have hcardReal : (Y.card : ℝ) ≤ halfspaceCount X ell (ell a) := by
    exact_mod_cast hcardNat
  exact (not_lt_of_ge (hcardReal.trans hcount)) hheavy

/-- A nonzero continuous real functional on a Hilbert space has a unit
Riesz normal on which it takes the value of its operator norm. -/
theorem exists_unit_normal (ell : E →L[ℝ] ℝ) (hell : ell ≠ 0) :
    ∃ u : E, ‖u‖ = 1 ∧ ell u = ‖ell‖ := by
  let v : E := (InnerProductSpace.toDual ℝ E).symm ell
  have hvnorm : ‖v‖ = ‖ell‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map ell
  have hvne : v ≠ 0 := by
    intro hv
    apply hell
    have : (InnerProductSpace.toDual ℝ E) v = ell :=
      (InnerProductSpace.toDual ℝ E).apply_symm_apply ell
    simpa [hv] using this.symm
  have hnpos : 0 < ‖ell‖ := by
    rw [← hvnorm]
    exact norm_pos_iff.mpr hvne
  let u : E := (‖ell‖)⁻¹ • v
  refine ⟨u, ?_, ?_⟩
  · simp [u, norm_smul, hvnorm, hnpos.ne']
  · have hvapply : ell v = ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq v]
      exact (InnerProductSpace.toDual_symm_apply (x := v) (y := ell)).symm
    simp [u, hvapply, hvnorm, hnpos.ne', pow_two]

/--
Quantitative supporting-hyperplane separation for a finite family of heavy
radius-`r` cells.

The conclusion exposes all of the geometry used later: `ell` is nonzero,
all other cells are strictly below one common level, and a point of the
threefold enlarged distinguished ball is on or above that level.
-/
theorem exists_supporting_separator_of_heavy_cells
    {X : Finset E} {delta r : ℝ} {I : Finset ι}
    {C : ι → Set E} {Y : ι → Finset E}
    {center a : ι → E} {i : ι}
    (hr : 0 ≤ r)
    (hi : i ∈ I)
    (hX : IsDeltaConvexPosition delta X)
    (haX : ∀ j ∈ I, a j ∈ X)
    (haC : ∀ j ∈ I, a j ∈ C j)
    (hYX : ∀ j ∈ I, Y j ⊆ X)
    (hYC : ∀ j ∈ I, (Y j : Set E) ⊆ C j)
    (hheavy : ∀ j ∈ I, delta * X.card < (Y j).card)
    (hcell : ∀ j ∈ I, C j ⊆ Metric.closedBall (center j) r) :
    ∃ (ell : E →L[ℝ] ℝ) (level : ℝ) (z : E),
      ell ≠ 0 ∧
      level = ell (a i) + 2 * ‖ell‖ * r ∧
      (∀ x ∈ otherCells I C i, ell x < level) ∧
      z ∈ Metric.closedBall (center i) (3 * r) ∧
      level ≤ ell z := by
  classical
  obtain ⟨ell, hcount⟩ :=
    isDeltaConvexPosition_iff_supporting_through_point.mp hX (a i) (haX i hi)
  have hbelow : ∀ j ∈ I, ∃ y ∈ Y j, ell y < ell (a i) := by
    intro j hj
    exact exists_mem_strictly_below_of_support_count ell hcount (hYX j hj) (hheavy j hj)
  obtain ⟨yi, hyiY, hyilt⟩ := hbelow i hi
  have hell : ell ≠ 0 := by
    intro hellzero
    subst ell
    simp at hyilt
  obtain ⟨u, hunorm, hellu⟩ := exists_unit_normal ell hell
  let level : ℝ := ell (a i) + 2 * ‖ell‖ * r
  let z : E := center i + (3 * r) • u
  refine ⟨ell, level, z, hell, rfl, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hjI, _hji, hxC⟩ := mem_otherCells_iff.mp hx
    obtain ⟨y, hyY, hylt⟩ := hbelow j hjI
    have hyball : y ∈ Metric.closedBall (center j) r :=
      hcell j hjI (hYC j hjI hyY)
    have hxball : x ∈ Metric.closedBall (center j) r := hcell j hjI hxC
    have hcenter : ell (center j) ≤ ell y + ‖ell‖ * r :=
      center_apply_le_apply_add_opNorm_mul ell hyball
    have hxupper : ell x ≤ ell (center j) + ‖ell‖ * r :=
      apply_le_center_add_opNorm_mul ell hxball
    dsimp [level]
    linarith
  · rw [Metric.mem_closedBall, dist_eq_norm]
    simp [z, norm_smul, hunorm, abs_of_nonneg hr]
  · have haBall : a i ∈ Metric.closedBall (center i) r :=
      hcell i hi (haC i hi)
    have haUpper : ell (a i) ≤ ell (center i) + ‖ell‖ * r :=
      apply_le_center_add_opNorm_mul ell haBall
    have hzApply : ell z = ell (center i) + (3 * r) * ‖ell‖ := by
      simp [z, hellu]
    dsimp [level]
    rw [hzApply]
    nlinarith [norm_nonneg ell]

/-- The threefold enlargement of a heavy cell is not contained in the
convex hull of all the other heavy cells.  No disjointness assumption is
needed for this stronger form. -/
theorem thickenedCell_not_subset_convexHull_others_of_heavy_fibers
    {X : Finset E} {delta r : ℝ} {I : Finset ι}
    {C : ι → Set E} {Y : ι → Finset E}
    {center a : ι → E} {i : ι}
    (hr : 0 ≤ r)
    (hi : i ∈ I)
    (hX : IsDeltaConvexPosition delta X)
    (haX : ∀ j ∈ I, a j ∈ X)
    (haC : ∀ j ∈ I, a j ∈ C j)
    (hYX : ∀ j ∈ I, Y j ⊆ X)
    (hYC : ∀ j ∈ I, (Y j : Set E) ⊆ C j)
    (hheavy : ∀ j ∈ I, delta * X.card < (Y j).card)
    (hcell : ∀ j ∈ I, C j ⊆ Metric.closedBall (center j) r) :
    ¬ Metric.closedBall (center i) (3 * r) ⊆
      convexHull ℝ (otherCells I C i) := by
  obtain ⟨ell, level, z, _hell, _hlevel, hother, hzball, hzlevel⟩ :=
    exists_supporting_separator_of_heavy_cells hr hi hX haX haC hYX hYC hheavy hcell
  refine fun hsubset ↦ ?_
  have hotherSub : otherCells I C i ⊆ strictLowerHalfspace ell level := hother
  have hhull : convexHull ℝ (otherCells I C i) ⊆ strictLowerHalfspace ell level :=
    convexHull_min hotherSub (convex_strictLowerHalfspace ell level)
  exact (not_lt_of_ge hzlevel) (hhull (hsubset hzball))

/-- Equation-(3) form for pairwise disjoint occupied cells.  Pairwise
disjointness records the geometric decomposition used in the application;
the proof only requires the stronger heavy-fiber hypotheses above. -/
theorem thickenedCell_not_subset_convexHull_others
    {X : Finset E} {delta r : ℝ} {I : Finset ι}
    {C : ι → Set E} {Y : ι → Finset E}
    {center a : ι → E} {i : ι}
    (hr : 0 ≤ r)
    (hi : i ∈ I)
    (_hdisjoint : PairwiseDisjointCellsOn I C)
    (hX : IsDeltaConvexPosition delta X)
    (haX : ∀ j ∈ I, a j ∈ X)
    (haC : ∀ j ∈ I, a j ∈ C j)
    (hYX : ∀ j ∈ I, Y j ⊆ X)
    (hYC : ∀ j ∈ I, (Y j : Set E) ⊆ C j)
    (hheavy : ∀ j ∈ I, delta * X.card < (Y j).card)
    (hcell : ∀ j ∈ I, C j ⊆ Metric.closedBall (center j) r) :
    ¬ Metric.closedBall (center i) (3 * r) ⊆
      convexHull ℝ (otherCells I C i) := by
  exact thickenedCell_not_subset_convexHull_others_of_heavy_fibers
    hr hi hX haX haC hYX hYC hheavy hcell

end

end Erdos186.PZ.ConvexDensity
