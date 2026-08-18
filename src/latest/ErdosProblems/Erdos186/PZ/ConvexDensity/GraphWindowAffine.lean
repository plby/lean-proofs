/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphWindowNormalization
import ErdosProblems.Erdos186.PZ.ConvexDensity.NormalizedCore

/-! # The graph-window normalization as an affine equivalence -/

open Set

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- The linear part of graph-window normalization: base coordinates are
divided by `2q`, and the last coordinate is divided by `outer`. -/
def graphWindowLinearMap {n : ℕ} (q outer : ℝ) :
    EuclideanPoint (n + 1) →ₗ[ℝ] EuclideanPoint (n + 1) where
  toFun z := appendCoordinate
    ((2 * q)⁻¹ • baseCoordinates z) (outer⁻¹ * lastCoordinate z)
  map_add' x y := by
    apply (lastCoordinateCLE n).injective
    apply Prod.ext
    · ext i
      simp [mul_add]
    · simp [lastCoordinate, coordinate, mul_add]
  map_smul' a x := by
    apply (lastCoordinateCLE n).injective
    apply Prod.ext
    · ext i
      simp [mul_assoc]
      ring
    · simp [lastCoordinate, coordinate]
      ring

@[simp]
theorem graphWindowLinearMap_apply {n : ℕ} (q outer : ℝ)
    (z : EuclideanPoint (n + 1)) :
    graphWindowLinearMap q outer z = appendCoordinate
      ((2 * q)⁻¹ • baseCoordinates z) (outer⁻¹ * lastCoordinate z) :=
  rfl

/-- The inverse linear map before bundling. -/
def graphWindowLinearInverse {n : ℕ} (q outer : ℝ)
    (z : EuclideanPoint (n + 1)) : EuclideanPoint (n + 1) :=
  appendCoordinate ((2 * q) • baseCoordinates z)
    (outer * lastCoordinate z)

theorem graphWindowLinearMap_bijective {n : ℕ} {q outer : ℝ}
    (hq : q ≠ 0) (houter : outer ≠ 0) :
    Function.Bijective (graphWindowLinearMap (n := n) q outer) := by
  have hleft : ∀ z : EuclideanPoint (n + 1),
      graphWindowLinearInverse q outer (graphWindowLinearMap q outer z) = z := by
    intro z
    apply (lastCoordinateCLE n).injective
    apply Prod.ext
    · ext i
      simp [graphWindowLinearInverse, graphWindowLinearMap]
      field_simp
    · simp [graphWindowLinearInverse, graphWindowLinearMap, houter]
  have hright : ∀ z : EuclideanPoint (n + 1),
      graphWindowLinearMap q outer (graphWindowLinearInverse q outer z) = z := by
    intro z
    apply (lastCoordinateCLE n).injective
    apply Prod.ext
    · ext i
      simp [graphWindowLinearInverse, graphWindowLinearMap]
      field_simp
    · simp [graphWindowLinearInverse, graphWindowLinearMap, houter]
  constructor
  · intro x y hxy
    rw [← hleft x, ← hleft y, hxy]
  · intro y
    refine ⟨graphWindowLinearInverse q outer y, ?_⟩
    exact hright y

/-- Invertible linear graph-window normalization. -/
def graphWindowLinearEquiv {n : ℕ} (q outer : ℝ)
    (hq : q ≠ 0) (houter : outer ≠ 0) :
    EuclideanPoint (n + 1) ≃ₗ[ℝ] EuclideanPoint (n + 1) :=
  LinearEquiv.ofBijective (graphWindowLinearMap q outer)
    (graphWindowLinearMap_bijective hq houter)

@[simp]
theorem graphWindowLinearEquiv_apply {n : ℕ} (q outer : ℝ)
    (hq : q ≠ 0) (houter : outer ≠ 0) (z : EuclideanPoint (n + 1)) :
    graphWindowLinearEquiv q outer hq houter z =
      graphWindowLinearMap q outer z :=
  rfl

/-- The base translation which turns the physical window `[-q,q]^n` into
the unit window `[0,1]^n`. -/
def graphWindowShift {n : ℕ} : EuclideanPoint (n + 1) :=
  appendCoordinate (WithLp.toLp 2 (fun _ : Fin n ↦ (1 / 2 : ℝ))) 0

/-- The complete graph-window affine equivalence. -/
def graphWindowAffineEquiv {n : ℕ} (q outer : ℝ)
    (hq : q ≠ 0) (houter : outer ≠ 0) :
    EuclideanPoint (n + 1) ≃ᵃ[ℝ] EuclideanPoint (n + 1) :=
  (graphWindowLinearEquiv q outer hq houter).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (EuclideanPoint (n + 1)) (graphWindowShift (n := n)))

@[simp]
theorem graphWindowAffineEquiv_apply {n : ℕ} {q outer : ℝ}
    (hq : q ≠ 0) (houter : outer ≠ 0) (z : EuclideanPoint (n + 1)) :
    graphWindowAffineEquiv q outer hq houter z = normalizeGraphPoint q outer z := by
  apply (lastCoordinateCLE n).injective
  apply Prod.ext
  · ext i
    simp [graphWindowAffineEquiv, graphWindowShift, graphWindowLinearMap,
      normalizeGraphPoint]
    field_simp
    ring
  · simp [graphWindowAffineEquiv, graphWindowShift, graphWindowLinearMap,
      normalizeGraphPoint, lastCoordinate, coordinate]
    ring

/-- Convex-density output can be transported through graph-window
normalization with no loss in the relative-volume or cardinality clauses. -/
theorem convexDensityOutput_graphWindowAffineEquiv_iff
    {n : ℕ} {q outer : ℝ} (hq : q ≠ 0) (houter : outer ≠ 0)
    (epsilon tau delta : ℝ) (Omega : Set (EuclideanPoint (n + 1)))
    (X : Finset (EuclideanPoint (n + 1))) :
    ConvexDensityOutput epsilon tau delta
        (graphWindowAffineEquiv q outer hq houter '' Omega)
        (affineEquivImageFinset (graphWindowAffineEquiv q outer hq houter) X) ↔
      ConvexDensityOutput epsilon tau delta Omega X :=
  convexDensityOutput_affineEquivImage_iff
    (graphWindowAffineEquiv q outer hq houter) epsilon tau delta Omega X

/-! ## Quantitative distance control -/

/-- A convenient `l¹` upper bound for the norm after appending one
coordinate. -/
theorem norm_appendCoordinate_le_add {n : ℕ}
    (x : EuclideanPoint n) (t : ℝ) :
    ‖appendCoordinate x t‖ ≤ ‖x‖ + |t| := by
  have hsplit : appendCoordinate x t =
      appendCoordinate x 0 + appendCoordinate 0 t := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  rw [hsplit]
  calc
    ‖appendCoordinate x 0 + appendCoordinate 0 t‖ ≤
        ‖appendCoordinate x 0‖ + ‖appendCoordinate 0 t‖ := norm_add_le _ _
    _ = ‖x‖ + |t| := by
      rw [norm_appendCoordinate_zero]
      have hsquare := norm_appendCoordinate_sq (0 : EuclideanPoint n) t
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_add] at hsquare
      congr 1
      nlinarith [norm_nonneg (appendCoordinate (0 : EuclideanPoint n) t),
        abs_nonneg t]

/-- The anisotropic graph-window normalization has the displayed elementary
Lipschitz constant. -/
theorem dist_graphWindowAffineEquiv_le {n : ℕ} {q outer : ℝ}
    (hq : 0 < q) (houter : 0 < outer)
    (x y : EuclideanPoint (n + 1)) :
    dist (graphWindowAffineEquiv q outer hq.ne' houter.ne' x)
        (graphWindowAffineEquiv q outer hq.ne' houter.ne' y) ≤
      ((2 * q)⁻¹ + outer⁻¹) * dist x y := by
  rw [graphWindowAffineEquiv_apply hq.ne' houter.ne',
    graphWindowAffineEquiv_apply hq.ne' houter.ne', dist_eq_norm]
  have hsub : normalizeGraphPoint q outer x - normalizeGraphPoint q outer y =
      graphWindowLinearMap q outer (x - y) := by
    apply (lastCoordinateCLE n).injective
    apply Prod.ext
    · ext i
      simp [normalizeGraphPoint, graphWindowLinearMap]
      ring
    · simp [normalizeGraphPoint, graphWindowLinearMap, lastCoordinate, coordinate]
      ring
  rw [hsub]
  let z := x - y
  have hbase := norm_baseCoordinates_le_norm z
  have hlast := abs_lastCoordinate_le_norm z
  have hinvq : 0 ≤ (2 * q)⁻¹ := inv_nonneg.mpr (by positivity)
  have hinvouter : 0 ≤ outer⁻¹ := inv_nonneg.mpr houter.le
  calc
    ‖graphWindowLinearMap q outer z‖ ≤
        ‖(2 * q)⁻¹ • baseCoordinates z‖ +
          |outer⁻¹ * lastCoordinate z| :=
      norm_appendCoordinate_le_add _ _
    _ = (2 * q)⁻¹ * ‖baseCoordinates z‖ +
          outer⁻¹ * |lastCoordinate z| := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinvq,
        abs_mul, abs_of_nonneg hinvouter]
    _ ≤ ((2 * q)⁻¹ + outer⁻¹) * ‖z‖ := by
      nlinarith [norm_nonneg (baseCoordinates z), norm_nonneg z,
        abs_nonneg (lastCoordinate z)]
    _ = ((2 * q)⁻¹ + outer⁻¹) * dist x y := by
      rw [dist_eq_norm]

/-- The complete physical graph chart: translate the inball centre to zero,
apply the cap-selected Householder reflection, and normalize the graph
window. -/
def centeredGraphWindowAffineEquiv {n : ℕ}
    (center direction : EuclideanPoint (n + 1))
    (q outer : ℝ) (hq : q ≠ 0) (houter : outer ≠ 0) :
    EuclideanPoint (n + 1) ≃ᵃ[ℝ] EuclideanPoint (n + 1) :=
  (centeredHouseholderEquiv center direction).toAffineEquiv.trans
    (graphWindowAffineEquiv q outer hq houter)

@[simp]
theorem centeredGraphWindowAffineEquiv_apply {n : ℕ}
    (center direction : EuclideanPoint (n + 1))
    {q outer : ℝ} (hq : q ≠ 0) (houter : outer ≠ 0)
    (z : EuclideanPoint (n + 1)) :
    centeredGraphWindowAffineEquiv center direction q outer hq houter z =
      normalizeGraphPoint q outer
        (centeredHouseholderEquiv center direction z) := by
  simp [centeredGraphWindowAffineEquiv]

end
end Erdos186.PZ.ConvexDensity
