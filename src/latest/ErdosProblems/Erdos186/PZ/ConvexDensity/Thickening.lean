/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.AxisBoxes

/-!
# Elementary volume bounds for Euclidean thickenings

This file bounds Minkowski sums with a closed ball by explicit boxes.  The
main estimate is adapted to an affine graph slab: perturbing the base by at
most `r` enlarges every base interval by `r` at both ends, and perturbing the
height enlarges the half-thickness by

`r * (1 + \sum i, slope i)`.

Here `slope i` bounds the absolute value of the `i`th coordinate coefficient
of the linear part of the affine map.  The resulting volume bound is stated
directly in the product model `EuclideanPoint d × ℝ`; it does not depend on a
choice of linear equivalence with another model of `(d+1)`-space.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

/-- Minkowski addition with the radius-`r` closed ball centred at zero. -/
def minkowskiClosedBall {E : Type*} [NormedAddCommGroup E]
    (s : Set E) (r : ℝ) : Set E :=
  s + Metric.closedBall 0 r

@[simp]
theorem mem_minkowskiClosedBall {E : Type*} [NormedAddCommGroup E]
    {s : Set E} {r : ℝ} {x : E} :
    x ∈ minkowskiClosedBall s r ↔
      ∃ a ∈ s, ∃ b ∈ Metric.closedBall (0 : E) r, a + b = x :=
  Iff.rfl

/-- A radius-`r` thickening of an axis box is contained in the box obtained
by moving every face outwards by `r`. -/
theorem minkowskiClosedBall_closedAxisBox_subset {d : ℕ}
    (lower upper : Fin d → ℝ) (r : ℝ) :
    minkowskiClosedBall (closedAxisBox lower upper) r ⊆
      closedAxisBox (fun i ↦ lower i - r) (fun i ↦ upper i + r) := by
  rintro x ⟨a, ha, b, hb, rfl⟩ i
  have hbnorm : ‖b‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hb
  have hcoord : |coordinate b i| ≤ r := by
    simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le b i).trans hbnorm
  have hneg : -r ≤ coordinate b i := (abs_le.mp hcoord).1
  have hpos : coordinate b i ≤ r := (abs_le.mp hcoord).2
  constructor
  · change lower i - r ≤ coordinate a i + coordinate b i
    linarith [(ha i).1]
  · change coordinate a i + coordinate b i ≤ upper i + r
    linarith [(ha i).2]

/-- Explicit volume bound for a thickened axis box. -/
theorem volume_minkowskiClosedBall_closedAxisBox_le {d : ℕ}
    (lower upper : Fin d → ℝ) (r : ℝ) :
    volume (minkowskiClosedBall (closedAxisBox lower upper) r) ≤
      ∏ i, ENNReal.ofReal (upper i - lower i + 2 * r) := by
  refine (measure_mono (minkowskiClosedBall_closedAxisBox_subset lower upper r)).trans_eq ?_
  rw [volume_closedAxisBox]
  congr 1
  funext i
  congr 1
  ring

/-- If `r` is at most `kappa` times every side length, then every side of
the enclosing thickened box is at most `(1 + 2*kappa)` times its old length. -/
theorem volume_minkowskiClosedBall_closedAxisBox_le_of_controlledRadius
    {d : ℕ} {lower upper : Fin d → ℝ} {r kappa : ℝ}
    (_hr : 0 ≤ r) (_hkappa : 0 ≤ kappa)
    (hordered : lower ≤ upper)
    (hcontrol : ∀ i, r ≤ kappa * (upper i - lower i)) :
    volume (minkowskiClosedBall (closedAxisBox lower upper) r) ≤
      ∏ i, ENNReal.ofReal ((1 + 2 * kappa) * (upper i - lower i)) := by
  refine (volume_minkowskiClosedBall_closedAxisBox_le lower upper r).trans ?_
  gcongr with i hi
  have hw : 0 ≤ upper i - lower i := sub_nonneg.mpr (hordered i)
  nlinarith [hcontrol i]

/-- The coefficient of the `i`th Euclidean coordinate in the linear part of
an affine functional. -/
def affineCoordinateCoefficient {d : ℕ}
    (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (i : Fin d) : ℝ :=
  L.linear (EuclideanSpace.single i 1)

/-- Coordinate expansion of the linear part of an affine functional. -/
theorem affine_linear_eq_sum_coordinates {d : ℕ}
    (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (u : EuclideanPoint d) :
    L.linear u =
      ∑ i, coordinate u i * affineCoordinateCoefficient L i := by
  classical
  have hu : u = ∑ i, coordinate u i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp only [coordinate, WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, PiLp.ofLp_single]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      have hji : j ≠ i := Ne.symm hij
      simp [hji]
    · simp
  calc
    L.linear u =
        L.linear (∑ i, coordinate u i • EuclideanSpace.single i (1 : ℝ)) :=
      congrArg L.linear hu
    _ = ∑ i, L.linear
        (coordinate u i • EuclideanSpace.single i (1 : ℝ)) := by
      rw [map_sum]
    _ = ∑ i, coordinate u i * affineCoordinateCoefficient L i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [affineCoordinateCoefficient]

/-- Absolute-value estimate obtained from coordinate coefficient bounds. -/
theorem abs_affine_linear_le_sum {d : ℕ}
    (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (slope : Fin d → ℝ)
    (hcoeff : ∀ i, |affineCoordinateCoefficient L i| ≤ slope i)
    (u : EuclideanPoint d) :
    |L.linear u| ≤ ∑ i, slope i * |coordinate u i| := by
  rw [affine_linear_eq_sum_coordinates]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left (hcoeff i) (abs_nonneg (coordinate u i))

/-- A coefficient-bounded affine functional changes by at most
`r * ∑ i, slope i` on a vector of norm at most `r`. -/
theorem abs_affine_linear_le_radius_mul_sum {d : ℕ}
    (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (slope : Fin d → ℝ)
    (hcoeff : ∀ i, |affineCoordinateCoefficient L i| ≤ slope i)
    {u : EuclideanPoint d} {r : ℝ} (hu : ‖u‖ ≤ r) :
    |L.linear u| ≤ r * ∑ i, slope i := by
  refine (abs_affine_linear_le_sum L slope hcoeff u).trans ?_
  calc
    ∑ i, slope i * |coordinate u i| ≤
        ∑ i, slope i * r := by
      apply Finset.sum_le_sum
      intro i hi
      have hslope : 0 ≤ slope i :=
        (abs_nonneg (affineCoordinateCoefficient L i)).trans (hcoeff i)
      have hcoordinate : |coordinate u i| ≤ r := by
        simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le u i).trans hu
      exact mul_le_mul_of_nonneg_left hcoordinate hslope
    _ = r * ∑ i, slope i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- A closed-ball thickening of an affine graph slab is contained in the
same graph slab over the enlarged base box.  Its new half-thickness is
`epsilon + r * (1 + ∑ i, slope i)`. -/
theorem minkowskiClosedBall_affineGraphSlab_subset {d : ℕ}
    (lower upper : Fin d → ℝ) (L : EuclideanPoint d →ᵃ[ℝ] ℝ)
    (slope : Fin d → ℝ) (epsilon r : ℝ)
    (hcoeff : ∀ i, |affineCoordinateCoefficient L i| ≤ slope i) :
    minkowskiClosedBall
        (affineGraphSlab (closedAxisBox lower upper) L epsilon) r ⊆
      affineGraphSlab
        (closedAxisBox (fun i ↦ lower i - r) (fun i ↦ upper i + r)) L
        (epsilon + r * (1 + ∑ i, slope i)) := by
  rintro p ⟨a, ha, b, hb, rfl⟩
  have hbnorm : ‖b‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hb
  have hbbase_norm : ‖b.1‖ ≤ r := (norm_fst_le b).trans hbnorm
  have hbheight_abs : |b.2| ≤ r :=
    (norm_snd_le b).trans hbnorm
  have hlinear_abs : |L.linear b.1| ≤ r * ∑ i, slope i :=
    abs_affine_linear_le_radius_mul_sum L slope hcoeff hbbase_norm
  have hL : L (a.1 + b.1) = L a.1 + L.linear b.1 := by
    simpa [vadd_eq_add, add_comm] using L.map_vadd a.1 b.1
  refine ⟨?_, ?_, ?_⟩
  · exact minkowskiClosedBall_closedAxisBox_subset lower upper r
      ⟨a.1, ha.1, b.1, by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hbbase_norm, rfl⟩
  · change L (a.1 + b.1) - (epsilon + r * (1 + ∑ i, slope i)) ≤
      a.2 + b.2
    rw [hL]
    have hbheight := (abs_le.mp hbheight_abs).1
    have hlinear := (abs_le.mp hlinear_abs).2
    linarith [ha.2.1]
  · change a.2 + b.2 ≤
      L (a.1 + b.1) + (epsilon + r * (1 + ∑ i, slope i))
    rw [hL]
    have hbheight := (abs_le.mp hbheight_abs).2
    have hlinear := (abs_le.mp hlinear_abs).1
    linarith [ha.2.2]

/-- Conversion-independent product-volume bound for any set lying in the
explicit enlarged affine graph slab. -/
theorem volume_le_enlarged_affineGraphSlab {d : ℕ}
    {T : Set (EuclideanPoint d × ℝ)}
    (lower upper : Fin d → ℝ) (L : EuclideanPoint d →ᵃ[ℝ] ℝ)
    (slope : Fin d → ℝ) (epsilon r : ℝ)
    (hepsilon : 0 ≤ epsilon) (hr : 0 ≤ r)
    (hslope : ∀ i, 0 ≤ slope i)
    (hT : T ⊆
      affineGraphSlab
        (closedAxisBox (fun i ↦ lower i - r) (fun i ↦ upper i + r)) L
        (epsilon + r * (1 + ∑ i, slope i))) :
    volume T ≤
      (∏ i, ENNReal.ofReal (upper i - lower i + 2 * r)) *
        ENNReal.ofReal (2 * (epsilon + r * (1 + ∑ i, slope i))) := by
  have hnew : 0 ≤ epsilon + r * (1 + ∑ i, slope i) := by
    have hsum : 0 ≤ ∑ i, slope i := Finset.sum_nonneg fun i hi ↦ hslope i
    positivity
  refine (measure_mono hT).trans_eq ?_
  rw [volume_affineGraphSlab_closedAxisBox _ _ L hnew]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring

/-- Explicit product-volume bound for a ball-thickened affine graph slab. -/
theorem volume_minkowskiClosedBall_affineGraphSlab_le {d : ℕ}
    (lower upper : Fin d → ℝ) (L : EuclideanPoint d →ᵃ[ℝ] ℝ)
    (slope : Fin d → ℝ) (epsilon r : ℝ)
    (hepsilon : 0 ≤ epsilon) (hr : 0 ≤ r)
    (hslope : ∀ i, 0 ≤ slope i)
    (hcoeff : ∀ i, |affineCoordinateCoefficient L i| ≤ slope i) :
    volume (minkowskiClosedBall
      (affineGraphSlab (closedAxisBox lower upper) L epsilon) r) ≤
      (∏ i, ENNReal.ofReal (upper i - lower i + 2 * r)) *
        ENNReal.ofReal (2 * (epsilon + r * (1 + ∑ i, slope i))) := by
  apply volume_le_enlarged_affineGraphSlab lower upper L slope epsilon r
    hepsilon hr hslope
  exact minkowskiClosedBall_affineGraphSlab_subset
    lower upper L slope epsilon r hcoeff

/-- Controlled-radius version: if `r ≤ kappa * width i`, then the base
factor in the graph-slab thickening estimate may be replaced by the product
of `(1 + 2*kappa) * width i`. -/
theorem volume_minkowskiClosedBall_affineGraphSlab_le_of_controlledRadius
    {d : ℕ} {lower upper : Fin d → ℝ}
    (L : EuclideanPoint d →ᵃ[ℝ] ℝ) (slope : Fin d → ℝ)
    {epsilon r kappa : ℝ}
    (hepsilon : 0 ≤ epsilon) (hr : 0 ≤ r) (_hkappa : 0 ≤ kappa)
    (hordered : lower ≤ upper)
    (hcontrol : ∀ i, r ≤ kappa * (upper i - lower i))
    (hslope : ∀ i, 0 ≤ slope i)
    (hcoeff : ∀ i, |affineCoordinateCoefficient L i| ≤ slope i) :
    volume (minkowskiClosedBall
      (affineGraphSlab (closedAxisBox lower upper) L epsilon) r) ≤
      (∏ i, ENNReal.ofReal
        ((1 + 2 * kappa) * (upper i - lower i))) *
        ENNReal.ofReal (2 * (epsilon + r * (1 + ∑ i, slope i))) := by
  refine (volume_minkowskiClosedBall_affineGraphSlab_le
    lower upper L slope epsilon r hepsilon hr hslope hcoeff).trans ?_
  gcongr with i hi
  have hw : 0 ≤ upper i - lower i := sub_nonneg.mpr (hordered i)
  nlinarith [hcontrol i]

end

end Erdos186.PZ.ConvexDensity
