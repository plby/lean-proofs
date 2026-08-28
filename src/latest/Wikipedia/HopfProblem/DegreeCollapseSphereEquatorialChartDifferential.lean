import Wikipedia.HopfProblem.DegreeCollapseSphereCenteredAmbientChart

/-!
# Differentiating the original sphere chart along its equator

The value of the chart on the equator is twice its fixed linear part.
Its ambient derivative also differentiates the denominator: this contributes
the rank-one term below. The chosen orthonormal coordinates are unchanged.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereEquatorialChartDifferential

open NoExoticSixSphere SphereCenteredAmbientChart
open Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

variable {n : ℕ}

theorem ambientChart_formula (z : Sphere n) (y : V (n + 1)) :
    ambientChart z y = (2 / (1 + inner ℝ z.val y)) • linearPart z y := by
  change coordinates z ((2 / (1 - inner ℝ (-z.val) y)) •
    (Tangent z).orthogonalProjectionOnto y) = _
  rw [map_smul, inner_neg_left, sub_neg_eq_add]
  rfl

theorem hasFDerivAt_coefficient (z : Sphere n) (x : V (n + 1))
    (hx : inner ℝ z.val x = 0) :
    HasFDerivAt (fun y ↦ 2 / (1 + inner ℝ z.val y))
      ((-2 : ℝ) • innerSL ℝ z.val) x := by
  have hd := ((innerSL ℝ z.val).hasFDerivAt (x := x)).const_add 1
  have hn : 1 + inner ℝ z.val x ≠ 0 := by rw [hx]; norm_num
  have hi := (hasDerivAt_inv hn).comp_hasFDerivAt x hd
  convert! hi.const_mul 2 using 1
  ext y
  simp [hx]

def differential (z : Sphere n) (x : V (n + 1)) : V (n + 1) →L[ℝ] V n :=
  (2 : ℝ) • linearPart z -
    ContinuousLinearMap.smulRight ((2 : ℝ) • innerSL ℝ z.val) (linearPart z x)

theorem differential_apply (z : Sphere n) (x v : V (n + 1)) :
    differential z x v = (2 : ℝ) • linearPart z v -
      (2 * inner ℝ z.val v) • linearPart z x := rfl

theorem hasFDerivAt_ambientChart (z : Sphere n) (x : V (n + 1))
    (hx : inner ℝ z.val x = 0) :
    HasFDerivAt (ambientChart z) (differential z x) x := by
  have h := (hasFDerivAt_coefficient z x hx).smul (linearPart z).hasFDerivAt
  convert! h using 1
  · funext y
    exact ambientChart_formula z y
  · ext v
    simp [differential, hx, sub_eq_add_neg, neg_smul]

theorem fderiv_ambientChart (z : Sphere n) (x : V (n + 1))
    (hx : inner ℝ z.val x = 0) :
    fderiv ℝ (ambientChart z) x = differential z x :=
  (hasFDerivAt_ambientChart z x hx).fderiv

theorem differential_equatorial (z : Sphere n) (x v : V (n + 1))
    (hv : inner ℝ z.val v = 0) :
    differential z x v = (2 : ℝ) • linearPart z v := by
  rw [differential_apply, hv, mul_zero, zero_smul, sub_zero]

theorem linearPart_inner (z : Sphere n) (u v : V (n + 1)) :
    inner ℝ (linearPart z u) (linearPart z v) =
      inner ℝ u v - inner ℝ z.val u * inner ℝ z.val v := by
  have h := (coordinates z).symm.inner_map_map (linearPart z u) (linearPart z v)
  change inner ℝ (tangentLift z (linearPart z u)) (tangentLift z (linearPart z v)) = _ at h
  rw [tangentLift_linearPart, tangentLift_linearPart,
    SphereRadialDifferential.tangentProjection_apply,
    SphereRadialDifferential.tangentProjection_apply] at h
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm,
    one_pow, mul_one] at h
  calc
    inner ℝ (linearPart z u) (linearPart z v) =
        inner ℝ u v - inner ℝ u z.val * inner ℝ z.val v := by nlinarith [h]
    _ = _ := by rw [real_inner_comm u z.val]

theorem differential_inner_tangent (z x : Sphere n) (hx : inner ℝ z.val x.val = 0)
    (u v : V (n + 1)) (hu : inner ℝ x.val u = 0) (hv : inner ℝ x.val v = 0) :
    inner ℝ (differential z x.val u) (differential z x.val v) = 4 * inner ℝ u v := by
  have hu' : inner ℝ u x.val = 0 := (real_inner_comm _ _).trans hu
  have hxx : inner ℝ x.val x.val = 1 := by
    rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow]
  rw [differential_apply, differential_apply]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    linearPart_inner, hx, hu', hv, hxx, mul_zero, zero_mul, sub_zero]
  ring

theorem half_differential_norm (z x : Sphere n) (hx : inner ℝ z.val x.val = 0)
    (v : V (n + 1)) (hv : inner ℝ x.val v = 0) :
    ‖(1 / 2 : ℝ) • differential z x.val v‖ = ‖v‖ := by
  have h := differential_inner_tangent z x hx v v hv hv
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [norm_smul, Real.norm_eq_abs]
  norm_num
  nlinarith [norm_nonneg (differential z x.val v), norm_nonneg v]

end Wikipedia.HopfProblem.DegreeCollapse.SphereEquatorialChartDifferential
