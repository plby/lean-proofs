import ErdosProblems.Erdos633.NormalizedSides
import ErdosProblems.Erdos633.TriangleUpperModel

/-!
# Intrinsic side-and-sine area equations

The determinant formula and an isometric upper-half-plane model give the
Euclidean side-and-sine area formula. The positive area of the standard
triangle cancels from every tiling equation, so its numerical value is not
needed. All normalized equations below follow from actual area additivity.
-/

namespace Erdos633

theorem Triangle.det_coordinateLinearMap (P : Triangle) :
    LinearMap.det P.coordinateLinearMap = orientedDoubleArea P.a P.b P.c := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Triangle.coordinateLinearMap, orientedDoubleArea, mul_comm]

theorem Triangle.det_coordinateEquiv (P : Triangle) :
    LinearMap.det (P.coordinateEquiv.linear : ℂ →ₗ[ℝ] ℂ) =
      orientedDoubleArea P.a P.b P.c := by
  change LinearMap.det P.coordinateLinearMap = _
  exact P.det_coordinateLinearMap

theorem Triangle.area_eq_abs_orientedDoubleArea_mul_standard (P : Triangle) :
    P.area = |orientedDoubleArea P.a P.b P.c| * standardTriangle.area := by
  have h := standardTriangle.area_mapAffineEquiv P.coordinateEquiv
  rwa [P.standard_map_coordinateEquiv, P.det_coordinateEquiv] at h

theorem Triangle.area_mapIsometry (P : Triangle) (e : ℂ ≃ᵢ ℂ) :
    (P.mapIsometry e).area = P.area := by
  unfold Triangle.area
  rw [P.mapIsometry_carrier, isometry_volume_image]

theorem Triangle.area_eq_dist_mul_sin (P : Triangle) :
    P.area = dist P.a P.b * dist P.a P.c * Real.sin P.angleA * standardTriangle.area := by
  have hm : P.upperModel.area = P.area := by
    rw [← P.map_upperIsometry, P.area_mapIsometry]
  calc
    P.area = P.upperModel.area := hm.symm
    _ = |orientedDoubleArea P.upperModel.a P.upperModel.b P.upperModel.c| *
        standardTriangle.area := P.upperModel.area_eq_abs_orientedDoubleArea_mul_standard
    _ = _ := by
      change |(dist P.a P.b - 0) * (P.upperPoint.im - 0) -
        (0 - 0) * (P.upperPoint.re - 0)| * standardTriangle.area = _
      simp only [sub_zero, zero_mul]
      rw [abs_of_pos (mul_pos (dist_pos.mpr P.a_ne_b) P.upperPoint_im_pos)]
      change dist P.a P.b * (dist P.a P.c * Real.sin P.angleA) * _ = _
      ring

theorem Triangle.area_eq_sideLength_mul_sin (P : Triangle) :
    P.area = P.sideLength 1 * P.sideLength 2 * Real.sin P.angleA *
      standardTriangle.area := by
  rw [P.area_eq_dist_mul_sin]
  change dist P.a P.b * dist P.a P.c * Real.sin P.angleA * _ =
    dist P.c P.a * dist P.a P.b * Real.sin P.angleA * _
  rw [dist_comm P.c P.a]
  ring

theorem CongruentTiling.side_sine_area_equation
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) :
    P.sideLength 1 * P.sideLength 2 * Real.sin P.angleA =
      (N : ℝ) * R.sideLength 1 * R.sideLength 2 * Real.sin R.angleA := by
  apply mul_right_cancel₀ (ne_of_gt standardTriangle.area_pos)
  calc
    _ = P.area := P.area_eq_sideLength_mul_sin.symm
    _ = (N : ℝ) * R.area := T.area_eq
    _ = _ := by rw [R.area_eq_sideLength_mul_sin]; ring

theorem CongruentTiling.normalized_area_equation
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) :
    (P.sideLength 1 / R.sideLength 2) * (P.sideLength 2 / R.sideLength 2) *
        Real.sin P.angleA =
      (N : ℝ) * R.normalizedSide 1 * Real.sin R.angleA := by
  unfold Triangle.normalizedSide
  calc
    _ = (P.sideLength 1 * P.sideLength 2 * Real.sin P.angleA) / R.sideLength 2 ^ 2 := by
      ring
    _ = ((N : ℝ) * R.sideLength 1 * R.sideLength 2 * Real.sin R.angleA) /
        R.sideLength 2 ^ 2 := by rw [T.side_sine_area_equation]
    _ = _ := by field_simp [ne_of_gt (R.sideLength_pos 2)]

theorem CongruentTiling.normalized_area_equation_same_angle
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hA : P.angleA = R.angleA) :
    (P.sideLength 1 / R.sideLength 2) * (P.sideLength 2 / R.sideLength 2) =
      (N : ℝ) * R.normalizedSide 1 := by
  apply mul_right_cancel₀ (ne_of_gt R.sin_angleA_pos)
  simpa only [hA] using T.normalized_area_equation

theorem CongruentTiling.normalized_area_equation_double_angle
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hA : P.angleA = 2 * R.angleA) :
    (P.sideLength 1 / R.sideLength 2) * (P.sideLength 2 / R.sideLength 2) *
        (2 * Real.cos R.angleA) = (N : ℝ) * R.normalizedSide 1 := by
  have h := T.normalized_area_equation
  rw [hA, Real.sin_two_mul] at h
  apply mul_right_cancel₀ (ne_of_gt R.sin_angleA_pos)
  convert h using 1
  ring

end Erdos633
