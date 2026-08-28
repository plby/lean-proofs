import Wikipedia.NoExoticSixSphere.QuaternionicHopfChartEquations

/-!
# The explicit right inverse in the original Hopf source chart

The pole component of right quaternion multiplication is removed and
inserted in the radial direction of the actual south fiber. The fixed
source and target coordinate maps are retained in the inverse formula.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def chartNormalAmbient (q : Sphere 3) : ℍ →L[ℝ] V 8 :=
  let R := (ContinuousLinearMap.mul ℝ ℍ).flip (second (southFiberPoint q).val)
  let r := (innerSL ℝ (1 : ℍ)).comp R
  firstAxis.comp R - (ContinuousLinearMap.toSpanSingleton ℝ (spherePole 7).val).comp r +
    (ContinuousLinearMap.toSpanSingleton ℝ (southFiberPoint q).val).comp r

theorem chartNormalAmbient_apply (q : Sphere 3) (w : ℍ) :
    chartNormalAmbient q w = firstAxis (w * second (southFiberPoint q).val) -
      (w * second (southFiberPoint q).val).re • (spherePole 7).val +
      (w * second (southFiberPoint q).val).re • (southFiberPoint q).val := by
  change firstAxis (w * second (southFiberPoint q).val) -
    (inner ℝ (1 : ℍ) (w * second (southFiberPoint q).val)) • (spherePole 7).val +
    (inner ℝ (1 : ℍ) (w * second (southFiberPoint q).val)) • (southFiberPoint q).val = _
  simp only [Quaternion.inner_def, one_mul, Quaternion.re_star]

theorem first_chartNormalAmbient (q : Sphere 3) (w : ℍ) :
    first (chartNormalAmbient q w) = w * second (southFiberPoint q).val -
      (w * second (southFiberPoint q).val).re • (1 : ℍ) := by
  rw [chartNormalAmbient_apply, map_add, map_sub, map_smul, map_smul,
    first_firstAxis, first_sourcePole, first_southFiberPoint, smul_zero, add_zero]

theorem second_chartNormalAmbient (q : Sphere 3) (w : ℍ) :
    second (chartNormalAmbient q w) =
      (w * second (southFiberPoint q).val).re • second (southFiberPoint q).val := by
  rw [chartNormalAmbient_apply, map_add, map_sub, map_smul, map_smul,
    second_firstAxis, second_sourcePole, smul_zero, sub_self, zero_add]

theorem chartNormalAmbient_orthogonal_pole (q : Sphere 3) (w : ℍ) :
    inner ℝ (spherePole 7).val (chartNormalAmbient q w) = 0 := by
  rw [sourcePole_inner, first_chartNormalAmbient]
  simp

def chartNormalLift (q : Sphere 3) : ℍ →L[ℝ] V 7 :=
  (StereographicEquator.project 7).comp (chartNormalAmbient q)

theorem lift_chartNormalLift (q : Sphere 3) (w : ℍ) :
    StereographicEquator.lift 7 (chartNormalLift q w) = chartNormalAmbient q w :=
  StereographicEquator.lift_project_of_orthogonal 7 _ (chartNormalAmbient_orthogonal_pole q w)

theorem inner_chartNormalAmbient (q : Sphere 3) (w : ℍ) :
    inner ℝ (southFiberPoint q).val (chartNormalAmbient q w) =
      (w * second (southFiberPoint q).val).re := by
  rw [inner_quaternion_coordinates, first_southFiberPoint, inner_zero_left, zero_add,
    second_chartNormalAmbient, real_inner_smul_right, real_inner_self_eq_norm_sq,
    second_norm_sq_south (southFiberPoint q) (first_southFiberPoint q), mul_one]

theorem chartNormalLift_right_inverse (q : Sphere 3) (w : ℍ) :
    fderiv ℝ southChartEquations ((2 : ℝ) • southChartUnit q) (chartNormalLift q w) =
      targetTailChart w := by
  rw [southChartEquations_derivative, lift_chartNormalLift, first_chartNormalAmbient,
    inner_chartNormalAmbient, sub_add_cancel, mul_assoc,
    south_second_mul_star (southFiberPoint q) (first_southFiberPoint q), mul_one]

theorem chartNormalLift_coordinates_right_inverse (q : Sphere 3) (v : V 4) :
    fderiv ℝ southChartEquations ((2 : ℝ) • southChartUnit q)
      (chartNormalLift q (targetTailChartEquiv.symm v)) = v := by
  rw [chartNormalLift_right_inverse]
  exact targetTailChartEquiv.apply_symm_apply v

theorem southChartEquations_surjective (q : Sphere 3) :
    Function.Surjective (fderiv ℝ southChartEquations ((2 : ℝ) • southChartUnit q)) :=
  fun v ↦ ⟨chartNormalLift q (targetTailChartEquiv.symm v),
    chartNormalLift_coordinates_right_inverse q v⟩

end NoExoticSixSphere.QuaternionicHopf
