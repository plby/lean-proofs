import Wikipedia.NoExoticSixSphere.QuaternionicHopfChartTarget

/-!
# The original stereographic Hopf equations and their exact differential

The defining function is the original target chart of the original Hopf
map in the original source chart. The ambient formula is an equality of
those actual functions; its differential is then computed along the fiber.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def southChartEquations : V 7 → V 4 :=
  StereographicFiber.coordinates (k := 3) sphereMap south (spherePole 7)

theorem southChartEquations_formula : southChartEquations =
    StereographicEquator.ambientChart 4 ∘ polynomial ∘ StereographicEquator.finiteAmbient 7 := by
  funext y
  change SpherePoleCompactification.chart (-south)
    (sphereMap ((SpherePoleCompactification.chart (spherePole 7)).symm y)) = _
  rw [neg_south]
  change sphereProjection 4 (sphereMap ((sphereProjection 7).symm y)) = _
  rw [← StereographicEquator.ambientChart_sphere]
  change _ = StereographicEquator.ambientChart 4 (polynomial
    (euclideanOnePointSphere 7 (y : OnePoint (V 7))).val)
  rw [euclideanOnePointSphere_coe]
  rfl

theorem polynomial_southChartUnit (q : Sphere 3) :
    polynomial (StereographicEquator.finiteAmbient 7 ((2 : ℝ) • southChartUnit q)) =
      -(spherePole 4).val := by
  rw [finiteAmbient_southChartUnit]
  exact congrArg Subtype.val (sphereMap_southFiberPoint q)

theorem southChartEquations_derivative (q : Sphere 3) (v : V 7) :
    fderiv ℝ southChartEquations ((2 : ℝ) • southChartUnit q) v =
      targetTailChart ((first (StereographicEquator.lift 7 v) +
        (inner ℝ (southFiberPoint q).val (StereographicEquator.lift 7 v)) • (1 : ℍ)) *
          star (second (southFiberPoint q).val)) := by
  let z := (2 : ℝ) • southChartUnit q
  have hA : DifferentiableAt ℝ (StereographicEquator.ambientChart 4)
      (polynomial (StereographicEquator.finiteAmbient 7 z)) := by
    rw [polynomial_southChartUnit]
    apply (StereographicEquator.contDiffAt_ambientChart 4 _ ?_).differentiableAt (by simp)
    rw [StereographicEquator.inner_pole_antipode]
    norm_num
  have hP := contDiff_polynomial.differentiable (by simp)
  have hS := (StereographicEquator.contDiff_finiteAmbient 7).differentiable (by simp)
  rw [southChartEquations_formula, fderiv_comp z hA ((hP _).comp z (hS z)),
    fderiv_comp z (hP _) (hS z)]
  change fderiv ℝ (StereographicEquator.ambientChart 4)
    (polynomial (StereographicEquator.finiteAmbient 7 z))
      (fderiv ℝ polynomial (StereographicEquator.finiteAmbient 7 z)
        (fderiv ℝ (StereographicEquator.finiteAmbient 7) z v)) = _
  rw [polynomial_southChartUnit, StereographicEquator.ambientChart_derivative_antipode,
    finiteAmbient_southChartUnit, StereographicEquator.finiteAmbient_derivative_double 7
      (southChartUnit q) (norm_southChartUnit q), lift_southChartUnit,
    polynomial_fderiv_south _ (first_southFiberPoint q), project_target_join]
  have hc : inner ℝ (southChartUnit q) v =
      inner ℝ (southFiberPoint q).val (StereographicEquator.lift 7 v) := by
    rw [← lift_southChartUnit, StereographicEquator.inner_lift]
  apply congrArg targetTailChart
  rw [hc, map_smul, map_add, map_sub, map_smul, map_smul, first_southFiberPoint,
    first_sourcePole, smul_zero, sub_zero, smul_mul_assoc, smul_smul]
  norm_num only
  exact one_smul ℝ _

end NoExoticSixSphere.QuaternionicHopf
