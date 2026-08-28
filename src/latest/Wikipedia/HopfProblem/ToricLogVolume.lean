import Wikipedia.HopfProblem.CanonicalBundleAlternating
import Wikipedia.HopfProblem.ToricVolumeCoordinates
import Wikipedia.HopfProblem.ToricCoordinates

/-!
# The displayed logarithmic volume form on the dense torus

The form `dx₁ ∧ dx₂ ∧ dt / (x₁ x₂)` is a genuine continuous top covector
at each point of the dense torus. Its pullback through every actual toric
chart is the signed coordinate volume `det(rays) · dz₀ ∧ dz₁ ∧ dz₂`.
Thus the constant local canonical coefficients are those of the displayed
form, not only an abstract solution of a transition equation.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem

namespace CanonicalBundle

/-- The exact source form `dx₁ ∧ dx₂ ∧ dt / (x₁ x₂)`. The value outside
the nonvanishing locus is only a total-function convention. -/
def logarithmicVolume (w : Model) : TopCovector :=
  coefficientEquiv ((w 0 * w 1)⁻¹)

theorem logarithmicVolume_apply (w : Model) (v : Fin 3 → Model) :
    logarithmicVolume w v = (Matrix.of v).det / (w 0 * w 1) := by
  simp [logarithmicVolume, div_eq_mul_inv, mul_comm]

theorem logarithmicVolume_ne_zero {w : Model} (hw : w ∈ ToricCharts.torus) :
    logarithmicVolume w ≠ 0 := by
  change coefficientEquiv ((w 0 * w 1)⁻¹) ≠ 0
  exact coefficientEquiv.map_eq_zero_iff.not.mpr (inv_ne_zero (mul_ne_zero (hw 0) (hw 1)))

theorem logarithmicVolume_holomorphic :
    ContDiffOn ℂ ω logarithmicVolume ToricCharts.torus := by
  apply coefficientEquiv.contDiff.comp_contDiffOn
  exact ((contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)).contDiffOn.inv
    (fun _ hw => mul_ne_zero (hw 0) (hw 1))

end CanonicalBundle

namespace ToricFan.Triangle

open ToricCharts CanonicalBundle

/-- The Jacobian of the ray-character map, with the third output equal
to the product of the chart coordinates. -/
theorem rays_monomial_det_fderiv (s : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ torus) :
    LinearMap.det (fderiv ℂ (monomial s.rays) z).toLinearMap =
      (s.rays.det : ℂ) * (monomial s.rays z 0 * monomial s.rays z 1) := by
  rw [← jacobianMatrix_det_eq_fderiv_det, jacobianMatrix_monomial s.rays hz,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  have hcast : (s.rays.map (Int.castRingHom ℂ)).det = (s.rays.det : ℂ) :=
    (Int.castRingHom ℂ |>.map_det s.rays).symm
  have hprod : (∏ j, z j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hz j
  have himage : (∏ j, monomial s.rays z j) =
      (monomial s.rays z 0 * monomial s.rays z 1) * (∏ j, z j) := by
    simp [Fin.prod_univ_succ, monomial_rays_height, Triangle.time, mul_assoc]
  rw [hcast, himage, Finset.prod_inv_distrib]
  calc
    (monomial s.rays z 0 * monomial s.rays z 1) * (∏ j, z j) * (s.rays.det : ℂ) *
        (∏ j, z j)⁻¹ =
      (s.rays.det : ℂ) * (monomial s.rays z 0 * monomial s.rays z 1) *
        ((∏ j, z j) * (∏ j, z j)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hprod, mul_one]

theorem rays_monomial_pullback_logarithmicVolume (s : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ torus) :
    (logarithmicVolume (monomial s.rays z)).compContinuousLinearMap
      (fderiv ℂ (monomial s.rays) z) = (s.rays.det : ℂ) • volume := by
  change ContinuousAlternatingMap.compContinuousLinearMap
    (coefficientEquiv ((monomial s.rays z 0 * monomial s.rays z 1)⁻¹))
    (fderiv ℂ (monomial s.rays) z) = coefficientEquiv (s.rays.det : ℂ)
  rw [coefficientEquiv_pullback, rays_monomial_det_fderiv s hz]
  have hn : monomial s.rays z 0 * monomial s.rays z 1 ≠ 0 :=
    mul_ne_zero (monomial_mapsTo_torus _ hz 0) (monomial_mapsTo_torus _ hz 1)
  rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]

end ToricFan.Triangle

namespace ToricSpace

open ToricCharts ToricFan Triangle CanonicalBundle

theorem torusCoordinates_inclusion_fderiv (s : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ torus) :
    fderiv ℂ (torusCoordinates ∘ inclusion s) z = fderiv ℂ (monomial s.rays) z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [torus_open.mem_nhds hz] with w hw
  exact torusCoordinates_inclusion s hw

/-- Pullback of the displayed source form through the actual chart of the
glued toric space equals the signed local canonical volume. -/
theorem torusCoordinates_chart_pullback_logarithmicVolume (s : Triangle)
    {z : CoordinateSpace 3} (hz : z ∈ torus) :
    (logarithmicVolume (torusCoordinates (inclusion s z))).compContinuousLinearMap
      (fderiv ℂ (torusCoordinates ∘ inclusion s) z) = (s.rays.det : ℂ) • volume := by
  rw [torusCoordinates_inclusion s hz, torusCoordinates_inclusion_fderiv s hz]
  exact rays_monomial_pullback_logarithmicVolume s hz

end ToricSpace

end Wikipedia.HopfProblem
