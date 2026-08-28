import Wikipedia.HopfProblem.TriangleRiemannIdealLimits
import Wikipedia.HopfProblem.RiemannSphereMobiusInverse
import Wikipedia.HopfProblem.RiemannSphereMobiusNormalization
import Wikipedia.HopfProblem.SpecialPeriodsModularLocalChartsInverse

/-!
# The reciprocal-normalized analytic cusp germ

The actual ideal germ of the triangle Riemann map has a nonzero derivative.
The actual three distinct vertex values determine the prescribed
cross-ratio normalization. In the target's infinity coordinate, their
composition is analytic at the filled cusp and has a simple zero.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.RiemannSphere.MobiusCircle

/-- Interchanging zero and pole gives the reciprocal rational formula,
including the totalized values at either exceptional point. -/
theorem crossRatio_swap_first_third (a b c z : ℂ) :
    crossRatio c b a z = (crossRatio a b c z)⁻¹ := by
  simp only [crossRatio, inv_div]

/-- The exact derivative of the cross-ratio at its zero. -/
theorem crossRatio_hasStrictDerivAt_first {a b c : ℂ}
    (hba : b ≠ a) (hac : a ≠ c) :
    HasStrictDerivAt (crossRatio a b c)
      ((b - c) / ((a - c) * (b - a))) a := by
  have hn₀ : HasStrictDerivAt (fun z : ℂ => z - a) 1 a :=
    (hasStrictDerivAt_id a).sub_const a
  have hd₀ : HasStrictDerivAt (fun z : ℂ => z - c) 1 a :=
    (hasStrictDerivAt_id a).sub_const c
  have hn : HasStrictDerivAt (fun z : ℂ => (z - a) * (b - c)) (b - c) a := by
    simpa only [one_mul] using hn₀.mul_const (b - c)
  have hd : HasStrictDerivAt (fun z : ℂ => (z - c) * (b - a)) (b - a) a := by
    simpa only [one_mul] using hd₀.mul_const (b - a)
  have hden : (a - c) * (b - a) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hac) (sub_ne_zero.mpr hba)
  convert hn.div hd hden using 1
  all_goals first | rfl | (field_simp [sub_ne_zero.mpr hac, sub_ne_zero.mpr hba]; ring)

end Wikipedia.HopfProblem.RiemannSphere.MobiusCircle

namespace Wikipedia.HopfProblem.RiemannSphere

open MobiusCircle

/-- The literal reciprocal cross-ratio is the infinity-chart coordinate
of the actual sphere normalization, including its value at the pole. -/
theorem threePointBiholomorph_eq_infinityParametrization
    {a b c z : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hza : z ≠ a) :
    threePointBiholomorph a b c hab hac hbc (z : RiemannSphere) =
      infinityParametrization (crossRatio c b a z) := by
  by_cases hzc : z = c
  · subst z
    rw [threePointBiholomorph_third, crossRatio_at_zero, infinityParametrization_zero]
  · have hk : crossRatio c b a z ≠ 0 :=
      div_ne_zero
        (mul_ne_zero (sub_ne_zero.mpr hzc) (sub_ne_zero.mpr hab.symm))
        (mul_ne_zero (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hbc))
    rw [threePointBiholomorph_coe a b c hab hac hbc z hzc,
      infinityParametrization_of_ne hk, crossRatio_swap_first_third, inv_inv]
    rfl

end Wikipedia.HopfProblem.RiemannSphere

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannSphere.MobiusCircle

/-- The actual normalized ideal germ in the target infinity coordinate.
Its source is the half-strip exponential used in the boundary construction. -/
def triangleReciprocalNormalizedCusp (q : ℂ) : ℂ :=
  crossRatio (triangleIdealGerm.function 0) (triangleCornerFourGerm.function 0)
    (triangleCornerThreeGerm.function 0) (triangleIdealGerm.function q)

/-- This is the reciprocal of the required three-point normalization,
not a different choice of target normalization. -/
theorem triangleReciprocalNormalizedCusp_eq_inv (q : ℂ) :
    triangleReciprocalNormalizedCusp q =
      (crossRatio (triangleCornerThreeGerm.function 0) (triangleCornerFourGerm.function 0)
        (triangleIdealGerm.function 0) (triangleIdealGerm.function q))⁻¹ :=
  crossRatio_swap_first_third _ _ _ _

@[simp] theorem triangleReciprocalNormalizedCusp_zero :
    triangleReciprocalNormalizedCusp 0 = 0 :=
  crossRatio_at_zero _ _ _

theorem triangleReciprocalNormalizedCusp_analyticAt_zero :
    AnalyticAt ℂ triangleReciprocalNormalizedCusp 0 := by
  apply (crossRatio_analyticAt triangleCornerFour_boundary_value_ne_ideal
    triangleCornerThree_boundary_value_ne_ideal.symm).comp
  exact triangleIdealGerm.analytic 0 (mem_ball_self triangleIdealGerm.radius_pos)

/-- Its linear coefficient is explicit and uses only the actual
three vertex values and the actual ideal germ derivative. -/
theorem triangleReciprocalNormalizedCusp_hasStrictDerivAt_zero :
    HasStrictDerivAt triangleReciprocalNormalizedCusp
      (((triangleCornerFourGerm.function 0 - triangleCornerThreeGerm.function 0) /
        ((triangleIdealGerm.function 0 - triangleCornerThreeGerm.function 0) *
          (triangleCornerFourGerm.function 0 - triangleIdealGerm.function 0))) *
            deriv triangleIdealGerm.function 0) 0 :=
  (crossRatio_hasStrictDerivAt_first triangleCornerFour_boundary_value_ne_ideal
    triangleCornerThree_boundary_value_ne_ideal.symm).comp 0 triangleIdealGerm.strictDeriv

theorem triangleReciprocalNormalizedCusp_deriv_ne_zero :
    deriv triangleReciprocalNormalizedCusp 0 ≠ 0 := by
  rw [triangleReciprocalNormalizedCusp_hasStrictDerivAt_zero.hasDerivAt.deriv]
  exact mul_ne_zero
    (div_ne_zero (sub_ne_zero.mpr triangleCorner_boundary_values_ne.symm)
      (mul_ne_zero (sub_ne_zero.mpr triangleCornerThree_boundary_value_ne_ideal.symm)
        (sub_ne_zero.mpr triangleCornerFour_boundary_value_ne_ideal)))
    triangleIdealGerm.deriv_ne_zero

/-- The filled cusp is a simple zero of the normalized reciprocal. -/
theorem triangleReciprocalNormalizedCusp_order_zero :
    analyticOrderAt triangleReciprocalNormalizedCusp 0 = 1 :=
  triangleReciprocalNormalizedCusp_analyticAt_zero.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    triangleReciprocalNormalizedCusp_zero triangleReciprocalNormalizedCusp_deriv_ne_zero

/-- This germ is an actual analytic local coordinate, with an analytic
inverse on its declared target. -/
theorem exists_triangleReciprocalNormalizedCusp_coordinate :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      0 ∈ e.source ∧ (∀ q, e q = triangleReciprocalNormalizedCusp q) ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target :=
  SpecialPeriods.exists_analytic_openPartialHomeomorph
    triangleReciprocalNormalizedCusp_analyticAt_zero
    triangleReciprocalNormalizedCusp_deriv_ne_zero

/-- The local formula agrees with the reciprocal of the actual normalized
triangle map whenever the exponential lies in the chosen ideal germ. -/
theorem triangleReciprocalNormalizedCusp_eq_triangleMap_inv
    {z : ℂ} (hz : z ∈ triangleInterior)
    (hq : triangleCuspExp z ∈ ball (0 : ℂ) triangleIdealGerm.radius) :
    triangleReciprocalNormalizedCusp (triangleCuspExp z) =
      (crossRatio (triangleCornerThreeGerm.function 0) (triangleCornerFourGerm.function 0)
        (triangleIdealGerm.function 0) (triangleMap z))⁻¹ := by
  rw [triangleReciprocalNormalizedCusp_eq_inv, triangleMap_eq_ideal_cusp_of_param_mem hz hq]

/-- The same formula holds on the entire triangle end, not just along
chosen logarithmic rays. -/
theorem triangleReciprocalNormalizedCusp_eventually_eq_triangleMap_inv :
    (fun z => triangleReciprocalNormalizedCusp (triangleCuspExp z)) =ᶠ[triangleInfinityFilter]
      (fun z =>
        (crossRatio (triangleCornerThreeGerm.function 0) (triangleCornerFourGerm.function 0)
          (triangleIdealGerm.function 0) (triangleMap z))⁻¹) := by
  filter_upwards [triangleMap_eventually_eq_ideal_cusp] with z hz
  rw [triangleReciprocalNormalizedCusp_eq_inv, hz]

/-- The reciprocal germ is a genuine infinity-chart expression of the
fixed sphere's three-point biholomorphism near the filled ideal point. -/
theorem triangleReciprocalNormalizedCusp_eventually_sphere :
    ∀ᶠ q in 𝓝 (0 : ℂ),
      RiemannSphere.threePointBiholomorph
          (triangleCornerThreeGerm.function 0) (triangleCornerFourGerm.function 0)
          (triangleIdealGerm.function 0) triangleCorner_boundary_values_ne
          triangleCornerThree_boundary_value_ne_ideal triangleCornerFour_boundary_value_ne_ideal
          (triangleIdealGerm.function q : RiemannSphere) =
        RiemannSphere.infinityParametrization (triangleReciprocalNormalizedCusp q) := by
  have hc := (triangleIdealGerm.analytic 0
    (mem_ball_self triangleIdealGerm.radius_pos)).continuousAt
  filter_upwards [hc.eventually_ne triangleCornerThree_boundary_value_ne_ideal.symm] with q hq
  exact RiemannSphere.threePointBiholomorph_eq_infinityParametrization
    triangleCorner_boundary_values_ne triangleCornerThree_boundary_value_ne_ideal
    triangleCornerFour_boundary_value_ne_ideal hq

end Wikipedia.HopfProblem.RiemannMapping
