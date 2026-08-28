import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullbackComparison
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspScalarRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspScalarUniform

/-!
# The genuine normalized cusp coefficient near the entire central fibre

The exact canonical pullback normalization multiplies the proved scalar
analytic unit by `width / (2πi)^3`. The logarithmic identity is uniform over
every lift of each sufficiently small parameter; no choice of logarithm
branch, or assumed equality over a whole earlier radius, is involved.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension

open CuspUniformization CuspGeometry HolomorphicForms.Cusp GlobalCuspPullback

/-- The constant dictated by the two actual canonical-volume derivatives. -/
def volumeNormalization : ℂ :=
  (Triangle.width : ℂ) / (2 * Real.pi * Complex.I : ℂ) ^ 3

theorem volumeNormalization_ne_zero : volumeNormalization ≠ 0 :=
  div_ne_zero (Complex.ofReal_ne_zero.mpr Triangle.width_ne_zero)
    (pow_ne_zero _ exponential_factor_ne_zero)

/-- The actual analytic unit after multiplication by the literal reciprocal base coordinate. -/
def regularizingGerm (q : ℂ) : ℂ :=
  volumeNormalization * GlobalCuspScalar.reciprocalRegularization q

theorem regularizingGerm_analyticAt : AnalyticAt ℂ regularizingGerm 0 :=
  analyticAt_const.mul GlobalCuspScalar.reciprocalRegularization_analyticAt

theorem regularizingGerm_zero_ne_zero : regularizingGerm 0 ≠ 0 :=
  mul_ne_zero volumeNormalization_ne_zero GlobalCuspScalar.reciprocalRegularization_zero_ne_zero

/-- The actual global reciprocal coordinate of every logarithmic cusp point. -/
theorem reciprocal_globalLogMap (x : LogDomain) :
    GlobalCusp.reciprocalCoordinate (Threefold.projectionSphere (globalLogMap x)) =
      GlobalCusp.coordinateChange (exponential x.val.1) := by
  have hp : parameter (localLogMap x) = exponential x.val.1 :=
    projection_totalCuspCover data.correction data.radius x
  exact (GlobalCusp.reciprocal_projection_inclusion (localLogMap x)).trans
    (congrArg GlobalCusp.coordinateChange hp)

/-- The actual canonical-fibre comparison, multiplied by the actual reciprocal
coordinate, is uniformly the analytic unit on all sufficiently small cusp fibres. -/
theorem normalizedFactor_logarithmic_uniform : ∀ᶠ q : ℂ in 𝓝 0,
    ∀ x : LogDomain, exponential x.val.1 = q →
      GlobalCusp.reciprocalCoordinate (Threefold.projectionSphere (globalLogMap x)) *
          regularToCuspFactor x = regularizingGerm q := by
  filter_upwards [GlobalCuspScalar.scalarDeriv_div_generator_log_uniform] with q hq
  intro x hx
  have hr : GlobalRegular.regularCoefficient (toRegularCover x).1 =
      GlobalCuspScalar.coefficientGerm q := by
    rw [GlobalCuspScalar.regularCoefficient_eq_scalarDeriv_div_generator]
    exact hq x hx
  have hq0 : q ≠ 0 := hx ▸ exponential_ne_zero x.val.1
  rw [reciprocal_globalLogMap, regularToCuspFactor_eq, hr, hx]
  change GlobalCusp.coordinateChange q *
    (volumeNormalization * GlobalCuspScalar.poleGerm q) =
      volumeNormalization * GlobalCuspScalar.reciprocalRegularization q
  calc
    _ = volumeNormalization *
        (GlobalCusp.coordinateChange q * GlobalCuspScalar.poleGerm q) := by ring
    _ = _ := by rw [GlobalCuspScalar.coordinateChange_mul_poleGerm hq0]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension
