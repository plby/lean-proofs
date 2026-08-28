import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspCoordinates

/-!
# The actual scalar cusp coefficient of `dt/F`

The proved source-coordinate derivative and the constructed global
generator determine one analytic nonzero cusp germ.  Dividing this germ
by the actual exponential parameter gives a simple pole.  Multiplying
by the unchanged reciprocal sphere coordinate cancels that pole and
leaves an analytic unit.

These are scalar identities.  Their comparison with the genuine native
canonical-bundle frame is a separate pullback calculation.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspScalar

open Triangle TriangleHolomorphicDifferentials

/-- Both coordinate APIs use the same actual cusp chart and sphere map. -/
theorem coordinateChange_eq_specialCuspCoordinate :
    GlobalCusp.coordinateChange = specialCuspCoordinate := rfl

theorem coordinateUnit_eq_specialCuspUnit :
    GlobalCusp.coordinateUnit = specialCuspUnit := rfl

/-- The scalar `dt/F` in the original exponential cusp parameter. -/
def coefficientGerm (q : ℂ) : ℂ :=
  -cuspDerivativeScale * deriv specialCuspCoordinate q /
    (specialCuspUnit q ^ 2 * GlobalGenerator.cuspUnit q)

theorem coefficientGerm_analyticAt : AnalyticAt ℂ coefficientGerm 0 := by
  exact (analyticAt_const.mul specialCuspCoordinate_deriv_analyticAt_zero).div
    ((specialCuspUnit_analyticAt_zero.pow 2).mul GlobalGenerator.cuspUnit_analyticAt)
    (mul_ne_zero (pow_ne_zero 2 specialCuspUnit_zero_ne_zero)
      GlobalGenerator.cuspUnit_zero_ne_zero)

theorem coefficientGerm_zero_ne_zero : coefficientGerm 0 ≠ 0 :=
  div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr cuspDerivativeScale_ne_zero)
      specialCuspCoordinate_deriv_ne_zero)
    (mul_ne_zero (pow_ne_zero 2 specialCuspUnit_zero_ne_zero)
      GlobalGenerator.cuspUnit_zero_ne_zero)

theorem coefficientGerm_order : analyticOrderAt coefficientGerm 0 = 0 :=
  coefficientGerm_analyticAt.analyticOrderAt_eq_zero.mpr coefficientGerm_zero_ne_zero

theorem coefficientGerm_ne_zero_eventually : ∀ᶠ q in 𝓝 (0 : ℂ), coefficientGerm q ≠ 0 :=
  coefficientGerm_analyticAt.continuousAt.eventually_ne coefficientGerm_zero_ne_zero

/-- The actual derivative divided by the same constructed generator is
this unit germ; neither factor is replaced by a formal model. -/
theorem scalarDeriv_div_generator_eventually : ∀ᶠ z in atImInfty,
    scalarDeriv specialSourceCoordinate z / GlobalGenerator.generator z =
      coefficientGerm (cuspQ z) := by
  filter_upwards [specialSourceCoordinate_scalarDeriv_cusp,
    GlobalGenerator.generator_cusp_eventually] with z hz hF
  rw [hz, hF, coefficientGerm, div_div]
  congr 1
  calc
    (cuspQ z * specialCuspUnit (cuspQ z) ^ 2) *
        ((cuspQ z)⁻¹ * GlobalGenerator.cuspUnit (cuspQ z)) =
      (cuspQ z * (cuspQ z)⁻¹) *
        (specialCuspUnit (cuspQ z) ^ 2 * GlobalGenerator.cuspUnit (cuspQ z)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (cuspQ_ne_zero z), one_mul]

/-- The equality holds pointwise on a sufficiently high actual horodisc. -/
theorem scalarDeriv_div_generator_on_horodisc :
    ∃ Y : ℝ, GlobalGenerator.cuspHeight ≤ Y ∧
      ∀ z ∈ horodisc Y,
        scalarDeriv specialSourceCoordinate z / GlobalGenerator.generator z =
          coefficientGerm (cuspQ z) := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp
    scalarDeriv_div_generator_eventually
  refine ⟨max Y GlobalGenerator.cuspHeight, le_max_right _ _, ?_⟩
  intro z hz
  exact hY z ((le_max_left _ _).trans (show max Y GlobalGenerator.cuspHeight < z.im from hz).le)

/-- The scalar pole before multiplication by the reciprocal base coordinate. -/
def poleGerm (q : ℂ) : ℂ := coefficientGerm q / q

theorem poleGerm_meromorphicAt : MeromorphicAt poleGerm 0 :=
  coefficientGerm_analyticAt.meromorphicAt.div analyticAt_id.meromorphicAt

/-- The numerator is a genuine nonzero analytic unit, hence the pole is simple. -/
theorem poleGerm_order : meromorphicOrderAt poleGerm 0 = (-1 : ℤ) := by
  change meromorphicOrderAt (coefficientGerm / id) 0 = (-1 : ℤ)
  rw [meromorphicOrderAt_div coefficientGerm_analyticAt.meromorphicAt
    analyticAt_id.meromorphicAt, coefficientGerm_analyticAt.meromorphicOrderAt_eq,
    coefficientGerm_order, meromorphicOrderAt_id]
  norm_num

/-- The actual regularizing coefficient in the reciprocal sphere coordinate. -/
def reciprocalRegularization (q : ℂ) : ℂ := coefficientGerm q * specialCuspUnit q

theorem reciprocalRegularization_analyticAt : AnalyticAt ℂ reciprocalRegularization 0 :=
  coefficientGerm_analyticAt.mul specialCuspUnit_analyticAt_zero

theorem reciprocalRegularization_zero_ne_zero : reciprocalRegularization 0 ≠ 0 :=
  mul_ne_zero coefficientGerm_zero_ne_zero specialCuspUnit_zero_ne_zero

theorem reciprocalRegularization_order : analyticOrderAt reciprocalRegularization 0 = 0 :=
  reciprocalRegularization_analyticAt.analyticOrderAt_eq_zero.mpr
    reciprocalRegularization_zero_ne_zero

/-- Multiplication uses the literal coordinate transition of the actual
glued cusp patch.  The cancelled scalar extends as the displayed unit. -/
theorem coordinateChange_mul_poleGerm {q : ℂ} (hq : q ≠ 0) :
    GlobalCusp.coordinateChange q * poleGerm q = reciprocalRegularization q := by
  rw [GlobalCusp.coordinateChange_eq_mul_unit, coordinateUnit_eq_specialCuspUnit]
  change (q * specialCuspUnit q) * (coefficientGerm q / q) =
    coefficientGerm q * specialCuspUnit q
  calc
    _ = (q / q) * (coefficientGerm q * specialCuspUnit q) := by ring
    _ = _ := by rw [div_self hq, one_mul]

theorem coordinateChange_mul_poleGerm_eventually :
    (fun q => GlobalCusp.coordinateChange q * poleGerm q) =ᶠ[𝓝[≠] (0 : ℂ)]
      reciprocalRegularization := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact coordinateChange_mul_poleGerm hq

/-- The scalar regularization is an actual analytic unit, with no
analytic-extension or coordinate-transition hypothesis. -/
theorem coordinateChange_mul_poleGerm_extends :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∀ q : ℂ, q ≠ 0 → GlobalCusp.coordinateChange q * poleGerm q = u q :=
  ⟨reciprocalRegularization, reciprocalRegularization_analyticAt,
    reciprocalRegularization_zero_ne_zero, fun _ hq => coordinateChange_mul_poleGerm hq⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspScalar
