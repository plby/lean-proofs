import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorElliptic

/-!
# Reciprocal coefficients of the actual global generator

These are the scalar coefficients used when extending `F⁻¹ e` in
Proposition 9.11.  In the source cusp coordinate the reciprocal extends
as `q / cuspUnit q` with exactly a simple zero.  At an elliptic point,
`sᵃ / F` extends as the reciprocal of the proved analytic elliptic unit.
All identities concern the same constructed global function and the
original cusp and normalized elliptic coordinates.
-/

noncomputable section

open Set Filter UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalGenerator

/-- The actual holomorphic extension of the reciprocal generator at the cusp. -/
def inverseCuspCoefficient (t : ℂ) : ℂ := t / cuspUnit t

theorem inverseCuspCoefficient_analyticOnNhd :
    AnalyticOnNhd ℂ inverseCuspCoefficient (Metric.ball 0 cuspRadius) := by
  intro t ht
  exact analyticAt_id.div (cuspUnit_analyticOnNhd t ht) (cuspUnit_ne_zero t ht)

theorem inverseCuspCoefficient_analyticAt : AnalyticAt ℂ inverseCuspCoefficient 0 :=
  inverseCuspCoefficient_analyticOnNhd 0 (Metric.mem_ball_self cuspRadius_pos)

@[simp] theorem inverseCuspCoefficient_zero : inverseCuspCoefficient 0 = 0 := by
  simp only [inverseCuspCoefficient, zero_div]

theorem inverseCuspCoefficient_ne_zero_iff (t : ℂ)
    (ht : t ∈ Metric.ball 0 cuspRadius) :
    inverseCuspCoefficient t ≠ 0 ↔ t ≠ 0 := by
  constructor
  · intro h
    exact (div_ne_zero_iff.mp h).1
  · intro h
    exact div_ne_zero h (cuspUnit_ne_zero t ht)

/-- The reciprocal of the actual cusp pole has exactly a simple analytic zero. -/
theorem inverseCuspCoefficient_order :
    analyticOrderAt inverseCuspCoefficient 0 = 1 := by
  have hu : AnalyticAt ℂ (fun t => (cuspUnit t)⁻¹) 0 :=
    cuspUnit_analyticAt.inv cuspUnit_zero_ne_zero
  have ho : analyticOrderAt (fun t => (cuspUnit t)⁻¹) 0 = 0 :=
    hu.analyticOrderAt_eq_zero.mpr (inv_ne_zero cuspUnit_zero_ne_zero)
  change analyticOrderAt (id * fun t => (cuspUnit t)⁻¹) 0 = 1
  rw [analyticOrderAt_mul analyticAt_id hu, analyticOrderAt_id, ho, add_zero]

theorem inverse_generator_cusp (z : ℍ) (hz : z ∈ Triangle.horodisc cuspHeight) :
    (generator z)⁻¹ = inverseCuspCoefficient (Triangle.cuspQ z) := by
  rw [generator_cusp_on_horodisc z hz, inverseCuspCoefficient, div_eq_mul_inv,
    _root_.mul_inv_rev, inv_inv, mul_comm]

theorem inverse_generator_cusp_eventually : ∀ᶠ z in atImInfty,
    (generator z)⁻¹ = inverseCuspCoefficient (Triangle.cuspQ z) :=
  eventually_mem_cuspHorodisc.mono fun z hz => inverse_generator_cusp z hz

/-- The exact cusp extension and its order are consequences, not assumptions. -/
theorem inverse_generator_has_simple_cusp_zero :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ analyticOrderAt f 0 = 1 ∧
      ∀ᶠ z in atImInfty, (generator z)⁻¹ = f (Triangle.cuspQ z) :=
  ⟨inverseCuspCoefficient, inverseCuspCoefficient_analyticAt,
    inverseCuspCoefficient_order, inverse_generator_cusp_eventually⟩

/-- The actual unit extending `sᵃ / F` at each elliptic point. -/
def inverseEllipticUnit (j : Elliptic.Kind) (s : ℂ) : ℂ := (ellipticUnit j s)⁻¹

theorem inverseEllipticUnit_analyticOnNhd (j : Elliptic.Kind) :
    AnalyticOnNhd ℂ (inverseEllipticUnit j) (Metric.ball 0 (ellipticUnitRadius j)) := by
  intro s hs
  exact (ellipticUnit_analyticOnNhd j s hs).inv (ellipticUnit_ne_zero j hs)

theorem inverseEllipticUnit_ne_zero (j : Elliptic.Kind) {s : ℂ}
    (hs : s ∈ Metric.ball 0 (ellipticUnitRadius j)) : inverseEllipticUnit j s ≠ 0 :=
  inv_ne_zero (ellipticUnit_ne_zero j hs)

theorem inverseEllipticUnit_analyticAt (j : Elliptic.Kind) :
    AnalyticAt ℂ (inverseEllipticUnit j) 0 :=
  inverseEllipticUnit_analyticOnNhd j 0 (Metric.mem_ball_self (ellipticUnitRadius_pos j))

theorem inverseEllipticUnit_zero_ne_zero (j : Elliptic.Kind) :
    inverseEllipticUnit j 0 ≠ 0 :=
  inverseEllipticUnit_ne_zero j (Metric.mem_ball_self (ellipticUnitRadius_pos j))

theorem inverseEllipticUnit_order (j : Elliptic.Kind) :
    analyticOrderAt (inverseEllipticUnit j) 0 = 0 :=
  (inverseEllipticUnit_analyticAt j).analyticOrderAt_eq_zero.mpr
    (inverseEllipticUnit_zero_ne_zero j)

/-- The actual cancelled quotient equals this unit on the punctured
normalized disc, with no value assigned to the quotient at the centre. -/
theorem power_div_discGenerator (j : Elliptic.Kind) (s : Disc)
    (hs : ‖(s : ℂ)‖ < ellipticUnitRadius j) (hs0 : (s : ℂ) ≠ 0) :
    (s : ℂ) ^ ellipticExponent j / discGenerator j s = inverseEllipticUnit j s := by
  rw [discGenerator_factor j s hs, div_mul_eq_div_div,
    div_self (pow_ne_zero _ hs0), one_div]
  rfl

theorem power_div_discGenerator_ambient (j : Elliptic.Kind) {s : ℂ}
    (hs : s ∈ Metric.ball 0 (ellipticUnitRadius j)) (hs0 : s ≠ 0) :
    s ^ ellipticExponent j / SectionsUnit.discExtension (discGenerator j) s =
      inverseEllipticUnit j s := by
  rw [discGenerator_ambient_factor j hs, div_mul_eq_div_div,
    div_self (pow_ne_zero _ hs0), one_div]
  rfl

theorem inverseEllipticUnit_native_holomorphicAt (j : Elliptic.Kind) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun s : Disc => inverseEllipticUnit j s) discZero :=
  (ellipticUnit_native_holomorphicAt j).inv₀ (ellipticUnit_zero_ne_zero j)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalGenerator
