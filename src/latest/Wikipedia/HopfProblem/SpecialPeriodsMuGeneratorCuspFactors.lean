import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorBasic
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCusp

/-!
# The actual q-expansion factors of the μ-generator

The cusp change of parameter is `q ↦ q * u q`. Composing the actual
Eisenstein-series cusp functions and the convergent discriminant product
with this map gives the numerator and denominator units used below.
-/

noncomputable section

open Function Set Filter UpperHalfPlane ModularForm ModularGroup
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

/-- The normalized Eisenstein series of weight six has constant term one. -/
theorem E₆_cuspFunction_zero : cuspFunction 1 E₆ 0 = 1 := by
  have h := EisensteinSeries.E_qExpansion_coeff_zero
    (show 3 ≤ 6 by decide) (show Even 6 by decide)
  simpa [qExpansion_coeff] using h

/-- The actual change between the source and modular exponential parameters. -/
def cuspModularParameter (u : ℂ → ℂ) (t : ℂ) : ℂ := t * u t

@[simp] theorem cuspModularParameter_zero (u : ℂ → ℂ) :
    cuspModularParameter u 0 = 0 := by simp [cuspModularParameter]

theorem cuspModularParameter_analyticAt {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (cuspModularParameter u) 0 :=
  analyticAt_id.mul hu

def cuspEisensteinFour (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  cuspFunction 1 E₄ (cuspModularParameter u t)

def cuspEisensteinSix (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  cuspFunction 1 E₆ (cuspModularParameter u t)

def cuspDiscriminantUnit (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  u t * discriminantUnit (cuspModularParameter u t)

@[simp] theorem cuspEisensteinFour_zero (u : ℂ → ℂ) : cuspEisensteinFour u 0 = 1 := by
  simp [cuspEisensteinFour, E₄_cuspFunction_zero]

@[simp] theorem cuspEisensteinSix_zero (u : ℂ → ℂ) : cuspEisensteinSix u 0 = 1 := by
  simp [cuspEisensteinSix, E₆_cuspFunction_zero]

@[simp] theorem cuspDiscriminantUnit_zero (u : ℂ → ℂ) : cuspDiscriminantUnit u 0 = u 0 := by
  simp [cuspDiscriminantUnit]

theorem cuspEisensteinFour_analyticAt {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (cuspEisensteinFour u) 0 := by
  have h : AnalyticAt ℂ (cuspFunction 1 E₄) (cuspModularParameter u 0) := by
    rw [cuspModularParameter_zero]
    exact ModularFormClass.analyticAt_cuspFunction_zero E₄ zero_lt_one
      one_mem_strictPeriods_SL
  exact h.comp (cuspModularParameter_analyticAt hu)

theorem cuspEisensteinSix_analyticAt {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (cuspEisensteinSix u) 0 := by
  have h : AnalyticAt ℂ (cuspFunction 1 E₆) (cuspModularParameter u 0) := by
    rw [cuspModularParameter_zero]
    exact ModularFormClass.analyticAt_cuspFunction_zero E₆ zero_lt_one
      one_mem_strictPeriods_SL
  exact h.comp (cuspModularParameter_analyticAt hu)

theorem cuspDiscriminantUnit_analyticAt {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (cuspDiscriminantUnit u) 0 := by
  have h : AnalyticAt ℂ discriminantUnit (cuspModularParameter u 0) := by
    rw [cuspModularParameter_zero]
    exact discriminantUnit_analyticAt_zero
  exact hu.mul (h.comp (cuspModularParameter_analyticAt hu))

/-- An analytic square-root branch gives the precise candidate unit in the
μ-generator. Its value at zero is the branch sign divided by `u 0`. -/
def cuspGeneratorUnit (u b : ℂ → ℂ) (t : ℂ) : ℂ :=
  cuspEisensteinFour u t ^ 2 * b t / cuspDiscriminantUnit u t

@[simp] theorem cuspGeneratorUnit_zero (u b : ℂ → ℂ) :
    cuspGeneratorUnit u b 0 = b 0 / u 0 := by
  simp [cuspGeneratorUnit]

theorem cuspGeneratorUnit_analyticAt {u b : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hb : AnalyticAt ℂ b 0) (hu0 : u 0 ≠ 0) :
    AnalyticAt ℂ (cuspGeneratorUnit u b) 0 :=
  ((cuspEisensteinFour_analyticAt hu).pow 2 |>.mul hb).div
    (cuspDiscriminantUnit_analyticAt hu) (by simpa only [cuspDiscriminantUnit_zero] using hu0)

theorem cuspGeneratorUnit_zero_ne_zero {u b : ℂ → ℂ}
    (hu0 : u 0 ≠ 0) (hb0 : b 0 ≠ 0) : cuspGeneratorUnit u b 0 ≠ 0 := by
  rw [cuspGeneratorUnit_zero]
  exact div_ne_zero hb0 hu0

namespace Root

variable {τ : ℍ → ℍ} (r : Root τ)

/-- The actual root equation in the source cusp parameter. -/
theorem square_eq_cuspEisensteinSix (u : ℂ → ℂ) (z : ℍ)
    (hq : Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z)) :
    r z ^ 2 = cuspEisensteinSix u (Triangle.cuspQ z) := by
  rw [r.square z, ← SlashInvariantFormClass.eq_cuspFunction E₆ (τ z)
    one_mem_strictPeriods_SL one_ne_zero, hq]
  rfl

/-- Exact factorization of the actual μ-generator, once its root has been
identified with an analytic branch in the source cusp coordinate. -/
theorem generator_eq_inv_q_mul_unit (u b : ℂ → ℂ) (z : ℍ)
    (hq : Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z))
    (hr : r z = b (Triangle.cuspQ z)) :
    r.generator z = (Triangle.cuspQ z)⁻¹ * cuspGeneratorUnit u b (Triangle.cuspQ z) := by
  have hE : E₄ (τ z) = cuspEisensteinFour u (Triangle.cuspQ z) := by
    rw [← SlashInvariantFormClass.eq_cuspFunction E₄ (τ z)
      one_mem_strictPeriods_SL one_ne_zero, hq]
    rfl
  have hD : discriminant (τ z) = Triangle.cuspQ z *
      cuspDiscriminantUnit u (Triangle.cuspQ z) := by
    have h := discriminant_eq_q_prod (τ z)
    change discriminant (τ z) =
      Periodic.qParam 1 (τ z) * discriminantUnit (Periodic.qParam 1 (τ z)) at h
    rw [h, hq, cuspDiscriminantUnit, cuspModularParameter]
    ring
  rw [generator, hE, hr, hD, cuspGeneratorUnit]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end Root

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
