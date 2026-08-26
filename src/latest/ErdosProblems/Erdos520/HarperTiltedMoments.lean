import ErdosProblems.Erdos520.HarperLogTaylor
import ErdosProblems.Erdos520.HarperTiltedLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# One-prime moments under Harper's tilted law

The exact change of measure is already in `HarperTiltedLaw`.  This file
computes the mean and variance of the linearized logarithmic increment and
combines those identities with the cubic Taylor estimate from
`HarperLogTaylor`.
-/

theorem epsilon_const_eq_cubeSign (b : Bool) (p : ℕ) :
    ε (fun _ ↦ b) p = cubeSign b := by
  cases b <;> rfl

/-- The logarithmic Euler increment as a function of one Boolean sign. -/
noncomputable def harperCoordinateLogIncrement
    (p : ℕ) (u : ℝ) (b : Bool) : ℝ :=
  harperLogPrimeIncrement (fun _ ↦ b) p u

/-- The first-order random part of the logarithmic increment. -/
noncomputable def harperLinearPrimeIncrement
    (p : ℕ) (u : ℝ) (b : Bool) : ℝ :=
  cubeSign b * Real.cos (u * Real.log (p : ℝ)) /
    Real.sqrt (p : ℝ)

/-- The deterministic Rademacher second harmonic. -/
noncomputable def harperPrimeSecondHarmonic (p : ℕ) (u : ℝ) : ℝ :=
  Real.cos (2 * (u * Real.log (p : ℝ))) / (2 * (p : ℝ))

/-- Quadratic main term for one logarithmic Euler increment. -/
noncomputable def harperCoordinateLogMain
    (p : ℕ) (u : ℝ) (b : Bool) : ℝ :=
  harperLinearPrimeIncrement p u b - harperPrimeSecondHarmonic p u

theorem abs_harperCoordinateLogIncrement_sub_main_le
    {p : ℕ} (hp : 4 ≤ p) (u : ℝ) (b : Bool) :
    |harperCoordinateLogIncrement p u b -
        harperCoordinateLogMain p u b| ≤
      (2 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  simpa only [harperCoordinateLogIncrement, harperCoordinateLogMain,
    harperLinearPrimeIncrement, harperPrimeSecondHarmonic,
    epsilon_const_eq_cubeSign] using!
      abs_harperLogPrimeIncrement_sub_main_le
        (fun _ ↦ b) hp u

/-- The tilted sign has unit second moment. -/
theorem integral_cubeSign_sq_harperTiltedCoin (p : ℕ) (t : ℝ) :
    (∫ b, cubeSign b ^ 2 ∂harperTiltedCoin p t) = 1 := by
  rw [integral_harperTiltedCoin]
  simpa [cubeSign] using! harperTiltedCoinWeight_false_add_true p t

/-- Exact centered sign variance under the one-coordinate tilted law. -/
theorem integral_cubeSign_sub_bias_sq_harperTiltedCoin
    (p : ℕ) (t : ℝ) :
    (∫ b, (cubeSign b - harperTiltBias p t) ^ 2
        ∂harperTiltedCoin p t) =
      1 - harperTiltBias p t ^ 2 := by
  rw [integral_harperTiltedCoin]
  change harperTiltedCoinWeight p t false *
        ((-1 : ℝ) - harperTiltBias p t) ^ 2 +
      harperTiltedCoinWeight p t true *
        (1 - harperTiltBias p t) ^ 2 = _
  have hsum := harperTiltedCoinWeight_false_add_true p t
  have hdiff := harperTiltedCoinWeight_true_sub_false p t
  nlinarith

/-- Exact tilted mean of the linearized increment. -/
theorem integral_harperLinearPrimeIncrement
    (p : ℕ) (t u : ℝ) :
    (∫ b, harperLinearPrimeIncrement p u b
        ∂harperTiltedCoin p t) =
      harperTiltBias p t *
        (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)) := by
  rw [integral_harperTiltedCoin]
  unfold harperLinearPrimeIncrement
  change harperTiltedCoinWeight p t false *
        ((-1 : ℝ) * Real.cos (u * Real.log (p : ℝ)) /
          Real.sqrt (p : ℝ)) +
      harperTiltedCoinWeight p t true *
        (1 * Real.cos (u * Real.log (p : ℝ)) /
          Real.sqrt (p : ℝ)) = _
  rw [← harperTiltedCoinWeight_true_sub_false]
  ring

/-- Exact centered variance of the linearized increment. -/
theorem integral_harperLinearPrimeIncrement_sub_mean_sq
    (p : ℕ) (t u : ℝ) :
    (∫ b,
        (harperLinearPrimeIncrement p u b -
          harperTiltBias p t *
            (Real.cos (u * Real.log (p : ℝ)) /
              Real.sqrt (p : ℝ))) ^ 2
        ∂harperTiltedCoin p t) =
      (Real.cos (u * Real.log (p : ℝ)) /
          Real.sqrt (p : ℝ)) ^ 2 *
        (1 - harperTiltBias p t ^ 2) := by
  let c : ℝ := Real.cos (u * Real.log (p : ℝ)) /
    Real.sqrt (p : ℝ)
  have hpoint (b : Bool) :
      harperLinearPrimeIncrement p u b - harperTiltBias p t * c =
        c * (cubeSign b - harperTiltBias p t) := by
    dsimp [c, harperLinearPrimeIncrement]
    ring
  simp_rw [show Real.cos (u * Real.log (p : ℝ)) /
      Real.sqrt (p : ℝ) = c by rfl, hpoint, mul_pow]
  rw [integral_const_mul,
    integral_cubeSign_sub_bias_sq_harperTiltedCoin]

/-- Exact tilted mean of the quadratic main term. -/
theorem integral_harperCoordinateLogMain
    (p : ℕ) (t u : ℝ) :
    (∫ b, harperCoordinateLogMain p u b
        ∂harperTiltedCoin p t) =
      harperTiltBias p t *
          (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)) -
        harperPrimeSecondHarmonic p u := by
  unfold harperCoordinateLogMain
  rw [integral_harperTiltedCoin]
  have hlin := integral_harperLinearPrimeIncrement p t u
  rw [integral_harperTiltedCoin] at hlin
  have hsum := harperTiltedCoinWeight_false_add_true p t
  calc
    harperTiltedCoinWeight p t false *
          (harperLinearPrimeIncrement p u false -
            harperPrimeSecondHarmonic p u) +
        harperTiltedCoinWeight p t true *
          (harperLinearPrimeIncrement p u true -
            harperPrimeSecondHarmonic p u) =
        (harperTiltedCoinWeight p t false *
            harperLinearPrimeIncrement p u false +
          harperTiltedCoinWeight p t true *
            harperLinearPrimeIncrement p u true) -
          (harperTiltedCoinWeight p t false +
            harperTiltedCoinWeight p t true) *
            harperPrimeSecondHarmonic p u := by ring
    _ = _ := by rw [hlin, hsum, one_mul]

/-- The tilted mean of the true logarithmic increment differs from its
quadratic approximation by at most the same cubic one-prime remainder. -/
theorem abs_integral_harperCoordinateLogIncrement_sub_mainMean_le
    {p : ℕ} (hp : 4 ≤ p) (t u : ℝ) :
    |(∫ b, harperCoordinateLogIncrement p u b
          ∂harperTiltedCoin p t) -
        (harperTiltBias p t *
            (Real.cos (u * Real.log (p : ℝ)) /
              Real.sqrt (p : ℝ)) -
          harperPrimeSecondHarmonic p u)| ≤
      (2 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  let R : ℝ := (2 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3
  let δ : Bool → ℝ := fun b ↦
    harperCoordinateLogIncrement p u b - harperCoordinateLogMain p u b
  have hδ (b : Bool) : |δ b| ≤ R := by
    exact abs_harperCoordinateLogIncrement_sub_main_le hp u b
  have hrewrite :
      (∫ b, harperCoordinateLogIncrement p u b
          ∂harperTiltedCoin p t) -
        (harperTiltBias p t *
            (Real.cos (u * Real.log (p : ℝ)) /
              Real.sqrt (p : ℝ)) -
          harperPrimeSecondHarmonic p u) =
        ∫ b, δ b ∂harperTiltedCoin p t := by
    rw [← integral_harperCoordinateLogMain p t u,
      ← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  rw [hrewrite, integral_harperTiltedCoin]
  have hwf := harperTiltedCoinWeight_nonneg p t false
  have hwt := harperTiltedCoinWeight_nonneg p t true
  calc
    |harperTiltedCoinWeight p t false * δ false +
        harperTiltedCoinWeight p t true * δ true| ≤
        |harperTiltedCoinWeight p t false * δ false| +
          |harperTiltedCoinWeight p t true * δ true| := abs_add_le _ _
    _ = harperTiltedCoinWeight p t false * |δ false| +
          harperTiltedCoinWeight p t true * |δ true| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hwf, abs_of_nonneg hwt]
    _ ≤ harperTiltedCoinWeight p t false * R +
          harperTiltedCoinWeight p t true * R := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hδ false) hwf)
        (mul_le_mul_of_nonneg_left (hδ true) hwt)
    _ = R := by
      rw [← add_mul, harperTiltedCoinWeight_false_add_true, one_mul]

end Problem520
end Erdos
