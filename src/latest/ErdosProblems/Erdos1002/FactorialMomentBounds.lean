import ErdosProblems.Erdos1002.FactorialMoments
import Mathlib.Data.Nat.Factorial.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Ordinary moments from falling-factorial moments

The point-process argument repeatedly passes from bounds for `(R)_s` to
bounds for `R^s`.  The explicit inequality below makes this implication
quantitative and avoids leaving uniform integrability as an informal use of
the Stirling-number identity.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos1002

noncomputable section

private theorem half_pow_le_descFactorial
    (x s : ℕ) (hxs : 2 * s ≤ x) :
    ((x : ℝ) / 2) ^ s ≤ (x.descFactorial s : ℝ) := by
  rw [Nat.descFactorial_eq_prod_range]
  push_cast
  rw [show ((x : ℝ) / 2) ^ s =
      ∏ _i ∈ Finset.range s, ((x : ℝ) / 2) by
    simp [div_pow]]
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    have his : i < s := Finset.mem_range.mp hi
    have hnat : x ≤ 2 * (x - i) := by omega
    have hreal : (x : ℝ) ≤ 2 * ((x - i : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith

/-- Explicit comparison of an ordinary power with one falling factorial.
The additive term handles the finite range `x < 2s`. -/
theorem natCast_pow_le_two_pow_mul_descFactorial_add
    (x s : ℕ) :
    (x : ℝ) ^ s ≤
      (2 : ℝ) ^ s * (x.descFactorial s : ℝ) +
        ((2 * s : ℕ) : ℝ) ^ s := by
  by_cases hxs : 2 * s ≤ x
  · have hhalf := half_pow_le_descFactorial x s hxs
    have htwo : (0 : ℝ) < 2 ^ s := by positivity
    have hscaled : (x : ℝ) ^ s ≤
        (2 : ℝ) ^ s * (x.descFactorial s : ℝ) := by
      calc
        (x : ℝ) ^ s = (2 : ℝ) ^ s * (((x : ℝ) / 2) ^ s) := by
          rw [div_pow]
          field_simp
        _ ≤ (2 : ℝ) ^ s * (x.descFactorial s : ℝ) := by
          gcongr
    exact hscaled.trans (le_add_of_nonneg_right (by positivity))
  · have hxlt : x < 2 * s := lt_of_not_ge hxs
    have hx : (x : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by
      exact_mod_cast hxlt.le
    calc
      (x : ℝ) ^ s ≤ ((2 * s : ℕ) : ℝ) ^ s := by gcongr
      _ ≤ (2 : ℝ) ^ s * (x.descFactorial s : ℝ) +
          ((2 * s : ℕ) : ℝ) ^ s := by
        exact le_add_of_nonneg_left (mul_nonneg (by positivity) (by positivity))

/-- Integrated moment comparison under a probability measure. -/
theorem integral_natCast_pow_le_of_descFactorial
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℕ) (hX : Measurable X) (s : ℕ)
    (hfac : Integrable (fun ω ↦ (X ω).descFactorial s : Ω → ℝ) μ) :
    ∫ ω, (X ω : ℝ) ^ s ∂μ ≤
      (2 : ℝ) ^ s *
          ∫ ω, ((X ω).descFactorial s : ℝ) ∂μ +
        ((2 * s : ℕ) : ℝ) ^ s := by
  let F : Ω → ℝ := fun ω ↦ (X ω : ℝ) ^ s
  let G : Ω → ℝ := fun ω ↦
    (2 : ℝ) ^ s * ((X ω).descFactorial s : ℝ) +
      ((2 * s : ℕ) : ℝ) ^ s
  have hFmeas : StronglyMeasurable F := by
    exact ((measurable_of_countable
      (fun n : ℕ ↦ (n : ℝ) ^ s)).comp hX).stronglyMeasurable
  have hGint : Integrable G μ := by
    exact (hfac.const_mul ((2 : ℝ) ^ s)).add (integrable_const _)
  have hFint : Integrable F μ := by
    apply hGint.mono' hFmeas.aestronglyMeasurable
    filter_upwards with ω
    dsimp [F, G]
    rw [abs_of_nonneg (by positivity)]
    exact natCast_pow_le_two_pow_mul_descFactorial_add (X ω) s
  calc
    (∫ ω, (X ω : ℝ) ^ s ∂μ) = ∫ ω, F ω ∂μ := by rfl
    _ ≤ ∫ ω, G ω ∂μ := by
      apply integral_mono hFint hGint
      intro ω
      exact natCast_pow_le_two_pow_mul_descFactorial_add (X ω) s
    _ = (2 : ℝ) ^ s *
          ∫ ω, ((X ω).descFactorial s : ℝ) ∂μ +
        ((2 * s : ℕ) : ℝ) ^ s := by
      rw [integral_add, integral_const_mul, integral_const]
      · simp
      · exact hfac.const_mul _
      · exact integrable_const _

/-- A uniform bound on one falling-factorial moment therefore gives the
corresponding uniform ordinary-moment bound. -/
theorem integral_natCast_pow_le_of_descFactorial_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℕ) (hX : Measurable X) (s : ℕ)
    (hfac : Integrable (fun ω ↦ (X ω).descFactorial s : Ω → ℝ) μ)
    {C : ℝ}
    (hC : ∫ ω, ((X ω).descFactorial s : ℝ) ∂μ ≤ C) :
    ∫ ω, (X ω : ℝ) ^ s ∂μ ≤
      (2 : ℝ) ^ s * C + ((2 * s : ℕ) : ℝ) ^ s := by
  calc
    ∫ ω, (X ω : ℝ) ^ s ∂μ ≤
        (2 : ℝ) ^ s *
            ∫ ω, ((X ω).descFactorial s : ℝ) ∂μ +
          ((2 * s : ℕ) : ℝ) ^ s :=
      integral_natCast_pow_le_of_descFactorial μ X hX s hfac
    _ ≤ (2 : ℝ) ^ s * C + ((2 * s : ℕ) : ℝ) ^ s := by
      gcongr

/-- Sequence form used for uniform integrability: a uniform factorial
moment bound at the fixed order `s` yields a uniform ordinary-moment bound
at that order. -/
theorem uniform_integral_natCast_pow_of_uniform_descFactorial
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℕ)
    (hX : ∀ n, Measurable (X n)) (s : ℕ)
    (hfac : ∀ n,
      Integrable (fun ω ↦ (X n ω).descFactorial s : Ω → ℝ) μ)
    {C : ℝ}
    (hC : ∀ n,
      ∫ ω, ((X n ω).descFactorial s : ℝ) ∂μ ≤ C) :
    ∀ n,
      ∫ ω, (X n ω : ℝ) ^ s ∂μ ≤
        (2 : ℝ) ^ s * C + ((2 * s : ℕ) : ℝ) ^ s := by
  intro n
  exact integral_natCast_pow_le_of_descFactorial_integral_le
    μ (X n) (hX n) s (hfac n) (hC n)

end

end Erdos1002
