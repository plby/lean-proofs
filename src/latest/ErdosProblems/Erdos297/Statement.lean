/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Basic

/-!
# Erdős Problem 297: statement of the sharp asymptotic

This file contains only the public analytic definitions and the exact theorem
statement to be proved by the arithmetic and Fourier-analytic development.

For `λ > 0`, put

`p_λ(x) = 1 / (1 + exp (λ / x))`.

The sharp parameter is the unique positive solution of

`integral (x in (0,1)), p_λ(x) / x = 1`.

The natural-log growth constant is

`γ(λ) = λ + integral (x in (0,1)), log (1 + exp (-λ / x))`,

and the exponent when the answer is written in base two is
`c(λ) = γ(λ) / log 2`.  Values assigned to the kernels at `x = 0` do
not change their Lebesgue integrals; we set them to zero so that the Lean
definitions are total and agree literally with the improper-integral
integrands away from the endpoint.
-/

open Filter MeasureTheory
open scoped Topology

namespace Erdos297

noncomputable section

/-- The inhomogeneous Bernoulli selection probability used in the sharp
entropy optimization.  Its endpoint value is immaterial to all integrals. -/
def selectionProbability (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else 1 / (1 + Real.exp (lam / x))

/-- The kernel in the equation defining the sharp positive parameter. -/
def momentKernel (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else selectionProbability lam x / x

/-- The moment whose value must equal one.  This is the Lebesgue realization
of the improper integral from `0` to `1`. -/
def moment (lam : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, momentKernel lam x

/-- The integral kernel in the free-energy formula for the sharp growth
constant. -/
def freeEnergyKernel (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.log (1 + Real.exp (-lam / x))

/-- The natural-log exponential growth constant attached to `λ`. -/
def gamma (lam : ℝ) : ℝ :=
  lam + ∫ x in Set.Icc (0 : ℝ) 1, freeEnergyKernel lam x

/-- The same exponential growth constant expressed as a power of two. -/
def binaryExponent (lam : ℝ) : ℝ :=
  gamma lam / Real.log 2

/-- A positive solution of the integral equation from the resolution of
Erdős Problem 297. -/
def IsCriticalParameter (lam : ℝ) : Prop :=
  0 < lam ∧ moment lam = 1

/-- `λ` is the unique positive solution of the defining integral equation. -/
def IsUniqueCriticalParameter (lam : ℝ) : Prop :=
  IsCriticalParameter lam ∧ ∀ μ, IsCriticalParameter μ → μ = lam

/-- The normalized base-two logarithm of the exact number of representations. -/
def binaryLogGrowth (N : ℕ) : ℝ :=
  Real.logb 2 (count N : ℝ) / N

/-- Canonical proposition expressing the established resolution of Problem
297.  It asserts both uniqueness of the integral-equation parameter and the
sharp natural-log asymptotic for the exact rational count. -/
def NaturalLogResolution : Prop :=
  ∃ lam : ℝ, IsUniqueCriticalParameter lam ∧
    Tendsto logGrowth atTop (𝓝 (gamma lam))

/-- The customary `2^((c + o(1)) N)` formulation of the same resolution,
expressed as convergence of the normalized base-two logarithm. -/
def BinaryLogResolution : Prop :=
  ∃ lam : ℝ, IsUniqueCriticalParameter lam ∧
    Tendsto binaryLogGrowth atTop (𝓝 (binaryExponent lam))

theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos one_lt_two

theorem log_two_ne_zero : Real.log 2 ≠ 0 :=
  ne_of_gt log_two_pos

/-- Pointwise change of logarithm base for the normalized counting function. -/
theorem binaryLogGrowth_eq (N : ℕ) :
    binaryLogGrowth N = logGrowth N / Real.log 2 := by
  simp only [binaryLogGrowth, logGrowth, Real.logb]
  ring

/-- A natural-log asymptotic immediately gives the base-two exponent. -/
theorem tendsto_binaryLogGrowth_of_tendsto_logGrowth {γ : ℝ}
    (h : Tendsto logGrowth atTop (𝓝 γ)) :
    Tendsto binaryLogGrowth atTop (𝓝 (γ / Real.log 2)) := by
  have hfun : binaryLogGrowth = fun N ↦ logGrowth N / Real.log 2 := by
    funext N
    exact binaryLogGrowth_eq N
  rw [hfun]
  exact h.div_const (Real.log 2)

/-- The base-two formulation loses no information because `log 2` is
nonzero. -/
theorem tendsto_logGrowth_of_tendsto_binaryLogGrowth {γ : ℝ}
    (h : Tendsto binaryLogGrowth atTop (𝓝 (γ / Real.log 2))) :
    Tendsto logGrowth atTop (𝓝 γ) := by
  have hm := h.mul_const (Real.log 2)
  have hfun : (fun N : ℕ ↦ binaryLogGrowth N * Real.log 2) = logGrowth := by
    funext N
    rw [binaryLogGrowth_eq]
    field_simp [log_two_ne_zero]
  rw [hfun] at hm
  convert hm using 1
  field_simp [log_two_ne_zero]

theorem tendsto_binaryLogGrowth_iff_tendsto_logGrowth {γ : ℝ} :
    Tendsto binaryLogGrowth atTop (𝓝 (γ / Real.log 2)) ↔
      Tendsto logGrowth atTop (𝓝 γ) := by
  constructor
  · exact tendsto_logGrowth_of_tendsto_binaryLogGrowth
  · exact tendsto_binaryLogGrowth_of_tendsto_logGrowth

/-- The natural-log and `2^((c + o(1))N)` formulations are exactly
equivalent, with the same uniquely characterized parameter. -/
theorem binaryLogResolution_iff_naturalLogResolution :
    BinaryLogResolution ↔ NaturalLogResolution := by
  constructor
  · rintro ⟨lam, hlam, hlim⟩
    exact ⟨lam, hlam, tendsto_logGrowth_of_tendsto_binaryLogGrowth hlim⟩
  · rintro ⟨lam, hlam, hlim⟩
    exact ⟨lam, hlam, tendsto_binaryLogGrowth_of_tendsto_logGrowth hlim⟩

/-- The assertion that the base-two exponent is below one is exactly the
assertion that the natural-log growth constant is below `log 2`. -/
theorem binaryExponent_lt_one_iff (lam : ℝ) :
    binaryExponent lam < 1 ↔ gamma lam < Real.log 2 := by
  rw [binaryExponent, div_lt_one log_two_pos]

end

end Erdos297

#print axioms Erdos297.binaryLogResolution_iff_naturalLogResolution
