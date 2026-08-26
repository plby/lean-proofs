module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The beta = 1/2 Fock series

This file studies the scalar Fock series with coefficients normalized by `sqrt (k!)`.
-/

@[expose] public section

open Filter
open scoped ENNReal NNReal Polynomial Topology

namespace CofiniteDerivatives

noncomputable section

/-- The parameter in the Fock normalization used here. -/
def fockBeta : ℝ := 1 / 2

/-- The denominator in degree `k` for the `beta = 1/2` Fock normalization. -/
def fockDenominator (k : ℕ) : ℝ :=
  Real.sqrt (k.factorial : ℝ)

/-- The normalized coefficient of a Fock series. -/
def fockCoefficient (ξ : ℕ → ℂ) (k : ℕ) : ℂ :=
  ξ k / fockDenominator k

/-- The formal multilinear series associated to the normalized coefficients. -/
def fockPowerSeries (ξ : ℕ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fockCoefficient ξ)

/-- The `beta = 1/2` Fock series. -/
def fockFunction (ξ : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, ξ k * z ^ k / fockDenominator k

theorem fockDenominator_pos (k : ℕ) : 0 < fockDenominator k := by
  simp only [fockDenominator]
  positivity

@[simp]
theorem fockDenominator_ne_zero (k : ℕ) : fockDenominator k ≠ 0 :=
  (fockDenominator_pos k).ne'

theorem fockFunction_eq_series_sum (ξ : ℕ → ℂ) :
    fockFunction ξ = (fockPowerSeries ξ).sum := by
  funext z
  rw [fockFunction, fockPowerSeries, FormalMultilinearSeries.sum]
  apply tsum_congr
  intro k
  rw [FormalMultilinearSeries.ofScalars_apply_eq]
  change ξ k * z ^ k / (fockDenominator k : ℂ) =
    (ξ k / (fockDenominator k : ℂ)) * z ^ k
  ring

private theorem summable_pow_div_sqrt_factorial (r : ℝ≥0) :
    Summable fun k : ℕ => (r : ℝ) ^ k / fockDenominator k := by
  by_cases hr : r = 0
  · subst r
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  · apply summable_of_ratio_test_tendsto_lt_one zero_lt_one
    · exact Eventually.of_forall fun k => by
        exact div_ne_zero (pow_ne_zero k (NNReal.coe_ne_zero.mpr hr))
          (fockDenominator_ne_zero k)
    · convert! (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).const_div_atTop (r : ℝ)
          using 1
      funext k
      simp only [norm_div, Real.norm_eq_abs, abs_pow, abs_of_nonneg r.coe_nonneg,
        abs_of_pos (fockDenominator_pos k), abs_of_pos (fockDenominator_pos (k + 1)),
        Function.comp_apply]
      rw [fockDenominator, fockDenominator, Nat.factorial_succ]
      push_cast
      rw [Real.sqrt_mul (by positivity)]
      field_simp [pow_succ, NNReal.coe_ne_zero.mpr hr]
      simp [pow_succ]

/-- The Fock formal power series has infinite radius of convergence. -/
theorem fockPowerSeries_radius (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    (fockPowerSeries ξ).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg k)) (fun k => ?_)
    (summable_pow_div_sqrt_factorial r)
  rw [fockPowerSeries, FormalMultilinearSeries.ofScalars_norm, fockCoefficient, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (fockDenominator_pos k)]
  simpa [div_eq_mul_inv, mul_comm] using!
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hξ k) (fockDenominator_pos k).le)
      (pow_nonneg r.coe_nonneg k)

/-- The defining formal series represents the Fock function on all of `ℂ`. -/
theorem hasFPowerSeriesOnBall_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    HasFPowerSeriesOnBall (fockFunction ξ) (fockPowerSeries ξ) 0 ⊤ := by
  rw [fockFunction_eq_series_sum]
  have hr : 0 < (fockPowerSeries ξ).radius := by
    rw [fockPowerSeries_radius ξ hξ]
    exact WithTop.top_pos
  simpa [fockPowerSeries_radius ξ hξ] using!
    (fockPowerSeries ξ).hasFPowerSeriesOnBall hr

/-- A bounded-coefficient Fock series is analytic at every complex point. -/
theorem analyticAt_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (z : ℂ) :
    AnalyticAt ℂ (fockFunction ξ) z := by
  exact (hasFPowerSeriesOnBall_fockFunction ξ hξ).analyticAt_of_mem (by simp)

/-- A bounded-coefficient Fock series is entire. -/
theorem analyticOnNhd_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    AnalyticOnNhd ℂ (fockFunction ξ) Set.univ := by
  intro z _
  exact analyticAt_fockFunction ξ hξ z

/-- A bounded-coefficient Fock series is complex differentiable everywhere. -/
theorem differentiable_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    Differentiable ℂ (fockFunction ξ) := by
  intro z
  exact (analyticAt_fockFunction ξ hξ z).differentiableAt

/-- The scalar coefficients of the first derivative of a Fock series. -/
def fockDerivativeCoefficient (ξ : ℕ → ℂ) (m : ℕ) : ℂ :=
  (m + 1) * fockCoefficient ξ (m + 1)

theorem fockDerivativeCoefficient_eq_factorial (ξ : ℕ → ℂ) (m : ℕ) :
    fockDerivativeCoefficient ξ m =
      ξ (m + 1) * (fockDenominator (m + 1) : ℂ) / (m.factorial : ℂ) := by
  have hden : (fockDenominator (m + 1) : ℂ) * fockDenominator (m + 1) =
      ((m + 1).factorial : ℕ) := by
    norm_cast
    exact Real.mul_self_sqrt (by positivity)
  have hfac : (m.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr m.factorial_ne_zero
  rw [fockDerivativeCoefficient, fockCoefficient]
  field_simp [fockDenominator_ne_zero, hfac]
  rw [pow_two, hden, Nat.factorial_succ]
  push_cast
  ring

private theorem fock_derivSeries_eq (ξ : ℕ → ℂ) :
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (fockPowerSeries ξ).derivSeries =
      FormalMultilinearSeries.ofScalars ℂ (fockDerivativeCoefficient ξ) := by
  apply funext
  intro m
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (fockPowerSeries ξ).derivSeries) m,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq
      (FormalMultilinearSeries.ofScalars ℂ (fockDerivativeCoefficient ξ)) m]
  congr 1
  rw [FormalMultilinearSeries.coeff_ofScalars]
  change ((fockPowerSeries ξ).derivSeries.coeff m) 1 = fockDerivativeCoefficient ξ m
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  simp [fockPowerSeries, fockDerivativeCoefficient, nsmul_eq_mul]

/-- The derivative has its coefficientwise differentiated power series on all of `ℂ`. -/
theorem hasFPowerSeriesOnBall_deriv_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) :
    HasFPowerSeriesOnBall (deriv (fockFunction ξ))
      (FormalMultilinearSeries.ofScalars ℂ (fockDerivativeCoefficient ξ)) 0 ⊤ := by
  have h := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall
    (hasFPowerSeriesOnBall_fockFunction ξ hξ).fderiv
  rw [fock_derivSeries_eq ξ] at h
  apply h.congr
  intro z _
  exact fderiv_apply_one_eq_deriv

/-- The first derivative of a Fock series, in coefficientwise differentiated form. -/
theorem deriv_fockFunction_eq_tsum (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (z : ℂ) :
    deriv (fockFunction ξ) z =
      ∑' m : ℕ, (m + 1) * fockCoefficient ξ (m + 1) * z ^ m := by
  have h := hasFPowerSeriesOnBall_deriv_fockFunction ξ hξ
  calc
    deriv (fockFunction ξ) z =
        (FormalMultilinearSeries.ofScalars ℂ (fockDerivativeCoefficient ξ)).sum z := by
      simpa using! h.sum (by simp)
    _ = ∑' m : ℕ, (m + 1) * fockCoefficient ξ (m + 1) * z ^ m := by
      rw [FormalMultilinearSeries.sum]
      apply tsum_congr
      intro m
      rw [FormalMultilinearSeries.ofScalars_apply_eq]
      simp [fockDerivativeCoefficient]

/-- The first derivative in the Fock factorial normalization. -/
theorem deriv_fockFunction_eq_tsum_factorial (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (z : ℂ) :
    deriv (fockFunction ξ) z =
      ∑' m : ℕ, ξ (m + 1) * Real.sqrt ((m + 1).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m := by
  rw [deriv_fockFunction_eq_tsum ξ hξ z]
  apply tsum_congr
  intro m
  rw [← fockDerivativeCoefficient, fockDerivativeCoefficient_eq_factorial]
  rfl

private theorem hasFiniteFPowerSeriesOnBall_polynomial (p : ℂ[X]) :
    HasFiniteFPowerSeriesOnBall (fun z : ℂ => p.eval z)
      (FormalMultilinearSeries.ofScalars ℂ p.coeff) 0 (p.natDegree + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro m hm
    apply FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero
    exact p.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (Nat.lt_succ_self _) hm)
  · exact ENNReal.zero_lt_top
  · intro z _
    simp [Polynomial.eval_eq_sum_range, mul_comm]

private theorem fockCoefficient_ne_zero {ξ : ℕ → ℂ} {k : ℕ} (hξ : ξ k ≠ 0) :
    fockCoefficient ξ k ≠ 0 := by
  apply div_ne_zero hξ
  exact Complex.ofReal_ne_zero.mpr (fockDenominator_ne_zero k)

/-- If every input coefficient is nonzero, the Fock function is not the evaluation of `p`. -/
theorem fockFunction_ne_polynomial_eval (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (hξ0 : ∀ k, ξ k ≠ 0) (p : ℂ[X]) :
    fockFunction ξ ≠ fun z : ℂ => p.eval z := by
  intro h
  have hp : HasFPowerSeriesAt (fockFunction ξ)
      (FormalMultilinearSeries.ofScalars ℂ p.coeff) 0 := by
    rw [h]
    exact (hasFiniteFPowerSeriesOnBall_polynomial p).hasFiniteFPowerSeriesAt.hasFPowerSeriesAt
  have heq : fockPowerSeries ξ = FormalMultilinearSeries.ofScalars ℂ p.coeff :=
    (hasFPowerSeriesOnBall_fockFunction ξ hξ).hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  let n := p.natDegree + 1
  have hcoeff : fockCoefficient ξ n = p.coeff n := by
    simpa [fockPowerSeries] using!
      congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q.coeff n) heq
  have hpzero : p.coeff n = 0 :=
    p.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  exact fockCoefficient_ne_zero (hξ0 n) (hcoeff.trans hpzero)

/-- If every input coefficient is nonzero, no complex polynomial represents the Fock function. -/
theorem not_exists_polynomial_eval_eq_fockFunction (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (hξ0 : ∀ k, ξ k ≠ 0) :
    ¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = fockFunction ξ z := by
  rintro ⟨p, hp⟩
  apply fockFunction_ne_polynomial_eval ξ hξ hξ0 p
  funext z
  exact (hp z).symm

end

end CofiniteDerivatives
