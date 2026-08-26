import ErdosProblems.Erdos421.ZetaPoleLogDerivative
import ErdosProblems.Erdos421.VonMangoldtPerron
import Mathlib.NumberTheory.LSeries.Linearity

/-! # The exact Perron comparison of von Mangoldt and integer sums -/

namespace Erdos421

open Complex MeasureTheory

noncomputable def primeErrorCoefficient (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) - 1

theorem LSeriesSummable_primeErrorCoefficient {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable primeErrorCoefficient s :=
  (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).sub (LSeriesSummable_one_iff.mpr hs)

theorem LSeries_primeErrorCoefficient {s : ℂ} (hs : 1 < s.re) :
    LSeries primeErrorCoefficient s = -zetaPrimeError s := by
  have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
  change LSeries ((fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) - 1) s = _
  rw [LSeries_sub (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (LSeriesSummable_one_iff.mpr hs), LSeries_one_eq_riemannZeta hs,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    zetaPrimeError_eq hs1 (riemannZeta_ne_zero_of_one_le_re hs.le), logDeriv_apply]
  ring

noncomputable def smoothedPrimeErrorSum (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), LSeries.term primeErrorCoefficient 0 n *
    ((1 - (n : ℝ) / x : ℝ) : ℂ)

noncomputable def smoothedIntegerSum (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), LSeries.term (fun _ ↦ 1) 0 n *
    ((1 - (n : ℝ) / x : ℝ) : ℂ)

theorem smoothedPrimeErrorSum_eq_sub (x : ℝ) :
    smoothedPrimeErrorSum x = smoothedVonMangoldtSum x 0 - smoothedIntegerSum x := by
  have he : primeErrorCoefficient = (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) - 1 := rfl
  simp only [smoothedPrimeErrorSum, smoothedVonMangoldtSum, smoothedIntegerSum, he,
    LSeries.term_sub_apply, Complex.ofReal_zero, zero_mul, sub_mul, Finset.sum_sub_distrib]
  rfl

theorem smoothedPrimeErrorSum_eq_integral {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    smoothedPrimeErrorSum x = -(1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ,
      (x : ℂ) ^ ((σ : ℂ) + y * I) * perronKernel ((σ : ℂ) + y * I) *
        zetaPrimeError ((σ : ℂ) + y * I)) := by
  have ha := LSeriesSummable_primeErrorCoefficient (s := (σ : ℂ)) (by simpa using hσ)
  have h := smoothedPerron_formula hx (by linarith : 1 / 2 ≤ σ) ha 0
  rw [triangularMellin_tsum_eq_finite _ hx 0] at h
  simp only [Complex.ofReal_zero, zero_mul, zero_add] at h
  have hpoint : ∀ y : ℝ, LSeries primeErrorCoefficient ((σ : ℂ) + y * I) =
      -zetaPrimeError ((σ : ℂ) + y * I) := fun y ↦
    LSeries_primeErrorCoefficient (by simpa using hσ)
  simp_rw [hpoint, mul_neg] at h
  rw [integral_neg] at h
  change _ = smoothedPrimeErrorSum x at h
  simpa only [neg_smul, smul_neg] using h.symm

end Erdos421
