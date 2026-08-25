import ErdosProblems.Erdos157.EulerPrimeTerms

/-! The full Euler logarithmic-derivative positivity inequality. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial
open ElementaryCharacterBound

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

theorem hasSum_re_primeEulerTerm (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ < r) :
    HasSum (fun p : PrimePolynomial K => (primeEulerTerm g χ p z).re)
      (z * ((lPolynomial g χ).derivative.eval z / (lPolynomial g χ).eval z)).re := by
  have h := (summable_primeEulerTerm g hg χ r hr hqr z hz.le).hasSum.map
    Complex.reCLM Complex.reCLM.continuous
  simpa only [Function.comp_def, Complex.reCLM_apply,
    sum_primeEulerTerm g hg χ hχ r hr hqr z hz] using h

theorem hasSum_re_zeta_primeEulerTerm (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (t : ℝ) (ht : 0 ≤ t) (htr : t < r) :
    HasSum (fun p : PrimePolynomial K => (primeEulerTerm 1 1 p (t : ℂ)).re)
      ((Fintype.card K : ℝ) * t / (1 - (Fintype.card K : ℝ) * t)) := by
  have htC : ‖(t : ℂ)‖ < r := by simpa [Complex.norm_real, abs_of_nonneg ht] using htr
  have h := (summable_primeEulerTerm (1 : K[X]) monic_one 1 r hr hqr (t : ℂ) htC.le).hasSum.map
    Complex.reCLM Complex.reCLM.continuous
  rw [sum_zeta_primeEulerTerm r hr hqr (t : ℂ) htC] at h
  have hreal : (((Fintype.card K : ℂ) * (t : ℂ)) /
      (1 - (Fintype.card K : ℂ) * (t : ℂ))).re =
      (Fintype.card K : ℝ) * t / (1 - (Fintype.card K : ℝ) * t) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  simpa only [Function.comp_def, Complex.reCLM_apply, hreal] using h

/-- The elementary positivity inequality for a character and its square. -/
theorem euler_logDerivative_positivity (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    (r : ℝ) (hr : 0 < r) (hqr : (Fintype.card K : ℝ) * r < 1)
    (z : ℂ) (hz : ‖z‖ < r) :
    0 ≤ 3 * ((Fintype.card K : ℝ) * ‖z‖ / (1 - (Fintype.card K : ℝ) * ‖z‖)) +
      4 * (z * ((lPolynomial g χ).derivative.eval z / (lPolynomial g χ).eval z)).re +
      (squaredPhase z * ((lPolynomial g (χ ^ 2)).derivative.eval (squaredPhase z) /
        (lPolynomial g (χ ^ 2)).eval (squaredPhase z))).re := by
  have hw : ‖squaredPhase z‖ < r := by rwa [norm_squaredPhase]
  have h0 := hasSum_re_zeta_primeEulerTerm (K := K) r hr hqr ‖z‖ (norm_nonneg z) hz
  have h1 := hasSum_re_primeEulerTerm g hg χ hχ r hr hqr z hz
  have h2 := hasSum_re_primeEulerTerm g hg (χ ^ 2) hχ2 r hr hqr (squaredPhase z) hw
  have hs := ((h0.mul_left 3).add (h1.mul_left 4)).add h2
  have hcard : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hrone : r < 1 := (le_mul_of_one_le_left hr.le hcard).trans_lt hqr
  exact HasSum.nonneg (fun p => primeEulerTerm_positivity g hg χ p z (hz.trans hrone)) hs

end Erdos157.Elementary.PolynomialCharacters
