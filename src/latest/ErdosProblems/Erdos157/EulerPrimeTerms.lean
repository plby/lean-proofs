import ErdosProblems.Erdos157.PolynomialZeta
import ErdosProblems.Erdos157.EulerPositivity
import ErdosProblems.Erdos157.CharacterRootBound

/-! Prime-factor terms in the logarithmic derivative. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

noncomputable def primeEulerTerm (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (p : PrimePolynomial K) (z : ℂ) : ℂ :=
  (p.1.natDegree : ℂ) * (primeWeight g χ z p / (1 - primeWeight g χ z p))

theorem primeEulerTerm_eq_logDerivative (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (p : PrimePolynomial K) (z : ℂ) :
    primeEulerTerm g χ p z = -z * eulerLogDerivative g χ p z := by
  have hd : p.1.natDegree = (p.1.natDegree - 1) + 1 := by
    have := primePolynomial_degree_pos p
    omega
  have hpow : z ^ p.1.natDegree = z ^ (p.1.natDegree - 1) * z := by
    nth_rw 1 [hd]
    rw [pow_succ]
  unfold primeEulerTerm eulerLogDerivative
  unfold primeWeight
  rw [hpow]
  ring

theorem summable_primeEulerTerm (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ ≤ r) :
    Summable (fun p : PrimePolynomial K => primeEulerTerm g χ p z) := by
  simpa only [primeEulerTerm_eq_logDerivative] using
    (summable_eulerLogDerivative g hg χ r hr hqr z hz).mul_left (-z)

theorem sum_primeEulerTerm (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ < r) :
    (∑' p : PrimePolynomial K, primeEulerTerm g χ p z) =
      z * ((lPolynomial g χ).derivative.eval z / (lPolynomial g χ).eval z) := by
  simp_rw [primeEulerTerm_eq_logDerivative]
  rw [tsum_mul_left, lPolynomial_logDerivative_eq g hg χ hχ r hr hqr z hz]
  ring

theorem sum_zeta_primeEulerTerm (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ < r) :
    (∑' p : PrimePolynomial K, primeEulerTerm 1 1 p z) =
      (Fintype.card K : ℂ) * z / (1 - (Fintype.card K : ℂ) * z) := by
  simp_rw [primeEulerTerm_eq_logDerivative]
  rw [tsum_mul_left, zeta_logDerivative r hr hqr z hz]
  ring

theorem primeWeight_zeta (p : PrimePolynomial K) (z : ℂ) :
    primeWeight 1 1 z p = z ^ p.1.natDegree := by
  simp only [primeWeight, trivial_modulus_character, one_mul]

/-- Normalize the phase of a nonzero argument and apply a character to it. -/
noncomputable def characterPhase (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (p : PrimePolynomial K) (z : ℂ) : ℂ :=
  χ (AdjoinRoot.mk g p.1) * (z / (‖z‖ : ℂ)) ^ p.1.natDegree

theorem characterPhase_norm_le (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (p : PrimePolynomial K) (z : ℂ)
    (hz : z ≠ 0) : ‖characterPhase g χ p z‖ ≤ 1 := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  have hphase : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z),
      div_self (norm_ne_zero_iff.mpr hz)]
  rw [characterPhase, norm_mul, norm_pow, hphase, one_pow, mul_one]
  exact character_norm_le_one χ _

theorem radius_mul_characterPhase (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (p : PrimePolynomial K) (z : ℂ) (hz : z ≠ 0) :
    ((‖z‖ ^ p.1.natDegree : ℝ) : ℂ) * characterPhase g χ p z = primeWeight g χ z p := by
  have hnorm : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hz
  unfold characterPhase primeWeight
  rw [Complex.ofReal_pow, div_pow]
  field_simp

theorem radius_mul_characterPhase_sq (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (p : PrimePolynomial K) (z : ℂ) (hz : z ≠ 0) :
    ((‖z‖ ^ p.1.natDegree : ℝ) : ℂ) * characterPhase g χ p z ^ 2 =
      primeWeight g (χ ^ 2) (ElementaryCharacterBound.squaredPhase z) p := by
  have hnorm : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hz
  have hcancel : (‖z‖ : ℂ) ^ p.1.natDegree * ((‖z‖ : ℂ)⁻¹) ^ p.1.natDegree = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hnorm, one_pow]
  unfold characterPhase primeWeight ElementaryCharacterBound.squaredPhase
  rw [χ.pow_apply' (by decide : 2 ≠ 0)]
  rw [Complex.ofReal_pow, mul_pow, div_pow, div_pow]
  field_simp [hnorm]
  linear_combination -(χ (AdjoinRoot.mk g p.1) ^ 2 * z ^ (p.1.natDegree * 2)) * hcancel

/-- Each prime contributes a nonnegative amount to the `3,4,1` combination. -/
theorem primeEulerTerm_positivity (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (p : PrimePolynomial K) (z : ℂ) (hz : ‖z‖ < 1) :
    0 ≤ 3 * (primeEulerTerm 1 1 p (‖z‖ : ℂ)).re +
      4 * (primeEulerTerm g χ p z).re +
      (primeEulerTerm g (χ ^ 2) p (ElementaryCharacterBound.squaredPhase z)).re := by
  by_cases hz0 : z = 0
  · subst z
    have hd : p.1.natDegree ≠ 0 := ne_of_gt (primePolynomial_degree_pos p)
    simp [primeEulerTerm, primeWeight, hd, ElementaryCharacterBound.squaredPhase]
  have ht : ‖z‖ ^ p.1.natDegree < 1 :=
    pow_lt_one₀ (norm_nonneg z) hz (ne_of_gt (primePolynomial_degree_pos p))
  have h := ElementaryCharacterBound.geometric_character_positivity
    (‖z‖ ^ p.1.natDegree) (by positivity) ht (characterPhase g χ p z)
    (characterPhase_norm_le g hg χ p z hz0)
  rw [radius_mul_characterPhase g χ p z hz0,
    radius_mul_characterPhase_sq g χ p z hz0] at h
  have hmul := mul_nonneg (show (0 : ℝ) ≤ p.1.natDegree by positivity) h
  have hre : (((‖z‖ ^ p.1.natDegree : ℝ) : ℂ) /
      (1 - ((‖z‖ ^ p.1.natDegree : ℝ) : ℂ))).re =
      ‖z‖ ^ p.1.natDegree / (1 - ‖z‖ ^ p.1.natDegree) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [primeEulerTerm, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero]
  rw [primeWeight_zeta, ← Complex.ofReal_pow, hre]
  nlinarith

end Erdos157.Elementary.PolynomialCharacters
