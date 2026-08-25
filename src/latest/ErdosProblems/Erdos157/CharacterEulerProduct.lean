import ErdosProblems.Erdos157.CharacterNonvanishing
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The character Euler product

The product identity follows from finite sieving and absolute convergence.
It is valid for every character; the finite-polynomial identification is
only used for a nonprincipal character.
-/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

theorem eulerProduct_mul_monicSeries (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    (∏' p : PrimePolynomial K, (1 - primeWeight g χ z p)) *
      (∑' f : AllMonic K, monicTerm g χ z f) = 1 := by
  have h := MultisetEuler.tprod_mul_tsum_eq_one (primeWeight g χ z)
    (summable_norm_primeMultisetWeight g hg χ z hz)
  have hsum := primeMultisetEquiv.tsum_eq (monicTerm g χ z)
  simp only [monicTerm_primeMultisetEquiv] at hsum
  rwa [hsum] at h

theorem eulerProduct_eq_inv_lPolynomial (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    (∏' p : PrimePolynomial K, (1 - primeWeight g χ z p)) =
      ((lPolynomial g χ).eval z)⁻¹ := by
  have h := eulerProduct_mul_monicSeries g hg χ z hz
  rw [tsum_monicTerm_eq_lPolynomial g hg χ hχ z hz] at h
  exact eq_inv_of_mul_eq_one_left h

theorem summable_primeWeight (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    Summable (primeWeight g χ z) :=
  (MultisetEuler.summable_norm_weight_singleton (primeWeight g χ z)
    (summable_norm_primeMultisetWeight g hg χ z hz)).of_norm

theorem primeWeight_norm_lt_one (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) (p : PrimePolynomial K) :
    ‖primeWeight g χ z p‖ < 1 := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  have hcard : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hzlt : ‖z‖ < 1 := (le_mul_of_one_le_left (norm_nonneg z) hcard).trans_lt hz
  calc
    _ ≤ ‖z‖ ^ p.1.natDegree := by
      rw [primeWeight, norm_mul, norm_pow]
      exact mul_le_of_le_one_left (by positivity) (character_norm_le_one χ _)
    _ < 1 := pow_lt_one₀ (norm_nonneg z) hzlt (by
      exact ne_of_gt (primePolynomial_degree_pos p))

theorem eulerFactor_ne_zero (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) (p : PrimePolynomial K) :
    1 - primeWeight g χ z p ≠ 0 := by
  intro h
  have heq : primeWeight g χ z p = 1 := (sub_eq_zero.mp h).symm
  have hnorm := primeWeight_norm_lt_one g hg χ z hz p
  simp [heq] at hnorm

/-- The logarithms converge in the disk of absolute convergence. -/
theorem summable_log_eulerFactor (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    Summable (fun p : PrimePolynomial K => Complex.log (1 - primeWeight g χ z p)) := by
  simpa only [sub_eq_add_neg] using
    Complex.summable_log_one_add_of_summable (summable_primeWeight g hg χ z hz).neg

/-- The logarithmic series exponentiates to the reciprocal character polynomial. -/
theorem exp_sum_log_eq_inv_lPolynomial (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    Complex.exp (∑' p : PrimePolynomial K, Complex.log (1 - primeWeight g χ z p)) =
      ((lPolynomial g χ).eval z)⁻¹ := by
  rw [Complex.cexp_tsum_eq_tprod (eulerFactor_ne_zero g hg χ z hz)
    (summable_log_eulerFactor g hg χ z hz)]
  exact eulerProduct_eq_inv_lPolynomial g hg χ hχ z hz

end Erdos157.Elementary.PolynomialCharacters
