import ErdosProblems.Erdos157.MonicFactorization
import ErdosProblems.Erdos157.MultisetEuler

/-!
# Nonvanishing in the elementary disk

Absolute convergence, unique factorization, and finite sieving prove that a
nonprincipal character polynomial has no zero in `card K * norm z < 1`.
-/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

noncomputable def monicWeight (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (z : ℂ) (f : MonicPolynomial K) : ℂ := χ (AdjoinRoot.mk g f.1) * z ^ f.1.natDegree

noncomputable def primeWeight (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (z : ℂ) (p : PrimePolynomial K) : ℂ := χ (AdjoinRoot.mk g p.1) * z ^ p.1.natDegree

omit [DecidableEq K] in
theorem monicWeight_primeProduct (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (z : ℂ) (s : Multiset (PrimePolynomial K)) :
    monicWeight g χ z (primeProduct s) = MultisetEuler.weight (primeWeight g χ z) s := by
  induction s using Multiset.induction with
  | empty => simp [monicWeight, primeProduct, MultisetEuler.weight]
  | cons p s ih =>
    have hdeg : (p.1 * (primeProduct s).1).natDegree =
        p.1.natDegree + (primeProduct s).1.natDegree :=
      Polynomial.natDegree_mul p.2.1.ne_zero (primeProduct s).2.ne_zero
    simp only [monicWeight, primeProduct, MultisetEuler.weight,
      Multiset.map_cons, Multiset.prod_cons]
    change χ (AdjoinRoot.mk g (p.1 * (primeProduct s).1)) *
      z ^ (p.1 * (primeProduct s).1).natDegree =
      primeWeight g χ z p * MultisetEuler.weight (primeWeight g χ z) s
    rw [hdeg, map_mul, map_mul, pow_add, ← ih]
    unfold primeWeight monicWeight
    ring

/-- Reindex the complete monic series by prime multisets. -/
noncomputable def primeMultisetEquiv : Multiset (PrimePolynomial K) ≃ AllMonic K :=
  primeFactorizationEquiv.symm.trans allMonicEquiv.symm

theorem monicTerm_primeMultisetEquiv (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (z : ℂ) (s : Multiset (PrimePolynomial K)) :
    monicTerm g χ z (primeMultisetEquiv s) = MultisetEuler.weight (primeWeight g χ z) s :=
  monicWeight_primeProduct g χ z s

theorem summable_norm_primeMultisetWeight [Fintype K] (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    Summable (fun s : Multiset (PrimePolynomial K) =>
      ‖MultisetEuler.weight (primeWeight g χ z) s‖) := by
  have h := (summable_norm_monicTerm g hg χ z hz).comp_injective
    primeMultisetEquiv.injective
  simpa only [Function.comp_def, monicTerm_primeMultisetEquiv] using h

/-- The character polynomial is nonzero throughout its disk of absolute convergence. -/
theorem lPolynomial_eval_ne_zero [Fintype K] (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    (lPolynomial g χ).eval z ≠ 0 := by
  have hsum := primeMultisetEquiv.tsum_eq (monicTerm g χ z)
  simp only [monicTerm_primeMultisetEquiv,
    tsum_monicTerm_eq_lPolynomial g hg χ hχ z hz] at hsum
  rw [← hsum]
  exact MultisetEuler.tsum_weight_ne_zero (primeWeight g χ z)
    (summable_norm_primeMultisetWeight g hg χ z hz)

/-- Consequently every inverse root has modulus at most the field cardinality. -/
theorem norm_inverseRoot_le_card [Fintype K] (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (a : ℂ)
    (ha : (lPolynomial g χ).eval a⁻¹ = 0) : ‖a‖ ≤ Fintype.card K := by
  by_contra hbad
  have hlt : (Fintype.card K : ℝ) < ‖a‖ := lt_of_not_ge hbad
  have hpos : 0 < ‖a‖ := (by positivity : (0 : ℝ) ≤ Fintype.card K).trans_lt hlt
  apply lPolynomial_eval_ne_zero g hg χ hχ a⁻¹ _ ha
  rw [norm_inv, ← div_eq_mul_inv]
  exact (div_lt_one hpos).mpr hlt

end Erdos157.Elementary.PolynomialCharacters
