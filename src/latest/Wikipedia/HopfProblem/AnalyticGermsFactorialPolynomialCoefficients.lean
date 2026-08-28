import Wikipedia.HopfProblem.AnalyticGermsFactorialNewton

/-!
# Polynomial and analytic consequences of Newton reconstruction

The coefficient manipulations here are valid in an arbitrary commutative
ring, so they apply both to complex-valued functions and to their actual
analytic germs.
-/

noncomputable section

open Finset Polynomial

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.Newton

section Coefficients

variable {R : Type*} [CommRing R]

/-- A degree-bounded polynomial listed in descending powers. -/
def descendingPolynomial (c : ℕ → R) (d : ℕ) : R[X] :=
  ∑ j ∈ range (d + 1), C (c j) * X ^ (d - j)

theorem descendingPolynomial_natDegree_le (c : ℕ → R) (d : ℕ) :
    (descendingPolynomial c d).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [descendingPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro j hj
  exact if_neg (by omega)

@[simp] theorem descendingPolynomial_coeff_degree (c : ℕ → R) (d : ℕ) :
    (descendingPolynomial c d).coeff d = c 0 := by
  simp only [descendingPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    exact if_neg (by have := mem_range.mp hj; omega)
  · simp

theorem descendingPolynomial_monic (c : ℕ → R) (d : ℕ) (hc : c 0 = 1) :
    (descendingPolynomial c d).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one d (descendingPolynomial_natDegree_le c d)
    ((descendingPolynomial_coeff_degree c d).trans hc)

theorem descendingPolynomial_natDegree [Nontrivial R]
    (c : ℕ → R) (d : ℕ) (hc : c 0 = 1) :
    (descendingPolynomial c d).natDegree = d :=
  natDegree_eq_of_le_of_coeff_ne_zero (descendingPolynomial_natDegree_le c d)
    (by rw [descendingPolynomial_coeff_degree, hc]; exact one_ne_zero)

theorem descendingPolynomial_map {S : Type*} [CommRing S] (φ : R →+* S)
    (c : ℕ → R) (d : ℕ) :
    (descendingPolynomial c d).map φ = descendingPolynomial (fun j => φ (c j)) d := by
  simp only [descendingPolynomial, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

theorem descendingPolynomial_eval (c : ℕ → R) (d : ℕ) (w : R) :
    (descendingPolynomial c d).eval w =
      ∑ j ∈ range (d + 1), c j * w ^ (d - j) := by
  simp only [descendingPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

end Coefficients

theorem polynomial_eq_descendingPolynomial (s : ℕ → ℂ) (d : ℕ) :
    polynomial s d = descendingPolynomial (fun j => (-1) ^ j * elementary s j) d := by
  simp only [polynomial, descendingPolynomial, map_mul, map_pow, map_neg, map_one, mul_assoc]

theorem polynomial_monic (s : ℕ → ℂ) (d : ℕ) : (polynomial s d).Monic := by
  rw [polynomial_eq_descendingPolynomial]
  exact descendingPolynomial_monic _ _ (by simp)

theorem polynomial_natDegree (s : ℕ → ℂ) (d : ℕ) : (polynomial s d).natDegree = d := by
  rw [polynomial_eq_descendingPolynomial]
  exact descendingPolynomial_natDegree _ _ (by simp)

theorem polynomial_eval (s : ℕ → ℂ) (d : ℕ) (w : ℂ) :
    (polynomial s d).eval w =
      ∑ j ∈ range (d + 1), ((-1) ^ j * elementary s j) * w ^ (d - j) := by
  rw [polynomial_eq_descendingPolynomial, descendingPolynomial_eval]

/-- Polynomial evaluation with analytic moment coefficients is jointly
analytic in the original parameter and the polynomial variable. -/
theorem polynomial_eval_analyticAt (s : ℕ → ℂ → ℂ) (d : ℕ)
    {p : ℂ × ℂ} (hs : ∀ k, AnalyticAt ℂ (s k) p.1) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => (polynomial (fun k => s k z.1) d).eval z.2) p := by
  simp only [polynomial_eval]
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact (analyticAt_const.mul ((elementary_analyticAt s hs j).comp analyticAt_fst)).mul
    (analyticAt_snd.pow (d - j))

end Wikipedia.HopfProblem.AnalyticGermsFactorial.Newton
