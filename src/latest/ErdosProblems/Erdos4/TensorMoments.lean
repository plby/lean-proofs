import ErdosProblems.Erdos4.ConductorSupport

/-!
# Exact factorization of twisted moments

The amplitude has arbitrary coefficients on the prime-label functions.
Only the residue average factors; the coefficient support need not be a
rectangle. This identity is used with the genuine product-cutoff vector.
-/

open scoped BigOperators

namespace Erdos4.TensorMoments

variable {P A : Type*} [Fintype P] [DecidableEq P] [Fintype A]
    {U : P → Type*} [∀ p, Fintype (U p)]

noncomputable def amplitude (v : (P → A) → ℂ) (E : ∀ p, A → U p → ℂ)
    (u : ∀ p, U p) : ℂ := ∑ a, v a * ∏ p, E p (a p) (u p)

omit [∀ p, Fintype (U p)] in
theorem amplitude_mul (v w : (P → A) → ℂ) (E : ∀ p, A → U p → ℂ)
    (u : ∀ p, U p) :
    amplitude v E u * amplitude w E u =
      ∑ a, ∑ b, (v a * w b) * ∏ p, E p (a p) (u p) * E p (b p) (u p) := by
  unfold amplitude
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  simp only [Finset.prod_mul_distrib]
  ring

theorem moment_factorization (v w : (P → A) → ℂ) (E : ∀ p, A → U p → ℂ)
    (weight : ∀ p, U p → ℂ) :
    (∑ u : ∀ p, U p, (∏ p, weight p (u p)) * (amplitude v E u * amplitude w E u)) =
      ∑ a, ∑ b, (v a * w b) * ∏ p, ∑ t : U p, weight p t * (E p (a p) t * E p (b p) t) := by
  have hpoint (u : ∀ p, U p) :
      (∏ p, weight p (u p)) * (amplitude v E u * amplitude w E u) =
        ∑ a, ∑ b, (v a * w b) * ∏ p,
          weight p (u p) * (E p (a p) (u p) * E p (b p) (u p)) := by
    rw [amplitude_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    simp only [Finset.prod_mul_distrib]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [← Finset.mul_sum]
  congr 1
  exact (Fintype.prod_sum (fun p (t : U p) => weight p t * (E p (a p) t * E p (b p) t))).symm

/-- Specialization to the real divisor vector and a square amplitude. -/
theorem coefficient_moment_factorization {k : ℕ} (m : ℝ) (R : ℕ) (ell : P → ℕ)
    (state : ∀ p, U p → Option (Fin k)) (weight : ∀ p, U p → ℂ) :
    (∑ u : ∀ p, U p, (∏ p, weight p (u p)) *
      amplitude (fun a => (DivisorCoefficients.coefficient m R ell a : ℂ))
        (fun p a t => (LocalOrthogonality.extendedBasis (ell p : ℝ) a (state p t) : ℂ)) u ^ 2) =
      ConductorSupport.tensorForm (DivisorCoefficients.coefficient m R ell)
        (fun p a b => ∑ t : U p, weight p t *
          ((LocalOrthogonality.extendedBasis (ell p : ℝ) a (state p t) : ℂ) *
            (LocalOrthogonality.extendedBasis (ell p : ℝ) b (state p t) : ℂ))) := by
  simpa only [pow_two, ConductorSupport.tensorForm] using
    moment_factorization (fun a => (DivisorCoefficients.coefficient m R ell a : ℂ))
      (fun a => (DivisorCoefficients.coefficient m R ell a : ℂ))
      (fun p a t => (LocalOrthogonality.extendedBasis (ell p : ℝ) a (state p t) : ℂ)) weight

end Erdos4.TensorMoments
