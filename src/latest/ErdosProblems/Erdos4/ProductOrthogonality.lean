import ErdosProblems.Erdos4.LocalOrthogonality
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact orthogonality over finitely many sieve primes

The coefficients can be restricted by any cutoff: the Parseval identities
hold for every coefficient vector, so no independence of divisor coordinates
or rectangular support is assumed.
-/

open scoped BigOperators

namespace Erdos4.ProductOrthogonality

open LocalOrthogonality

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def stateWeight (ell : P → ℝ) (s : P → Option (Fin k)) : ℝ :=
  ∏ p, LocalOrthogonality.stateWeight (ell p) k (s p)

noncomputable def basis (ell : P → ℝ) (a s : P → Option (Fin k)) : ℝ :=
  ∏ p, extendedBasis (ell p) (a p) (s p)

noncomputable def mean (ell : P → ℝ) (f : (P → Option (Fin k)) → ℝ) : ℝ :=
  ∑ s, stateWeight ell s * f s

omit [DecidableEq P] in
theorem stateWeight_nonneg (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (s : P → Option (Fin k)) : 0 ≤ stateWeight ell s :=
  Finset.prod_nonneg (fun p _hp => LocalOrthogonality.stateWeight_nonneg (hell p) (s p))

theorem sum_stateWeight (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p) :
    (∑ s : P → Option (Fin k), stateWeight ell s) = 1 := by
  classical
  unfold stateWeight
  rw [← Fintype.prod_sum]
  have hlocal : ∀ p, (∑ s : Option (Fin k), LocalOrthogonality.stateWeight (ell p) k s) = 1 := by
    intro p
    simpa only [mean_eq_sum, mul_one] using LocalOrthogonality.mean_one (hell p)
  simp_rw [hlocal]
  simp

theorem mean_one (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p) :
    mean (k := k) ell (fun _ => 1) = 1 := by
  simpa only [mean, mul_one] using sum_stateWeight ell hell

theorem mean_basis_mul (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (a b : P → Option (Fin k)) :
    mean ell (fun s => basis ell a s * basis ell b s) = if a = b then 1 else 0 := by
  classical
  have hlocal : ∀ p, (∑ s : Option (Fin k),
      LocalOrthogonality.stateWeight (ell p) k s *
        (extendedBasis (ell p) (a p) s * extendedBasis (ell p) (b p) s)) =
        if a p = b p then 1 else 0 := by
    intro p
    rw [← mean_eq_sum]
    exact mean_extendedBasis_mul (hell p) (a p) (b p)
  have hfactor : ∀ s : P → Option (Fin k),
      stateWeight ell s * (basis ell a s * basis ell b s) =
      ∏ p, LocalOrthogonality.stateWeight (ell p) k (s p) *
        (extendedBasis (ell p) (a p) (s p) * extendedBasis (ell p) (b p) (s p)) := by
    intro s
    simp only [stateWeight, basis, Finset.prod_mul_distrib]
  unfold mean
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun p (s : Option (Fin k)) =>
    LocalOrthogonality.stateWeight (ell p) k s *
      (extendedBasis (ell p) (a p) s * extendedBasis (ell p) (b p) s))]
  simp_rw [hlocal]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    obtain ⟨p, hp⟩ : ∃ p, a p ≠ b p := by
      by_contra hn
      push Not at hn
      exact hab (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

theorem mean_sum {α : Type*} (ell : P → ℝ) (S : Finset α)
    (f : α → (P → Option (Fin k)) → ℝ) :
    mean ell (fun s => ∑ a ∈ S, f a s) = ∑ a ∈ S, mean ell (f a) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mean_const_mul (ell : P → ℝ) (c : ℝ)
    (f : (P → Option (Fin k)) → ℝ) :
    mean ell (fun s => c * f s) = c * mean ell f := by
  unfold mean
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun s _hs => by ring)

noncomputable def expansion (ell : P → ℝ)
    (v : (P → Option (Fin k)) → ℝ) (s : P → Option (Fin k)) : ℝ :=
  ∑ a, v a * basis ell a s

/-- Exact inner product of two arbitrary divisor coefficient vectors. -/
theorem mean_expansion_mul (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (v w : (P → Option (Fin k)) → ℝ) :
    mean ell (fun s => expansion ell v s * expansion ell w s) = ∑ a, v a * w a := by
  classical
  have heq : ∀ s : P → Option (Fin k), expansion ell v s * expansion ell w s =
      ∑ a, ∑ b, (v a * w b) * (basis ell a s * basis ell b s) := by
    intro s
    unfold expansion
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _hb => by ring)
  simp_rw [heq]
  rw [mean_sum]
  simp_rw [mean_sum, mean_const_mul, mean_basis_mul ell hell]
  simp

theorem mean_expansion_sq (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (v : (P → Option (Fin k)) → ℝ) :
    mean ell (fun s => expansion ell v s ^ 2) = ∑ a, v a ^ 2 := by
  simpa only [pow_two] using mean_expansion_mul ell hell v v

end Erdos4.ProductOrthogonality
