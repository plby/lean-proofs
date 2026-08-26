import ErdosProblems.Erdos4.LocalFourier

/-!
# Exact conductor support from the product cutoff

If every prime in a conductor is occupied by at least one of two divisor
labels, the conductor product is at most the product of their two total
divisors. Therefore a quadratic tensor form whose twisted local matrices
vanish at the empty-empty entry is supported on conductors at most `R^2`.
No independence of the divisor cutoff is used.
-/

open scoped BigOperators

namespace Erdos4.ConductorSupport

open DivisorCoefficients

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem conductorProduct_le (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (J : Finset P) (a b : P → Option (Fin k))
    (hcover : ∀ p ∈ J, a p ≠ none ∨ b p ≠ none) :
    (∏ p ∈ J, ell p) ≤ totalDivisor ell a * totalDivisor ell b := by
  have hfactor (c : P → Option (Fin k)) (p : P) :
      1 ≤ if c p = none then 1 else ell p := by
    split_ifs
    · exact le_rfl
    · exact hell p
  have hpoint (p : P) : (if p ∈ J then ell p else 1) ≤
      (if a p = none then 1 else ell p) * (if b p = none then 1 else ell p) := by
    by_cases hp : p ∈ J
    · rw [if_pos hp]
      by_cases ha : a p = none
      · have hb : b p ≠ none := (hcover p hp).resolve_left (not_not.mpr ha)
        simp [ha, hb]
      · rw [if_neg ha]
        exact le_mul_of_one_le_right (Nat.zero_le _) (hfactor b p)
    · rw [if_neg hp]
      simpa only [one_mul] using Nat.mul_le_mul (hfactor a p) (hfactor b p)
  have heq : (∏ p : P, if p ∈ J then ell p else 1) = ∏ p ∈ J, ell p := by
    rw [← Finset.prod_filter]
    simp
  rw [totalDivisor, totalDivisor, ← Finset.prod_mul_distrib, ← heq]
  exact Finset.prod_le_prod (fun p _hp => Nat.zero_le _) (fun p _hp => hpoint p)

omit [DecidableEq P] in
theorem coefficient_ne_zero_cutoff (m : ℝ) (R : ℕ) (ell : P → ℕ)
    (a : P → Option (Fin k)) (ha : coefficient m R ell a ≠ 0) : totalDivisor ell a ≤ R := by
  by_contra hh
  simp only [coefficient, if_neg hh, ne_eq, not_true_eq_false] at ha

noncomputable def tensorForm (v : (P → Option (Fin k)) → ℝ)
    (M : P → Option (Fin k) → Option (Fin k) → ℂ) : ℂ :=
  ∑ a, ∑ b, (v a : ℂ) * (v b : ℂ) * ∏ p, M p (a p) (b p)

/-- The conductor product cannot exceed the square of the actual cutoff. -/
theorem tensorForm_eq_zero_of_large_conductor (m : ℝ) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (hlarge : R ^ 2 < ∏ p ∈ J, ell p)
    (M : P → Option (Fin k) → Option (Fin k) → ℂ)
    (hzero : ∀ p ∈ J, M p none none = 0) :
    tensorForm (coefficient m R ell) M = 0 := by
  unfold tensorForm
  apply Finset.sum_eq_zero
  intro a _ha
  apply Finset.sum_eq_zero
  intro b _hb
  by_cases ha : coefficient m R ell a = 0
  · simp [ha]
  by_cases hb : coefficient m R ell b = 0
  · simp [hb]
  have hex : ∃ p ∈ J, a p = none ∧ b p = none := by
    by_contra hn
    push Not at hn
    have hcover : ∀ p ∈ J, a p ≠ none ∨ b p ≠ none := by
      intro p hp
      by_cases hpa : a p = none
      · exact Or.inr (hn p hp hpa)
      · exact Or.inl hpa
    have hh := (conductorProduct_le ell hell J a b hcover).trans
      (Nat.mul_le_mul (coefficient_ne_zero_cutoff m R ell a ha)
        (coefficient_ne_zero_cutoff m R ell b hb))
    nlinarith
  obtain ⟨p, hp, hpa, hpb⟩ := hex
  have hprod : (∏ q, M q (a q) (b q)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ p) (by simpa only [hpa, hpb] using hzero p hp)
  rw [hprod, mul_zero]

theorem twistedMatrix_none_none (ell : ℝ) (j : Fin k) (phase : Fin k → ℂ) :
    LocalFourier.twistedMatrix ell j phase none none = 0 := by
  simp [LocalFourier.twistedMatrix, LocalFourier.evaluationDifference,
    LocalOrthogonality.extendedBasis]

end Erdos4.ConductorSupport
