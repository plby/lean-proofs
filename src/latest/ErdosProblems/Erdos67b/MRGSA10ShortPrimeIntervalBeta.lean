import ErdosProblems.Erdos67b.MRIntervalBetaSieve

/-!
# A beta-sieve upper bound for primes in a short interval

The vertical mean-value lemma used in the Granville--Soundararajan form of
finite Halasz needs a genuinely short-interval prime estimate.  The global
Chebyshev bound is not sufficient.  This file records the first arithmetic
step of that estimate: primes in `(L,U]`, when `Q < L`, are contained in the
integers coprime to the product of the primes in `[3,Q]`.  The arbitrary-
interval beta sieve therefore gives a short-interval upper bound, with its
finite level remainder left explicit.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b

/-- Primes above `Q` are coprime to the product of all primes in `[3,Q]`. -/
theorem prime_Ioc_subset_coprime_primeBlockProduct
    {L U Q : ℕ} (hQL : Q < L) :
    (Finset.Ioc L U).filter Nat.Prime ⊆
      (Finset.Ioc L U).filter fun n ↦
        (primeBlockProduct (3, Q)).Coprime n := by
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  rw [← not_hasPrimeFactorInBlock_iff_coprime_primeBlockProduct]
  rintro ⟨q, hq, hqp⟩
  have hqData := mem_primesInBlock.mp hq
  have hqpEq : q = p :=
    (Nat.prime_dvd_prime_iff_eq hqData.1 hp.2).mp hqp
  have hpLower := (Finset.mem_Ioc.mp hp.1).1
  omega

/-- The cardinality of a short interval of primes is bounded by the
corresponding interval beta sieve.  This is the exact finite-level form;
no asymptotic choice of the sieve endpoint has yet been made. -/
theorem exists_card_prime_Ioc_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ L U Q S : ℕ, L ≤ U → Q < L → 3 ≤ Q → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((((Finset.Ioc L U).filter Nat.Prime).card : ℝ)) ≤
          ((U - L : ℕ) : ℝ) *
              ((1 + eta) * primeBlockDensity (3, Q)) +
            (((Q ^ S : ℕ) : ℝ) ^ 2) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ :=
    Erdos67b.MRIntervalBetaSieve.exists_card_Ioc_filter_coprime_primeBlockProduct_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro L U Q S hLU hQL hQ hS hlog
  dsimp only
  have hcard :
      ((Finset.Ioc L U).filter Nat.Prime).card ≤
        ((Finset.Ioc L U).filter fun n ↦
          (primeBlockProduct (3, Q)).Coprime n).card :=
    Finset.card_le_card (prime_Ioc_subset_coprime_primeBlockProduct hQL)
  have hcardReal :
      ((((Finset.Ioc L U).filter Nat.Prime).card : ℝ)) ≤
        ((((Finset.Ioc L U).filter fun n ↦
          (primeBlockProduct (3, Q)).Coprime n).card : ℝ)) := by
    exact_mod_cast hcard
  exact hcardReal.trans
    (hbeta L U 3 Q S hLU (by norm_num) hQ hS hlog)

/-- Mertens-discharge of the density in the short-prime interval bound. -/
theorem exists_card_prime_Ioc_beta_mertens_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ L U Q S : ℕ, L ≤ U → Q < L → 3 ≤ Q → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((((Finset.Ioc L U).filter Nat.Prime).card : ℝ)) ≤
          ((U - L : ℕ) : ℝ) *
              ((1 + eta) *
                (Real.exp (2 * PrimeEstimates.mertensBound) *
                  (Real.log 2 / Real.log (Q : ℝ)))) +
            (((Q ^ S : ℕ) : ℝ) ^ 2) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ := exists_card_prime_Ioc_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro L U Q S hLU hQL hQ hS hlog
  dsimp only
  have hraw := hbeta L U Q S hLU hQL hQ hS hlog
  have hdensity := primeBlockDensity_le_mertensRatio
    (L := 3) (U := Q) (by norm_num) hQ
  have heta : 0 ≤
      1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    positivity
  calc
    ((((Finset.Ioc L U).filter Nat.Prime).card : ℝ)) ≤
        ((U - L : ℕ) : ℝ) *
            ((1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              primeBlockDensity (3, Q)) +
          (((Q ^ S : ℕ) : ℝ) ^ 2) := hraw
    _ ≤ ((U - L : ℕ) : ℝ) *
            ((1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (Real.exp (2 * PrimeEstimates.mertensBound) *
                (Real.log 2 / Real.log (Q : ℝ)))) +
          (((Q ^ S : ℕ) : ℝ) ^ 2) := by
      gcongr
      simpa using hdensity

/-- Every logarithmic prime weight in `(L,U]` is at most `log U`. -/
theorem sum_log_prime_Ioc_le_card_mul_log
    {L U : ℕ} :
    (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime, Real.log (p : ℝ)) ≤
      ((((Finset.Ioc L U).filter Nat.Prime).card : ℝ)) *
        Real.log (U : ℝ) := by
  calc
    (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime, Real.log (p : ℝ)) ≤
        ∑ _p ∈ (Finset.Ioc L U).filter Nat.Prime,
          Real.log (U : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpU := (Finset.mem_Ioc.mp hpData.1).2
      exact Real.log_le_log (by exact_mod_cast hpData.2.pos)
        (by exact_mod_cast hpU)
    _ = ((((Finset.Ioc L U).filter Nat.Prime).card : ℝ)) *
          Real.log (U : ℝ) := by simp

/-- Log-weighted short-prime-interval form of the beta-sieve estimate. -/
theorem exists_sum_log_prime_Ioc_beta_mertens_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ L U Q S : ℕ, L ≤ U → Q < L → 3 ≤ Q → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
            Real.log (p : ℝ)) ≤
          (((U - L : ℕ) : ℝ) *
                ((1 + eta) *
                  (Real.exp (2 * PrimeEstimates.mertensBound) *
                    (Real.log 2 / Real.log (Q : ℝ)))) +
              (((Q ^ S : ℕ) : ℝ) ^ 2)) *
            Real.log (U : ℝ) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ := exists_card_prime_Ioc_beta_mertens_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro L U Q S hLU hQL hQ hS hlog
  dsimp only
  exact (sum_log_prime_Ioc_le_card_mul_log (L := L) (U := U)).trans
    (mul_le_mul_of_nonneg_right
      (hbeta L U Q S hLU hQL hQ hS hlog)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ U by omega))))

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.exists_sum_log_prime_Ioc_beta_mertens_bound
