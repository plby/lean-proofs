import ErdosProblems.Erdos587.HooleyRankinEuler

/-!
# Finite Euler majorants for the Rankin twist

A finite collection of integers supported on a prescribed prime set is
embedded into the divisors of its product. The multiplicative Euler
identity and the uniform local estimate then bound its weighted mass.
-/

open scoped BigOperators

namespace Erdos587

lemma sum_divisors_multiplicative_eq_euler (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, f d) =
      ∏ p ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization p + 1), f (p ^ k) := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    (hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast).multiplicative_factorization _ hn]
  apply Finset.prod_congr n.support_factorization
  intro p hp
  change (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) (p ^ n.factorization p) = _
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]

noncomputable def deltaRankinEulerWeight (β : ℝ) : ArithmeticFunction ℝ :=
  (((ArithmeticFunction.sigma 0 : ArithmeticFunction ℝ).pmul (deltaRankinWeight β)).pmul
    (Erdos421.arithmeticRpow (-1)))

lemma deltaRankinEulerWeight_isMultiplicative (β : ℝ) :
    (deltaRankinEulerWeight β).IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_sigma.natCast.pmul
    (deltaRankinWeight_isMultiplicative β)).pmul (Erdos421.arithmeticRpow_isMultiplicative (-1))

lemma deltaRankinEulerWeight_apply {n : ℕ} (hn : n ≠ 0) (β : ℝ) :
    deltaRankinEulerWeight β n = (n.divisors.card : ℝ) * deltaRankinWeight β n / n := by
  simp only [deltaRankinEulerWeight, ArithmeticFunction.pmul_apply,
    Erdos421.arithmeticRpow_apply hn, Real.rpow_neg_one, div_eq_mul_inv,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.sigma_zero_apply]

lemma deltaRankinEulerWeight_nonneg {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    0 ≤ deltaRankinEulerWeight β n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [deltaRankinEulerWeight_apply hn]
    exact div_nonneg (mul_nonneg (by positivity) (deltaRankinWeight_nonneg hβ n)) (by positivity)

theorem sum_deltaRankinEulerWeight_divisors_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, deltaRankinEulerWeight β d) ≤
      ∏ p ∈ n.primeFactors, (1 + 20 * (((p : ℝ) ^ β - 1) / p)) := by
  rw [sum_divisors_multiplicative_eq_euler _ (deltaRankinEulerWeight_isMultiplicative β) hn]
  apply Finset.prod_le_prod
  · intro p hp
    exact Finset.sum_nonneg (fun k _ => deltaRankinEulerWeight_nonneg hβ0 _)
  · intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have heq : (∑ k ∈ Finset.range (n.factorization p + 1), deltaRankinEulerWeight β (p ^ k)) =
        ∑ k ∈ Finset.range (n.factorization p + 1),
          ((p ^ k).divisors.card : ℝ) * deltaRankinWeight β (p ^ k) / (p ^ k : ℕ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact deltaRankinEulerWeight_apply (pow_ne_zero k hpprime.ne_zero) β
    rw [heq]
    exact delta_rankin_local_euler_le hpprime hβ0 hβ _

theorem sum_smooth_deltaRankinWeight_le (S P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hS : ∀ n ∈ S, n ≠ 0)
    (hsub : ∀ n ∈ S, n.primeFactors ⊆ P)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) :
    (∑ n ∈ S, (n.divisors.card : ℝ) * deltaRankinWeight β n / n) ≤
      ∏ p ∈ P, (1 + 20 * (((p : ℝ) ^ β - 1) / p)) := by
  let Q := ∏ n ∈ S, n
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr hS
  have hdivs : S ⊆ Q.divisors := by
    intro n hn
    exact Nat.mem_divisors.mpr ⟨Finset.dvd_prod_of_mem id hn, hQ⟩
  have hQsub : Q.primeFactors ⊆ P := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ ∏ n ∈ S, n := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨n, hn, hpn⟩ := (hpprime.prime.dvd_finsetProd_iff id).mp hpdvd
    exact hsub n hn (Nat.mem_primeFactors.mpr ⟨hpprime, hpn, hS n hn⟩)
  have hfactor (p : ℕ) (hp : p ∈ P) : 1 ≤ 1 + 20 * (((p : ℝ) ^ β - 1) / p) := by
    have hpow : (1 : ℝ) ≤ (p : ℝ) ^ β :=
      Real.one_le_rpow (by exact_mod_cast (hprime p hp).one_le) hβ0
    have hnonneg : 0 ≤ (((p : ℝ) ^ β - 1) / p) := by positivity
    linarith
  calc
    _ = ∑ n ∈ S, deltaRankinEulerWeight β n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (deltaRankinEulerWeight_apply (hS n hn) β).symm
    _ ≤ ∑ n ∈ Q.divisors, deltaRankinEulerWeight β n :=
      Finset.sum_le_sum_of_subset_of_nonneg hdivs
        (fun n _ _ => deltaRankinEulerWeight_nonneg hβ0 n)
    _ ≤ ∏ p ∈ Q.primeFactors, (1 + 20 * (((p : ℝ) ^ β - 1) / p)) :=
      sum_deltaRankinEulerWeight_divisors_le hβ0 hβ hQ
    _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le hQsub
      (fun p hp => zero_le_one.trans (hfactor p (hQsub hp))) (fun p hp _ => hfactor p hp)

end Erdos587
