import ErdosProblems.Erdos823.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Squarefree abundancy ratios for Erdős Problem 823

This file proves the elementary analytic ingredient in Pollack's argument:
finite sums of `log ((p + 1) / p)` over arbitrarily large primes approximate
every nonnegative real number from above.  The corresponding product of the
primes is squarefree and has logarithmic abundancy equal to that sum.
-/

namespace Erdos823

open Filter Finset Topology
open scoped ArithmeticFunction.sigma BigOperators

noncomputable section

/-- The logarithmic abundancy contributed by a prime index, and zero at a
composite index. -/
def primeLogTerm (n : ℕ) : ℝ :=
  if n.Prime then Real.log (1 + 1 / (n : ℝ)) else 0

theorem primeLogTerm_nonneg (n : ℕ) : 0 ≤ primeLogTerm n := by
  rw [primeLogTerm]
  split_ifs with hn
  · apply Real.log_nonneg
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  · exact le_rfl

theorem primeLogTerm_le_inv (n : ℕ) :
    primeLogTerm n ≤ 1 / (n : ℝ) := by
  rw [primeLogTerm]
  split_ifs with hn
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.pos
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 1 / (n : ℝ) by positivity)
    simpa only [add_sub_cancel_left] using h
  · positivity

theorem prime_inv_le_two_mul_primeLogTerm (n : ℕ) :
    Set.indicator {p : ℕ | p.Prime} (fun p ↦ (1 : ℝ) / p) n ≤
      2 * primeLogTerm n := by
  by_cases hn : n.Prime
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, hn, if_true, primeLogTerm]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.pos
    have hlog := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 1 + 1 / (n : ℝ) by positivity)
    have hcalc : (1 : ℝ) / n ≤
        2 * (1 - (1 + 1 / (n : ℝ))⁻¹) := by
      field_simp
      nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn.one_le]
    exact hcalc.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, hn, if_false, primeLogTerm]
    norm_num

theorem primeLogTerm_not_summable : ¬ Summable primeLogTerm := by
  intro hsum
  apply not_summable_one_div_on_primes
  exact Summable.of_nonneg_of_le
    (fun n ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) _)
    prime_inv_le_two_mul_primeLogTerm (hsum.mul_left 2)

theorem primeLogTerm_partial_sums_tendsto_atTop :
    Tendsto (fun N ↦ ∑ n ∈ range N, primeLogTerm n) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact primeLogTerm_not_summable
  · exact primeLogTerm_nonneg

theorem primeLogTerm_tendsto_zero :
    Tendsto primeLogTerm atTop (nhds 0) := by
  exact squeeze_zero primeLogTerm_nonneg primeLogTerm_le_inv
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem exists_primeLog_tail_ge (N : ℕ) (t : ℝ) :
    ∃ M : ℕ, N ≤ M ∧ t ≤ ∑ n ∈ Ico N M, primeLogTerm n := by
  let S : ℝ := ∑ n ∈ range N, primeLogTerm n
  have hlarge : ∀ᶠ M : ℕ in atTop, t + S ≤
      ∑ n ∈ range M, primeLogTerm n :=
    primeLogTerm_partial_sums_tendsto_atTop.eventually
      (eventually_ge_atTop (t + S))
  obtain ⟨M, hNM, hM⟩ :=
    ((eventually_ge_atTop N).and hlarge).exists
  refine ⟨M, hNM, ?_⟩
  have hsplit := sum_range_add_sum_Ico primeLogTerm hNM
  dsimp only [S] at hM
  linarith

/-- A finite block of prime logarithmic abundancies, supported strictly above
any prescribed integer, approximates any positive target from above. -/
theorem exists_primeLog_block (B : ℕ) {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ N M : ℕ,
      B < N ∧ N < M ∧
      t ≤ ∑ n ∈ Ico N M, primeLogTerm n ∧
      ∑ n ∈ Ico N M, primeLogTerm n < t + ε := by
  have hevent : ∀ᶠ n : ℕ in atTop, primeLogTerm n < ε :=
    (tendsto_order.1 primeLogTerm_tendsto_zero).2 ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hevent
  let N := max (B + 1) N₀
  have hBN : B < N := by
    dsimp only [N]
    omega
  have hsmall : ∀ n, N ≤ n → primeLogTerm n < ε := by
    intro n hn
    apply hN₀ n
    exact (le_max_right (B + 1) N₀).trans hn
  let H : ∃ M : ℕ, N ≤ M ∧
      t ≤ ∑ n ∈ Ico N M, primeLogTerm n :=
    exists_primeLog_tail_ge N t
  let M := Nat.find H
  have hspec : N ≤ M ∧ t ≤
      ∑ n ∈ Ico N M, primeLogTerm n := Nat.find_spec H
  have hNM : N < M := by
    apply lt_of_le_of_ne hspec.1
    intro hEq
    have : (∑ n ∈ Ico N M, primeLogTerm n) = 0 := by
      rw [← hEq]
      simp
    linarith [hspec.2]
  have hNpred : N ≤ M - 1 := by omega
  have hpred : (∑ n ∈ Ico N (M - 1), primeLogTerm n) < t := by
    have hnot := Nat.find_min H (show M - 1 < M by omega)
    push_neg at hnot
    exact hnot hNpred
  have hsplit : (∑ n ∈ Ico N M, primeLogTerm n) =
      (∑ n ∈ Ico N (M - 1), primeLogTerm n) +
        primeLogTerm (M - 1) := by
    calc
      (∑ n ∈ Ico N M, primeLogTerm n) =
          ∑ n ∈ Ico N ((M - 1) + 1), primeLogTerm n := by
            congr 3 <;> omega
      _ = _ := sum_Ico_succ_top hNpred primeLogTerm
  refine ⟨N, M, hBN, hNM, hspec.2, ?_⟩
  rw [hsplit]
  linarith [hsmall (M - 1) hNpred]

/-- Product of the primes in the half-open interval `[N,M)`. -/
def primeBlockProduct (N M : ℕ) : ℕ :=
  ∏ p ∈ (Ico N M).filter Nat.Prime, p

theorem sum_primeLogTerm_Ico (N M : ℕ) :
    (∑ n ∈ Ico N M, primeLogTerm n) =
      ∑ p ∈ (Ico N M).filter Nat.Prime,
        Real.log (1 + 1 / (p : ℝ)) := by
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  simp only [primeLogTerm]

theorem sigma_primeBlockProduct (N M : ℕ) :
    σ 1 (primeBlockProduct N M) =
      ∏ p ∈ (Ico N M).filter Nat.Prime, (p + 1) := by
  let P := (Ico N M).filter Nat.Prime
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (mem_filter.1 hp).2
  change σ 1 (∏ p ∈ P, p) = ∏ p ∈ P, (p + 1)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime P hprime]
  apply prod_congr rfl
  intro p hp
  simpa using
    (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) (hprime p hp))

theorem log_sigma_div_primeBlockProduct (N M : ℕ) :
    Real.log
        ((σ 1 (primeBlockProduct N M) : ℕ) /
          (primeBlockProduct N M : ℝ)) =
      ∑ n ∈ Ico N M, primeLogTerm n := by
  let P := (Ico N M).filter Nat.Prime
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (mem_filter.1 hp).2
  have hsig : σ 1 (∏ p ∈ P, p) = ∏ p ∈ P, (p + 1) := by
    simpa only [P, primeBlockProduct] using sigma_primeBlockProduct N M
  rw [sum_primeLogTerm_Ico]
  change Real.log ((σ 1 (∏ p ∈ P, p) : ℕ) /
      ((∏ p ∈ P, p : ℕ) : ℝ)) = _
  rw [hsig]
  push_cast
  rw [← prod_div_distrib]
  rw [Real.log_prod]
  · apply sum_congr rfl
    intro p hp
    congr 1
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
    field_simp
  · intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    exact div_ne_zero (by positivity) hpR.ne'

/-- Squarefree logarithmic abundancies are dense from the right, even after
requiring the new integer to be coprime to an arbitrary positive modulus. -/
theorem exists_abundancy_approx (Q : ℕ) (hQ : 0 < Q)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    ∃ A : ℕ,
      0 < A ∧ Nat.Coprime A Q ∧
      t ≤ Real.log ((σ 1 A : ℕ) / (A : ℝ)) ∧
      Real.log ((σ 1 A : ℕ) / (A : ℝ)) < t + ε := by
  rcases ht.eq_or_lt with rfl | htpos
  · refine ⟨1, by norm_num, Nat.coprime_one_left Q, ?_, ?_⟩
    · norm_num [ArithmeticFunction.sigma_one]
    · simpa [ArithmeticFunction.sigma_one] using hε
  · obtain ⟨N, M, hQN, hNM, hlower, hupper⟩ :=
      exists_primeLog_block Q htpos hε
    let P := (Ico N M).filter Nat.Prime
    have hprime : ∀ p ∈ P, p.Prime := by
      intro p hp
      exact (mem_filter.1 hp).2
    have hpos : 0 < primeBlockProduct N M := by
      change 0 < ∏ p ∈ P, p
      exact Finset.prod_pos fun p hp ↦ (hprime p hp).pos
    have hcop : Nat.Coprime (primeBlockProduct N M) Q := by
      change Nat.Coprime (∏ p ∈ P, p) Q
      apply Nat.Coprime.prod_left
      intro p hp
      apply (hprime p hp).coprime_iff_not_dvd.mpr
      intro hpQ
      have hp_le_Q := Nat.le_of_dvd hQ hpQ
      have hp_mem : p ∈ Ico N M := (mem_filter.1 hp).1
      have hN_le_p := (mem_Ico.1 hp_mem).1
      omega
    refine ⟨primeBlockProduct N M, hpos, hcop, ?_, ?_⟩
    · rwa [log_sigma_div_primeBlockProduct]
    · rwa [log_sigma_div_primeBlockProduct]

end

end Erdos823
