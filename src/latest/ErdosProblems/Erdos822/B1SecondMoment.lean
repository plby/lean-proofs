/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1Arithmetic

/-!
# An elementary second moment for the B1 prime packets

The sample points are `n + 1` for `n ∈ range N`, so the exact count of
positive multiples is `Nat.card_multiples`.  Distinct primes give the
off-diagonal product divisibility needed for the second moment.
-/

namespace Erdos822

open scoped BigOperators

def packetIndicator (p n : ℕ) : ℝ := if p ∣ n then 1 else 0

def packetDivisorCount (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, packetIndicator p n

noncomputable def packetPrimeMean (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (1 : ℝ) / p

theorem packetDivisorCount_eq_card (P : Finset ℕ) (n : ℕ) :
    packetDivisorCount P n = ((P.filter (fun p ↦ p ∣ n)).card : ℝ) := by
  simp [packetDivisorCount, packetIndicator]

theorem packetPrimeMean_nonneg (P : Finset ℕ) : 0 ≤ packetPrimeMean P := by
  exact Finset.sum_nonneg fun p hp ↦ by positivity

theorem sum_packetIndicator_eq_div (N p : ℕ) :
    ∑ n ∈ Finset.range N, packetIndicator p (n + 1) =
      ((N / p : ℕ) : ℝ) := by
  calc
    (∑ n ∈ Finset.range N, packetIndicator p (n + 1)) =
        (((Finset.range N).filter (fun n ↦ p ∣ n + 1)).card : ℝ) := by
      simp [packetIndicator]
    _ = ((N / p : ℕ) : ℝ) := by rw [Nat.card_multiples]

theorem sum_packetDivisorCount_eq (N : ℕ) (P : Finset ℕ) :
    ∑ n ∈ Finset.range N, packetDivisorCount P (n + 1) =
      ∑ p ∈ P, ((N / p : ℕ) : ℝ) := by
  unfold packetDivisorCount
  rw [Finset.sum_comm]
  simp_rw [sum_packetIndicator_eq_div]

theorem natCast_div_le_cast_div (N p : ℕ) :
    ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
  exact Nat.cast_div_le

theorem cast_div_sub_one_le_natCast_div {N p : ℕ} (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have hmod := Nat.mod_lt N hp
  have hdiv := Nat.div_add_mod N p
  have hN : N < (N / p + 1) * p := by nlinarith
  have hNR : (N : ℝ) < (((N / p : ℕ) : ℝ) + 1) * (p : ℝ) := by
    exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hquot := (div_lt_iff₀ hpR).mpr hNR
  linarith

theorem sum_packetDivisorCount_lower (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (N : ℝ) * packetPrimeMean P - P.card ≤
      ∑ n ∈ Finset.range N, packetDivisorCount P (n + 1) := by
  rw [sum_packetDivisorCount_eq]
  calc
    (N : ℝ) * packetPrimeMean P - P.card =
        ∑ p ∈ P, ((N : ℝ) / p - 1) := by
      simp [packetPrimeMean, Finset.sum_sub_distrib, Finset.mul_sum,
        div_eq_mul_inv]
    _ ≤ ∑ p ∈ P, ((N / p : ℕ) : ℝ) := by
      exact Finset.sum_le_sum fun p hp ↦
        cast_div_sub_one_le_natCast_div (hP p hp).pos

theorem packetIndicator_mul_of_coprime {p q n : ℕ}
    (hcop : p.Coprime q) :
    packetIndicator p n * packetIndicator q n =
      packetIndicator (p * q) n := by
  have hiff : p * q ∣ n ↔ p ∣ n ∧ q ∣ n := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩
    · rintro ⟨hp, hq⟩
      exact hcop.mul_dvd_of_dvd_of_dvd hp hq
  unfold packetIndicator
  simp only [hiff]
  split_ifs <;> simp_all

theorem packetIndicator_mul_self (p n : ℕ) :
    packetIndicator p n * packetIndicator p n = packetIndicator p n := by
  unfold packetIndicator
  split_ifs <;> norm_num

/-- The second raw moment has the expected diagonal contribution and at
most the independent off-diagonal contribution. -/
theorem sum_packetDivisorCount_sq_le (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ Finset.range N, packetDivisorCount P (n + 1) ^ 2 ≤
      (N : ℝ) * packetPrimeMean P + N * packetPrimeMean P ^ 2 := by
  have hpair (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      (∑ n ∈ Finset.range N,
        packetIndicator p (n + 1) * packetIndicator q (n + 1)) ≤
        (if p = q then (N : ℝ) / p else 0) +
          (N : ℝ) / ((p : ℝ) * q) := by
    by_cases hpq : p = q
    · subst q
      simp_rw [packetIndicator_mul_self, sum_packetIndicator_eq_div]
      simp only [ite_true]
      exact (natCast_div_le_cast_div N p).trans (le_add_of_nonneg_right (by positivity))
    · have hcop := (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
      simp_rw [packetIndicator_mul_of_coprime hcop,
        sum_packetIndicator_eq_div]
      simpa [hpq, Nat.cast_mul] using natCast_div_le_cast_div N (p * q)
  calc
    (∑ n ∈ Finset.range N, packetDivisorCount P (n + 1) ^ 2) =
        ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Finset.range N,
          packetIndicator p (n + 1) * packetIndicator q (n + 1) := by
      simp only [packetDivisorCount, pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ ≤ ∑ p ∈ P, ∑ q ∈ P,
        ((if p = q then (N : ℝ) / p else 0) +
          (N : ℝ) / ((p : ℝ) * q)) := by
      exact Finset.sum_le_sum fun p hp ↦ Finset.sum_le_sum fun q hq ↦ hpair p hp q hq
    _ = (N : ℝ) * packetPrimeMean P + N * packetPrimeMean P ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      have hdiag : (∑ p ∈ P, ∑ q ∈ P,
          if p = q then (N : ℝ) / p else 0) =
          (N : ℝ) * packetPrimeMean P := by
        simp [packetPrimeMean, Finset.mul_sum, div_eq_mul_inv]
      rw [hdiag]
      congr 1
      simp only [packetPrimeMean, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- Centering at the independent reciprocal-prime mean costs only the
rounding error in the first moment. -/
theorem sum_packetDivisorCount_variance_le (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ Finset.range N,
        (packetDivisorCount P (n + 1) - packetPrimeMean P) ^ 2 ≤
      (N : ℝ) * packetPrimeMean P + 2 * packetPrimeMean P * P.card := by
  let μ := packetPrimeMean P
  have hμ : 0 ≤ μ := packetPrimeMean_nonneg P
  have hfirst := sum_packetDivisorCount_lower N P hP
  have hsecond := sum_packetDivisorCount_sq_le N P hP
  have hidentity :
      (∑ n ∈ Finset.range N, (packetDivisorCount P (n + 1) - μ) ^ 2) =
        (∑ n ∈ Finset.range N, packetDivisorCount P (n + 1) ^ 2) -
          2 * μ * (∑ n ∈ Finset.range N, packetDivisorCount P (n + 1)) +
            N * μ ^ 2 := by
    calc
      (∑ n ∈ Finset.range N, (packetDivisorCount P (n + 1) - μ) ^ 2) =
          ∑ n ∈ Finset.range N,
            (packetDivisorCount P (n + 1) ^ 2 -
              (2 * μ) * packetDivisorCount P (n + 1) + μ ^ 2) := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  change _ ≤ (N : ℝ) * μ + 2 * μ * P.card
  rw [hidentity]
  have hfirstMul := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 2 * μ by positivity)
  dsimp only [μ] at hfirstMul ⊢
  nlinarith

/-- Sample points having fewer than two selected prime divisors. -/
noncomputable def packetFewDivisors (N : ℕ) (P : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun n ↦ packetDivisorCount P (n + 1) ≤ 1

/-- A completely finite lower-tail estimate.  No independence assumption
is made about the integers; the proof uses only exact multiples counts. -/
theorem card_packetFewDivisors_mul_mean_le
    (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ N)
    (hmean : 2 ≤ packetPrimeMean P) :
    ((packetFewDivisors N P).card : ℝ) * packetPrimeMean P ≤ 12 * N := by
  classical
  let μ := packetPrimeMean P
  have hμ : 0 < μ := by dsimp [μ]; linarith
  have hμ2 : 2 ≤ μ := hmean
  have hcardR : (P.card : ℝ) ≤ N := by exact_mod_cast hcard
  have hvar := sum_packetDivisorCount_variance_le N P hP
  have hvar' :
      (∑ n ∈ Finset.range N, (packetDivisorCount P (n + 1) - μ) ^ 2) ≤
        3 * N * μ := by
    change _ ≤ (N : ℝ) * μ + 2 * μ * P.card at hvar
    have hm := mul_le_mul_of_nonneg_left hcardR (show 0 ≤ 2 * μ by positivity)
    nlinarith
  have hpoint (n : ℕ) (hn : n ∈ packetFewDivisors N P) :
      μ ^ 2 / 4 ≤ (packetDivisorCount P (n + 1) - μ) ^ 2 := by
    have hc : packetDivisorCount P (n + 1) ≤ 1 :=
      (Finset.mem_filter.mp hn).2
    have hhalf : μ / 2 ≤ μ - packetDivisorCount P (n + 1) := by linarith
    have hsquare : (μ / 2) ^ 2 ≤ (μ - packetDivisorCount P (n + 1)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith)).mpr hhalf
    nlinarith
  have hlow :
      ((packetFewDivisors N P).card : ℝ) * (μ ^ 2 / 4) ≤
        ∑ n ∈ Finset.range N, (packetDivisorCount P (n + 1) - μ) ^ 2 := by
    calc
      ((packetFewDivisors N P).card : ℝ) * (μ ^ 2 / 4) =
          ∑ _n ∈ packetFewDivisors N P, μ ^ 2 / 4 := by simp
      _ ≤ ∑ n ∈ packetFewDivisors N P,
          (packetDivisorCount P (n + 1) - μ) ^ 2 :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ n ∈ Finset.range N,
          (packetDivisorCount P (n + 1) - μ) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun n hn hnot ↦ sq_nonneg _)
  have hmul :
      μ * (((packetFewDivisors N P).card : ℝ) * μ) ≤ μ * (12 * N) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hμ).mp hmul

/-- Failure of square divisibility in the totient forces fewer than two
prime divisors from any packet congruent to one modulo the chosen modulus. -/
theorem packetDivisorCount_le_one_of_not_sq_dvd_totient
    {n t : ℕ} {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime)
    (hcong : ∀ q ∈ P, t ∣ q - 1)
    (hfail : ¬ t ^ 2 ∣ Nat.totient n) :
    packetDivisorCount P n ≤ 1 := by
  rw [packetDivisorCount_eq_card]
  by_contra hnot
  have hcard : 1 < (P.filter (fun q ↦ q ∣ n)).card := by
    exact_mod_cast (lt_of_not_ge hnot)
  obtain ⟨q₁, hq₁, q₂, hq₂, hne⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨hq₁P, hq₁n⟩ := Finset.mem_filter.mp hq₁
  obtain ⟨hq₂P, hq₂n⟩ := Finset.mem_filter.mp hq₂
  exact hfail (sq_dvd_totient_of_two_prime_divisors
    (hP q₁ hq₁P) (hP q₂ hq₂P) hne hq₁n hq₂n
    (hcong q₁ hq₁P) (hcong q₂ hq₂P))

/-- Counting-form B1 estimate for one modulus, ready for a union bound. -/
theorem card_not_sq_dvd_totient_mul_packetMean_le
    (N t : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (hcard : P.card ≤ N)
    (hcong : ∀ q ∈ P, t ∣ q - 1)
    (hmean : 2 ≤ packetPrimeMean P) :
    (((Finset.range N).filter
      (fun n ↦ ¬ t ^ 2 ∣ Nat.totient (n + 1))).card : ℝ) *
        packetPrimeMean P ≤ 12 * N := by
  have hsub : (Finset.range N).filter
      (fun n ↦ ¬ t ^ 2 ∣ Nat.totient (n + 1)) ⊆ packetFewDivisors N P := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn'.1,
      packetDivisorCount_le_one_of_not_sq_dvd_totient hP hcong hn'.2⟩
  have hc :
      (((Finset.range N).filter
        (fun n ↦ ¬ t ^ 2 ∣ Nat.totient (n + 1))).card : ℝ) ≤
          (packetFewDivisors N P).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact (mul_le_mul_of_nonneg_right hc (packetPrimeMean_nonneg P)).trans
    (card_packetFewDivisors_mul_mean_le N P hP hcard hmean)

end Erdos822
