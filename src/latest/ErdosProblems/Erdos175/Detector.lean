/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
# The Granville--Ramaré prime-power detector

This file formalizes the arithmetic inequality (7.1) in Granville and
Ramaré, *Explicit bounds on exponential sums and the scarcity of squarefree
binomial coefficients* (Mathematika 43 (1996), 73--107).  The analytic
Fourier estimate which follows (7.1) is deliberately not part of this file.

For integral quotients the paper uses the sawtooth convention `ψ(x) = 0`,
not `-1/2`.  Since all arguments needed here are rational numbers `a / d`,
we use a division-free definition in terms of `a % d`.
-/

import Mathlib

namespace Erdos175.Detector

open Nat Finset
open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- The sawtooth value at the rational number `a / d`, with the convention
that it vanishes at integers. -/
noncomputable def sawtoothQuot (a d : ℕ) : ℝ :=
  if d ∣ a then 0 else ((a % d : ℕ) : ℝ) / d - 1 / 2

/-- The finite integer interval written in the paper as
`sqrt n < d ≤ sqrt (2n)`.  Describing it by squares avoids all rounding
choices at the two endpoints. -/
def squareRootInterval (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * n)).filter fun d => n < d ^ 2 ∧ d ^ 2 ≤ 2 * n

lemma mem_squareRootInterval {n d : ℕ} :
    d ∈ squareRootInterval n ↔ 1 ≤ d ∧ d ≤ 2 * n ∧ n < d ^ 2 ∧ d ^ 2 ≤ 2 * n := by
  simp [squareRootInterval, and_assoc]

/-- If adding the two residues of `n` modulo `d` creates no carry, the
sawtooth defect is zero when `d ∣ n` and `1/2` otherwise. -/
lemma sawtoothQuot_two_mul_of_no_carry {n d : ℕ} (hd : 0 < d)
    (hcarry : n % d + n % d < d) :
    sawtoothQuot (2 * n) d - 2 * sawtoothQuot n d =
      if d ∣ n then 0 else (1 / 2 : ℝ) := by
  have hmod : (2 * n) % d = n % d + n % d := by
    simpa [two_mul] using Nat.add_mod_of_add_mod_lt hcarry
  by_cases hdn : d ∣ n
  · have hd2n : d ∣ 2 * n := dvd_mul_of_dvd_right hdn 2
    simp [sawtoothQuot, hdn, hd2n]
  · have hd2n : ¬d ∣ 2 * n := by
      intro hd2n
      have hz : (2 * n) % d = 0 := Nat.mod_eq_zero_of_dvd hd2n
      have hnmod : n % d = 0 := by omega
      exact hdn (Nat.dvd_of_mod_eq_zero hnmod)
    rw [sawtoothQuot, if_neg hd2n, sawtoothQuot, if_neg hdn, if_neg hdn, hmod]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
    ring

/-- The square interval never contains `1`. -/
lemma one_lt_of_mem_squareRootInterval {n d : ℕ} (hd : d ∈ squareRootInterval n) : 1 < d := by
  rw [mem_squareRootInterval] at hd
  by_contra h
  have : d = 1 := by omega
  subst d
  norm_num at hd
  omega

/-- The Kummer step behind Corollary 3.2 and (7.1): a prime power `d` in
the square-root interval already forces a carry at the `d²` place.  If the
binomial coefficient is squarefree, there cannot also be a carry at the `d`
place. -/
lemma no_low_carry_of_primePow_interval {n d : ℕ}
    (hsq : Squarefree (Nat.choose (n + n) n))
    (hd : d ∈ squareRootInterval n) (hdpp : IsPrimePow d) :
    n % d + n % d < d := by
  obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff d).mp hdpp
  have hdmem := (mem_squareRootInterval.mp hd)
  have hdlo : n < d ^ 2 := hdmem.2.2.1
  have hdhi : d ^ 2 ≤ n + n := by simpa [two_mul] using hdmem.2.2.2
  have hpone : 1 < p := hp.one_lt
  let b := Nat.log p (n + n) + 1
  have hformula := Nat.factorization_choose' (n := n) (k := n) hp
    (b := b) (Nat.lt_succ_self _)
  have hsfac : (Nat.choose (n + n) n).factorization p ≤ 1 :=
    hsq.natFactorization_le_one p
  rw [hformula] at hsfac
  by_contra hnot
  have hlow : d ≤ n % d + n % d := by omega
  have hpow_a : p ^ a = d := hpa
  have hpow_two_a : p ^ (2 * a) = d ^ 2 := by
    rw [show 2 * a = a + a by omega, pow_add, hpa, pow_two]
  have hdle : d ≤ n + n := by
    have hdone : 1 ≤ d := hdmem.1
    calc
      d ≤ d ^ 2 := by nlinarith
      _ ≤ n + n := hdhi
  have ha_log : a < b := by
    dsimp [b]
    have := Nat.le_log_of_pow_le hpone (hpa ▸ hdle)
    omega
  have htwoa_log : 2 * a < b := by
    dsimp [b]
    have := Nat.le_log_of_pow_le hpone (hpow_two_a ▸ hdhi)
    omega
  let carries :=
    (Finset.Ico 1 b).filter fun i => p ^ i ≤ n % p ^ i + n % p ^ i
  have ha_mem : a ∈ carries := by
    simp only [carries, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨ha, ha_log⟩, by simpa [hpa] using hlow⟩
  have htwoa_mem : 2 * a ∈ carries := by
    simp only [carries, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, htwoa_log⟩, ?_⟩
    simpa [hpow_two_a, Nat.mod_eq_of_lt hdlo] using hdhi
  have hne : a ≠ 2 * a := by omega
  have : 1 < carries.card :=
    Finset.one_lt_card.mpr ⟨a, ha_mem, 2 * a, htwoa_mem, hne⟩
  exact (not_lt_of_ge hsfac) (by simpa [carries] using this)

/-- The pointwise summand obtained by moving the two sawtooth sums in (7.1)
to the same side. -/
noncomputable def weightedDefect (n d : ℕ) : ℝ :=
  (sawtoothQuot (2 * n) d - 2 * sawtoothQuot n d) *
    ArithmeticFunction.vonMangoldt d

/-- Every prime-power summand in the square-root interval has nonnegative
defect.  Non-prime-powers have zero von Mangoldt weight. -/
lemma weightedDefect_nonneg {n d : ℕ}
    (hsq : Squarefree (Nat.choose (n + n) n))
    (hd : d ∈ squareRootInterval n) : 0 ≤ weightedDefect n d := by
  by_cases hdpp : IsPrimePow d
  · have hcarry := no_low_carry_of_primePow_interval hsq hd hdpp
    rw [weightedDefect,
      sawtoothQuot_two_mul_of_no_carry (Nat.zero_lt_of_lt (one_lt_of_mem_squareRootInterval hd))
        hcarry]
    split_ifs <;> positivity
  · rw [weightedDefect, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hdpp, mul_zero]

/-- On terms coprime to `2n`, the defect is exactly half the von Mangoldt
weight. -/
lemma weightedDefect_eq_half {n d : ℕ}
    (hsq : Squarefree (Nat.choose (n + n) n))
    (hd : d ∈ squareRootInterval n) (hcop : Nat.Coprime d (2 * n)) :
    weightedDefect n d = (1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt d := by
  by_cases hdpp : IsPrimePow d
  · have hcarry := no_low_carry_of_primePow_interval hsq hd hdpp
    have hdndvd : ¬d ∣ n := by
      intro hdn
      have hd2n : d ∣ 2 * n := dvd_mul_of_dvd_right hdn 2
      have hdgcd : d ∣ Nat.gcd d (2 * n) := Nat.dvd_gcd dvd_rfl hd2n
      have hd1 : d ∣ 1 := hcop ▸ hdgcd
      exact (one_lt_of_mem_squareRootInterval hd).ne' (Nat.dvd_one.mp hd1)
    rw [weightedDefect,
      sawtoothQuot_two_mul_of_no_carry (Nat.zero_lt_of_lt (one_lt_of_mem_squareRootInterval hd))
        hcarry,
      if_neg hdndvd]
  · rw [weightedDefect, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hdpp, mul_zero,
      mul_zero]

/-- Granville--Ramaré (7.1), in its exact prime-power/von-Mangoldt form.
The interval on the right is restricted by `(d,2n)=1`, as in the paper. -/
theorem sawtooth_mangoldt_detector (n : ℕ)
    (hsq : Squarefree (Nat.choose (n + n) n)) :
    (1 / 2 : ℝ) *
        (∑ d ∈ (squareRootInterval n).filter fun d => Nat.Coprime d (2 * n),
          ArithmeticFunction.vonMangoldt d) ≤
      |∑ d ∈ squareRootInterval n,
          sawtoothQuot (2 * n) d * ArithmeticFunction.vonMangoldt d| +
        2 * |∑ d ∈ squareRootInterval n,
          sawtoothQuot n d * ArithmeticFunction.vonMangoldt d| := by
  let good := (squareRootInterval n).filter fun d => Nat.Coprime d (2 * n)
  let allDefects := ∑ d ∈ squareRootInterval n, weightedDefect n d
  let firstSum := ∑ d ∈ squareRootInterval n,
    sawtoothQuot (2 * n) d * ArithmeticFunction.vonMangoldt d
  let secondSum := ∑ d ∈ squareRootInterval n,
    sawtoothQuot n d * ArithmeticFunction.vonMangoldt d
  have hgood :
      (1 / 2 : ℝ) *
          (∑ d ∈ good, ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ good, weightedDefect n d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := (Finset.mem_filter.mp hd)
    exact (weightedDefect_eq_half hsq hd'.1 hd'.2).symm
  have hsubset : good ⊆ squareRootInterval n := by
    exact Finset.filter_subset _ _
  have hsum : (∑ d ∈ good, weightedDefect n d) ≤ allDefects := by
    dsimp only [allDefects]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun d hd _ =>
      weightedDefect_nonneg hsq hd
  have hrewrite : allDefects = firstSum - 2 * secondSum := by
    simp only [allDefects, firstSum, secondSum, weightedDefect, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  calc
    (1 / 2 : ℝ) *
          (∑ d ∈ (squareRootInterval n).filter fun d => Nat.Coprime d (2 * n),
            ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ good, weightedDefect n d := by simpa only [good] using hgood
    _ ≤ allDefects := hsum
    _ = firstSum - 2 * secondSum := hrewrite
    _ ≤ |firstSum - 2 * secondSum| := le_abs_self _
    _ ≤ |firstSum| + |2 * secondSum| := abs_sub _ _
    _ = |firstSum| + 2 * |secondSum| := by rw [abs_mul]; norm_num
    _ = |∑ d ∈ squareRootInterval n,
          sawtoothQuot (2 * n) d * ArithmeticFunction.vonMangoldt d| +
        2 * |∑ d ∈ squareRootInterval n,
          sawtoothQuot n d * ArithmeticFunction.vonMangoldt d| := rfl

end Erdos175.Detector
