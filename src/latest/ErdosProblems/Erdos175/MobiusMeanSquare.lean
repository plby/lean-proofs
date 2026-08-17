/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# The Granville--Ramaré truncated Möbius mean square

This file supplies the arithmetic coefficient estimate used in the proof of
Erdős Problem 175.  It follows Section 10 of Granville--Ramaré,
*Explicit bounds on exponential sums and the scarcity of squarefree binomial
coefficients*, Mathematika 43 (1996), 73--107.

The first part is their Lemma 10.2.  Its proof is the elementary Davenport
argument: a coprime-filtered Möbius divisor sum is the indicator of the
integers all of whose prime factors divide the modulus, and the two relevant
sets meet only at `1`.
-/

namespace Erdos175

open scoped BigOperators
open ArithmeticFunction

/-! ## Granville--Ramaré Lemma 10.2 -/

/-- The Möbius function restricted to integers coprime to `q`. -/
noncomputable def coprimeMoebius (q : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if Nat.Coprime n q then ArithmeticFunction.moebius n else 0, by
    by_cases h : Nat.Coprime 0 q <;> simp [h]⟩

@[simp] theorem coprimeMoebius_apply (q n : ℕ) :
    coprimeMoebius q n =
      if Nat.Coprime n q then ArithmeticFunction.moebius n else 0 := rfl

theorem isMultiplicative_coprimeMoebius (q : ℕ) :
    (coprimeMoebius q).IsMultiplicative := by
  constructor
  · simp
  · intro m n hmn
    simp only [coprimeMoebius_apply]
    by_cases hm : Nat.Coprime m q
    · by_cases hn : Nat.Coprime n q
      · rw [if_pos (Nat.Coprime.mul_left hm hn), if_pos hm, if_pos hn,
          ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
      · rw [if_neg fun h =>
            hn (Nat.Coprime.coprime_dvd_left (dvd_mul_left n m) h),
          if_pos hm, if_neg hn, mul_zero]
    · rw [if_neg fun h =>
          hm (Nat.Coprime.coprime_dvd_left (dvd_mul_right m n) h),
        if_neg hm, zero_mul]

/-- Divisor sum of `coprimeMoebius q` on a positive prime power. -/
theorem sum_coprimeMoebius_divisors_prime_pow (q p k : ℕ)
    (hp : p.Prime) (hk : k ≠ 0) :
    ∑ d ∈ (p ^ k).divisors, coprimeMoebius q d = if p ∣ q then 1 else 0 := by
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
  have h0 : coprimeMoebius q (p ^ 0) = 1 := by simp
  by_cases hpq : p ∣ q
  · have hzero : ∀ i ∈ Finset.range k, coprimeMoebius q (p ^ (i + 1)) = 0 := by
      intro i _
      rw [coprimeMoebius_apply, if_neg]
      intro hco
      exact (hp.coprime_iff_not_dvd.mp
        (Nat.Coprime.coprime_dvd_left (dvd_pow_self p (Nat.succ_ne_zero i)) hco)) hpq
    rw [if_pos hpq, Finset.sum_congr rfl hzero, Finset.sum_const_zero, h0, zero_add]
  · have hc : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hpq
    have hterm : ∀ i ∈ Finset.range k,
        coprimeMoebius q (p ^ (i + 1)) = if i = 0 then (-1 : ℤ) else 0 := by
      intro i _
      rw [coprimeMoebius_apply, if_pos (Nat.Coprime.pow_left _ hc),
        ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero i)]
      rcases i with _ | j <;> simp
    rw [if_neg hpq, Finset.sum_congr rfl hterm,
      Finset.sum_ite_eq' (Finset.range k) 0 (fun _ => (-1 : ℤ)),
      if_pos (Finset.mem_range.mpr (Nat.pos_of_ne_zero hk)), h0]
    ring

/-- The coprime-filtered Möbius divisor sum is the indicator of the integers
all of whose prime factors divide the modulus. -/
theorem sum_coprimeMoebius_divisors (q : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, coprimeMoebius q d =
      if ∀ p ∈ m.primeFactors, p ∣ q then 1 else 0 := by
  classical
  have key : ((coprimeMoebius q *
        (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) m) =
      ∏ p ∈ m.primeFactors, (if p ∣ q then (1 : ℤ) else 0) := by
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
        ((isMultiplicative_coprimeMoebius q).mul
          ArithmeticFunction.isMultiplicative_zeta.natCast) hm]
    rw [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hk : m.factorization p ≠ 0 := by
      have := Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization])
      exact this
    rw [ArithmeticFunction.coe_mul_zeta_apply,
      sum_coprimeMoebius_divisors_prime_pow q p _ hpp hk]
  rw [← ArithmeticFunction.coe_mul_zeta_apply, key]
  by_cases hall : ∀ p ∈ m.primeFactors, p ∣ q
  · rw [if_pos hall,
      Finset.prod_congr rfl fun p hp => if_pos (hall p hp),
      Finset.prod_const_one]
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨p, hp, hpq⟩ := hall
    exact Finset.prod_eq_zero hp (if_neg hpq)

/-- The coprime Möbius--floor identity. -/
theorem coprime_moebius_floor_identity (q N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n q),
        (ArithmeticFunction.moebius n : ℤ) * ((N / n : ℕ) : ℤ) =
      (((Finset.Icc 1 N).filter
          (fun m => ∀ p ∈ m.primeFactors, p ∣ q)).card : ℤ) := by
  classical
  have stepA : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n q),
          (ArithmeticFunction.moebius n : ℤ) * ((N / n : ℕ) : ℤ) =
      ∑ p ∈ ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n q)).sigma
            (fun n => Finset.Icc 1 (N / n)),
          (ArithmeticFunction.moebius p.1 : ℤ) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
  have stepB : ∑ p ∈ ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n q)).sigma
            (fun n => Finset.Icc 1 (N / n)),
          (ArithmeticFunction.moebius p.1 : ℤ) =
      ∑ p ∈ (Finset.Icc 1 N).sigma
            (fun m => m.divisors.filter (fun d => Nat.Coprime d q)),
          (ArithmeticFunction.moebius p.2 : ℤ) := by
    apply Finset.sum_bij'
      (i := fun p _ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ))
      (j := fun p _ => (⟨p.2, p.1 / p.2⟩ : Σ _ : ℕ, ℕ))
    · rintro ⟨n, k⟩ hp
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hn1, hnN⟩, hnq⟩, hk1, hkNn⟩ := hp
      have hn0 : 0 < n := hn1
      have hnk : n * k ≤ N := by
        have := (Nat.le_div_iff_mul_le hn0).mp hkNn
        calc n * k = k * n := Nat.mul_comm n k
          _ ≤ N := this
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨le_trans hn1 (Nat.le_mul_of_pos_right n hk1), hnk⟩,
        ⟨dvd_mul_right n k, Nat.mul_ne_zero (by omega) (by omega)⟩, hnq⟩
    · rintro ⟨m, d⟩ hp
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors] at hp
      obtain ⟨⟨hm1, hmN⟩, ⟨hdm, hm0⟩, hdq⟩ := hp
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm (by omega)
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨⟨hd0, le_trans (Nat.le_of_dvd (by omega) hdm) hmN⟩, hdq⟩, ?_, ?_⟩
      · exact (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (by omega) hdm)
      · exact Nat.div_le_div_right hmN
    · rintro ⟨n, k⟩ hp
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hp
      have hn0 : 0 < n := hp.1.1.1
      simp only [Nat.mul_div_cancel_left k hn0]
    · rintro ⟨m, d⟩ hp
      rw [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hp
      have hdm : d ∣ m := hp.2.1.1
      simp only [Nat.mul_div_cancel' hdm]
    · rintro ⟨n, k⟩ _
      rfl
  rw [stepA, stepB, Finset.sum_sigma]
  have stepC : ∀ m ∈ Finset.Icc 1 N,
      (∑ d ∈ m.divisors.filter (fun d => Nat.Coprime d q),
          (ArithmeticFunction.moebius d : ℤ)) =
        if ∀ p ∈ m.primeFactors, p ∣ q then (1 : ℤ) else 0 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    calc
      ∑ d ∈ m.divisors.filter (fun d => Nat.Coprime d q),
            (ArithmeticFunction.moebius d : ℤ) =
          ∑ d ∈ m.divisors, coprimeMoebius q d := by
            rw [Finset.sum_filter]
            exact Finset.sum_congr rfl fun d _ => rfl
      _ = if ∀ p ∈ m.primeFactors, p ∣ q then (1 : ℤ) else 0 :=
        sum_coprimeMoebius_divisors q hm0
  rw [Finset.sum_congr rfl stepC, Finset.sum_boole]

/-- The `q`-smooth integers and integers coprime to `q` in `[1,N]` have
total cardinality at most `N+1`. -/
theorem card_smooth_add_card_coprime_le (q N : ℕ) :
    ((Finset.Icc 1 N).filter (fun m => ∀ p ∈ m.primeFactors, p ∣ q)).card +
      ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n q)).card ≤ N + 1 := by
  classical
  set B := (Finset.Icc 1 N).filter (fun m => ∀ p ∈ m.primeFactors, p ∣ q)
  set A := (Finset.Icc 1 N).filter (fun n => Nat.Coprime n q)
  have hunion : (B ∪ A).card ≤ N := by
    have hsub : B ∪ A ⊆ Finset.Icc 1 N :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    calc
      (B ∪ A).card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsub
      _ = N := by rw [Nat.card_Icc]; omega
  have hinter : (B ∩ A).card ≤ 1 := by
    have hsub : B ∩ A ⊆ {1} := by
      intro m hm
      rw [Finset.mem_inter, show B = _ by rfl, show A = _ by rfl,
        Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨⟨hm1, _⟩, hsmooth⟩, _, hco⟩ := hm
      rw [Finset.mem_singleton]
      by_contra hne
      have hp : m.minFac.Prime := Nat.minFac_prime hne
      have hpm : m.minFac ∣ m := Nat.minFac_dvd m
      have hpq : m.minFac ∣ q :=
        hsmooth m.minFac (Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩)
      have : m.minFac ∣ Nat.gcd m q := Nat.dvd_gcd hpm hpq
      rw [hco] at this
      exact hp.ne_one (Nat.dvd_one.mp this)
    calc
      (B ∩ A).card ≤ ({1} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton 1
  calc
    B.card + A.card = (B ∪ A).card + (B ∩ A).card :=
      (Finset.card_union_add_card_inter B A).symm
    _ ≤ N + 1 := Nat.add_le_add hunion hinter

/-- **Granville--Ramaré Lemma 10.2.** -/
theorem abs_coprime_mobius_sum_le_one (q N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n q),
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)| ≤ 1 := by
  classical
  set A := (Finset.Icc 1 N).filter (fun n => Nat.Coprime n q)
  set B := (Finset.Icc 1 N).filter (fun m => ∀ p ∈ m.primeFactors, p ∣ q)
  set S : ℝ := ∑ n ∈ A, ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)
  have h1A : (1 : ℕ) ∈ A := by
    rw [show A = _ by rfl, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hN⟩, Nat.coprime_one_left q⟩
  have hcardA : 1 ≤ A.card := Finset.card_pos.mpr ⟨1, h1A⟩
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsplit : (N : ℝ) * S = (B.card : ℝ) +
      ∑ n ∈ A, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
        ((N % n : ℕ) : ℝ) / (n : ℝ) := by
    have hterm : ∀ n ∈ A,
        (N : ℝ) * (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)) =
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) * ((N / n : ℕ) : ℝ) +
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              ((N % n : ℕ) : ℝ) / (n : ℝ) := by
      intro n hn
      rw [show A = _ by rfl, Finset.mem_filter, Finset.mem_Icc] at hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1.1
      have hdm : ((N / n : ℕ) : ℝ) * (n : ℝ) + ((N % n : ℕ) : ℝ) =
          (N : ℝ) := by exact_mod_cast Nat.div_add_mod' N n
      have hsplitn : (N : ℝ) / (n : ℝ) =
          ((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) / (n : ℝ) := by
        rw [div_eq_iff (ne_of_gt hn0), add_mul, div_mul_cancel₀ _ (ne_of_gt hn0)]
        linarith [hdm]
      calc
        (N : ℝ) * (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)) =
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) * ((N : ℝ) / (n : ℝ)) := by ring
        _ = ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) / (n : ℝ)) := by rw [hsplitn]
        _ = ((ArithmeticFunction.moebius n : ℤ) : ℝ) * ((N / n : ℕ) : ℝ) +
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              ((N % n : ℕ) : ℝ) / (n : ℝ) := by ring
    rw [show S = _ by rfl, Finset.mul_sum, Finset.sum_congr rfl hterm,
      Finset.sum_add_distrib]
    congr 1
    calc
      ∑ n ∈ A, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * ((N / n : ℕ) : ℝ) =
          ((∑ n ∈ A, (ArithmeticFunction.moebius n : ℤ) *
            ((N / n : ℕ) : ℤ) : ℤ) : ℝ) := by push_cast; rfl
      _ = ((B.card : ℤ) : ℝ) := by
        rw [show A = _ by rfl, show B = _ by rfl,
          coprime_moebius_floor_identity q N]
      _ = (B.card : ℝ) := by push_cast; rfl
  have herr : |∑ n ∈ A, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
        ((N % n : ℕ) : ℝ) / (n : ℝ)| ≤ (A.card : ℝ) - 1 := by
    have hzero1 : ((ArithmeticFunction.moebius 1 : ℤ) : ℝ) *
        ((N % 1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = 0 := by simp [Nat.mod_one]
    rw [← Finset.sum_erase A hzero1]
    have hstep : |∑ n ∈ A.erase 1, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          ((N % n : ℕ) : ℝ) / (n : ℝ)| ≤ ∑ _n ∈ A.erase 1, (1 : ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun n hn => ?_
      have hnA := Finset.mem_of_mem_erase hn
      rw [show A = _ by rfl, Finset.mem_filter, Finset.mem_Icc] at hnA
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnA.1.1
      have hmu : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      have hmod : ((N % n : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
        rw [div_le_one hn0]
        exact_mod_cast le_of_lt (Nat.mod_lt N (by omega))
      have hmodnn : (0 : ℝ) ≤ ((N % n : ℕ) : ℝ) / (n : ℝ) := by positivity
      calc
        |((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              ((N % n : ℕ) : ℝ) / (n : ℝ)| =
            |((ArithmeticFunction.moebius n : ℤ) : ℝ)| *
              (((N % n : ℕ) : ℝ) / (n : ℝ)) := by
                rw [mul_div_assoc, abs_mul, abs_of_nonneg hmodnn]
        _ ≤ 1 * 1 := mul_le_mul hmu hmod hmodnn (by norm_num)
        _ = 1 := one_mul 1
    refine le_trans hstep ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem h1A, Nat.cast_sub hcardA, Nat.cast_one]
  have hcount : (B.card : ℝ) + (A.card : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast card_smooth_add_card_coprime_le q N
  have hNS : |(N : ℝ) * S| ≤ (N : ℝ) := by
    rw [hsplit]
    calc
      |(B.card : ℝ) + ∑ n ∈ A, ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
          ((N % n : ℕ) : ℝ) / (n : ℝ)| ≤
          |(B.card : ℝ)| + |∑ n ∈ A,
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
              ((N % n : ℕ) : ℝ) / (n : ℝ)| := abs_add_le _ _
      _ ≤ (B.card : ℝ) + ((A.card : ℝ) - 1) := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (B.card : ℝ))]
        linarith [herr]
      _ ≤ (N : ℝ) := by linarith
  rw [abs_mul, abs_of_pos hNR] at hNS
  have h1 : (N : ℝ) * |S| ≤ (N : ℝ) * 1 := by linarith
  exact le_of_mul_le_mul_left h1 hNR

/-! ## The elementary squarefree-density estimates of Lemma 10.3 -/

/-- Integers not divisible by either `4` or `9`.  Every squarefree integer is
in this set. -/
def fourNineFree (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter fun n => ¬4 ∣ n ∧ ¬9 ∣ n

/-- Exact inclusion--exclusion formula for `fourNineFree`. -/
theorem card_fourNineFree (N : ℕ) :
    (fourNineFree N).card = N - N / 4 - N / 9 + N / 36 := by
  classical
  let s := Finset.Ioc 0 N
  let A := s.filter fun n => 4 ∣ n
  let B := s.filter fun n => 9 ∣ n
  let G := fourNineFree N
  have hs : s.card = N := by simp [s]
  have hA : A.card = N / 4 := by
    simpa [A, s] using Nat.Ioc_filter_dvd_card_eq_div N 4
  have hB : B.card = N / 9 := by
    simpa [B, s] using Nat.Ioc_filter_dvd_card_eq_div N 9
  have hAB : (A ∩ B).card = N / 36 := by
    have heq : A ∩ B = s.filter fun n => 36 ∣ n := by
      ext n
      simp only [A, B, Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hns, h4⟩, _, h9⟩
        exact ⟨hns, by
          rw [show (36 : ℕ) = 4 * 9 by norm_num]
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h9⟩
      · rintro ⟨hns, h36⟩
        exact ⟨⟨hns, dvd_trans (by norm_num : 4 ∣ 36) h36⟩,
          hns, dvd_trans (by norm_num : 9 ∣ 36) h36⟩
    rw [heq]
    simpa [s] using Nat.Ioc_filter_dvd_card_eq_div N 36
  have hpartition : G ∪ (A ∪ B) = s := by
    ext n
    simp only [G, fourNineFree, A, B, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdis : Disjoint G (A ∪ B) := by
    rw [Finset.disjoint_left]
    intro n hnG hnU
    simp only [G, fourNineFree, Finset.mem_filter] at hnG
    simp only [A, B, Finset.mem_union, Finset.mem_filter] at hnU
    rcases hnU with h4 | h9
    · exact hnG.2.1 h4.2
    · exact hnG.2.2 h9.2
  have hpartcard : G.card + (A ∪ B).card = N := by
    rw [← hs, ← hpartition, Finset.card_union_of_disjoint hdis]
  have hunion : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  change G.card = N - N / 4 - N / 9 + N / 36
  omega

/-- The `4`--`9` sieve gives the uniform density bound used by
Granville--Ramaré. -/
theorem three_mul_card_fourNineFree_le (N : ℕ) :
    3 * (fourNineFree N).card ≤ 2 * (N + 2) := by
  rw [card_fourNineFree]
  omega

/-- Finite summation by parts for reciprocal weights, in the exact form used
below. -/
theorem sum_div_eq_prefix_sum (a : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ)) =
      (∑ n ∈ Finset.Icc 1 N, a n) / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          (∑ k ∈ Finset.Icc 1 n, a k) / ((n : ℝ) * (n + 1 : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hN,
        Finset.sum_Icc_succ_top (by omega), ih]
      have hNR : (N : ℝ) ≠ 0 := by positivity
      have hNsR : (N + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring

/-- The square of the real Möbius value is the indicator of squarefreeness,
summed over an initial interval. -/
theorem sum_mobius_sq_eq_card_squarefree (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) =
      (((Finset.Icc 1 N).filter Squarefree).card : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) =
        ∑ n ∈ Finset.Icc 1 N, if Squarefree n then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n _
          rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
          split_ifs <;> norm_num
    _ = (((Finset.Icc 1 N).filter Squarefree).card : ℝ) := by
      rw [Finset.sum_boole]

/-- The number of squarefree integers in `[1,N]` is at most
`(2/3)(N+2)`. -/
theorem three_mul_card_squarefree_le (N : ℕ) :
    3 * ((Finset.Icc 1 N).filter Squarefree).card ≤ 2 * (N + 2) := by
  classical
  apply le_trans (Nat.mul_le_mul_left 3 (Finset.card_le_card ?_))
    (three_mul_card_fourNineFree_le N)
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  rw [fourNineFree, Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨hn.1.1, hn.1.2⟩, ?_, ?_⟩
  · intro h4
    have hu : IsUnit (2 : ℕ) := hn.2 2 (by simpa using h4)
    norm_num at hu
  · intro h9
    have hu : IsUnit (3 : ℕ) := hn.2 3 (by simpa using h9)
    norm_num at hu

/-- Real-valued form of the squarefree-density prefix bound. -/
theorem sum_mobius_sq_le_two_thirds (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) ≤
      (2 / 3 : ℝ) * (N + 2 : ℕ) := by
  rw [sum_mobius_sq_eq_card_squarefree]
  have h := three_mul_card_squarefree_le N
  have hR : (3 : ℝ) * (((Finset.Icc 1 N).filter Squarefree).card : ℝ) ≤
      2 * (N + 2 : ℕ) := by exact_mod_cast h
  nlinarith

/-- The elementary telescoping identity behind partial summation of the
density bound. -/
theorem squarefree_density_weight_identity (N : ℕ) (hN : 1 ≤ N) :
    (N + 2 : ℝ) / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          (n + 2 : ℝ) / ((n : ℝ) * (n + 1 : ℝ)) =
      (harmonic N : ℝ) + 2 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [harmonic]
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, harmonic_succ]
      push_cast
      have hNR : (N : ℝ) ≠ 0 := by positivity
      have hNsR : (N + 1 : ℝ) ≠ 0 := by positivity
      calc
        ((N : ℝ) + 1 + 2) / ((N : ℝ) + 1) +
              ((∑ k ∈ Finset.Ico 1 N,
                (↑k + 2) / (↑k * (↑k + 1))) +
                (↑N + 2) / (↑N * (↑N + 1))) =
            ((N + 2 : ℝ) / (N : ℝ) +
              ∑ k ∈ Finset.Ico 1 N,
                (↑k + 2) / (↑k * (↑k + 1))) +
              1 / (N + 1 : ℝ) := by
                field_simp
                push_cast
                ring
        _ = ((harmonic N : ℝ) + 2) + 1 / (N + 1 : ℝ) := by rw [ih]
        _ = (harmonic N : ℝ) + (N + 1 : ℝ)⁻¹ + 2 := by
          rw [one_div]
          ring

/-- First inequality of Granville--Ramaré Lemma 10.3. -/
theorem sum_mobius_sq_div_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2) / (n : ℝ)) ≤
      (2 / 3 : ℝ) * (Real.log N + 3) := by
  rw [sum_div_eq_prefix_sum
    (fun n => (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) N hN]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hend := div_le_div_of_nonneg_right (sum_mobius_sq_le_two_thirds N)
    (le_of_lt hNpos)
  have hsum :
      (∑ n ∈ Finset.Ico 1 N,
          (∑ k ∈ Finset.Icc 1 n,
            (((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2)) /
              ((n : ℝ) * (n + 1 : ℝ))) ≤
        ∑ n ∈ Finset.Ico 1 N,
          ((2 / 3 : ℝ) * (n + 2 : ℕ)) /
            ((n : ℝ) * (n + 1 : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    apply div_le_div_of_nonneg_right (sum_mobius_sq_le_two_thirds n)
    positivity
  have hcombine :
      ((2 / 3 : ℝ) * (N + 2 : ℕ)) / (N : ℝ) +
          ∑ n ∈ Finset.Ico 1 N,
            ((2 / 3 : ℝ) * (n + 2 : ℕ)) /
              ((n : ℝ) * (n + 1 : ℝ)) =
        (2 / 3 : ℝ) * ((harmonic N : ℝ) + 2) := by
    rw [← squarefree_density_weight_identity N hN]
    push_cast
    have hfac :
        (∑ n ∈ Finset.Ico 1 N,
            (2 / 3 : ℝ) * (n + 2 : ℝ) / ((n : ℝ) * (n + 1 : ℝ))) =
          (2 / 3 : ℝ) *
            ∑ n ∈ Finset.Ico 1 N,
              (n + 2 : ℝ) / ((n : ℝ) * (n + 1 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hfac]
    ring
  have hharm : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  calc
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          (∑ k ∈ Finset.Icc 1 n,
            (((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2)) /
              ((n : ℝ) * (n + 1 : ℝ)) ≤
      ((2 / 3 : ℝ) * (N + 2 : ℕ)) / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          ((2 / 3 : ℝ) * (n + 2 : ℕ)) /
            ((n : ℝ) * (n + 1 : ℝ)) := add_le_add hend hsum
    _ = (2 / 3 : ℝ) * ((harmonic N : ℝ) + 2) := hcombine
    _ ≤ (2 / 3 : ℝ) * (Real.log N + 3) := by nlinarith

/-- The real square of the Möbius function. -/
noncomputable def mobiusSqReal (n : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)

theorem mobiusSqReal_nonneg (n : ℕ) : 0 ≤ mobiusSqReal n := by
  exact sq_nonneg _

theorem mobiusSqReal_eq_one_of_squarefree {n : ℕ} (hn : Squarefree n) :
    mobiusSqReal n = 1 := by
  rw [mobiusSqReal, ← Int.cast_pow, ArithmeticFunction.moebius_sq, if_pos hn]
  norm_num

theorem mobiusSqReal_eq_zero_of_not_squarefree {n : ℕ} (hn : ¬Squarefree n) :
    mobiusSqReal n = 0 := by
  rw [mobiusSqReal, ← Int.cast_pow, ArithmeticFunction.moebius_sq, if_neg hn]
  norm_num

/-- For a squarefree number every divisor and complementary divisor is
squarefree.  For a non-squarefree number the left side below vanishes. -/
theorem mobiusSqReal_card_divisors_div_le_convolution
    {n : ℕ} (hn : 1 ≤ n) :
    mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ) ≤
      ∑ d ∈ n.divisors,
        (mobiusSqReal d / (d : ℝ)) *
          (mobiusSqReal (n / d) / ((n / d : ℕ) : ℝ)) := by
  classical
  by_cases hsq : Squarefree n
  · rw [mobiusSqReal_eq_one_of_squarefree hsq]
    have hterm : ∀ d ∈ n.divisors,
        (mobiusSqReal d / (d : ℝ)) *
            (mobiusSqReal (n / d) / ((n / d : ℕ) : ℝ)) = 1 / (n : ℝ) := by
      intro d hd
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdsq : Squarefree d := hsq.squarefree_of_dvd hdn
      have hqsq : Squarefree (n / d) :=
        hsq.squarefree_of_dvd ⟨d, (Nat.div_mul_cancel hdn).symm⟩
      rw [mobiusSqReal_eq_one_of_squarefree hdsq,
        mobiusSqReal_eq_one_of_squarefree hqsq]
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
      simp only [one_div]
      rw [← mul_inv, ← Nat.cast_mul, hmul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    simp only [one_mul, div_eq_mul_inv]
    exact le_rfl
  · rw [mobiusSqReal_eq_zero_of_not_squarefree hsq, zero_mul, zero_div]
    exact Finset.sum_nonneg fun d _ =>
      mul_nonneg (div_nonneg (mobiusSqReal_nonneg d) (by positivity))
        (div_nonneg (mobiusSqReal_nonneg (n / d)) (by positivity))

/-- Reindex a divisor convolution by its factor pair. -/
theorem sum_divisor_convolution_eq_sum_factor_pairs
    (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d * f (n / d)) =
      ∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
          (fun p => p.1 * p.2 ≤ N),
        f p.1 * f p.2 := by
  classical
  rw [Finset.sum_sigma']
  apply Finset.sum_bij'
    (i := fun p _ => (p.2, p.1 / p.2))
    (j := fun p _ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ))
  · rintro ⟨n, d⟩ hp
    have hp' : (1 ≤ n ∧ n ≤ N) ∧ d ∈ n.divisors := by
      simpa only [Finset.mem_sigma, Finset.mem_Icc] using hp
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hp'.2
    have hn0 : n ≠ 0 := Nat.ne_of_gt hp'.1.1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
    have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdn
    have hqpos : 1 ≤ n / d := (Nat.one_le_div_iff hdpos).2 hdle
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hdpos, hdle.trans hp'.1.2⟩,
      ⟨hqpos, (Nat.div_le_self n d).trans hp'.1.2⟩⟩,
      by simpa only [Nat.mul_div_cancel' hdn] using hp'.1.2⟩
  · rintro ⟨a, b⟩ hp
    have hp' : ((1 ≤ a ∧ a ≤ N) ∧ (1 ≤ b ∧ b ≤ N)) ∧ a * b ≤ N := by
      simpa only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] using hp
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    exact ⟨⟨Nat.mul_pos hp'.1.1.1 hp'.1.2.1, hp'.2⟩,
      ⟨dvd_mul_right a b, Nat.mul_ne_zero (by omega) (by omega)⟩⟩
  · rintro ⟨n, d⟩ hp
    have hp' : (1 ≤ n ∧ n ≤ N) ∧ d ∈ n.divisors := by
      simpa only [Finset.mem_sigma, Finset.mem_Icc] using hp
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hp'.2
    simp only [Nat.mul_div_cancel' hdn]
  · rintro ⟨a, b⟩ hp
    have hp' : ((1 ≤ a ∧ a ≤ N) ∧ (1 ≤ b ∧ b ≤ N)) ∧ a * b ≤ N := by
      simpa only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] using hp
    have ha0 : 0 < a := hp'.1.1.1
    simp only [Nat.mul_div_cancel_left b ha0]
  · rintro ⟨n, d⟩ _
    rfl

/-- The divisor-weighted Möbius square sum is bounded by the square of its
unweighted reciprocal sum. -/
theorem sum_mobius_sq_card_divisors_div_le_sq (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ)) ≤
      (∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ)) ^ 2 := by
  calc
    (∑ n ∈ Finset.Icc 1 N,
        mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
          (mobiusSqReal d / (d : ℝ)) *
            (mobiusSqReal (n / d) / ((n / d : ℕ) : ℝ)) := by
              apply Finset.sum_le_sum
              intro n hn
              exact mobiusSqReal_card_divisors_div_le_convolution
                (Finset.mem_Icc.mp hn).1
    _ = ∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
          (fun p => p.1 * p.2 ≤ N),
        (mobiusSqReal p.1 / (p.1 : ℝ)) *
          (mobiusSqReal p.2 / (p.2 : ℝ)) :=
      sum_divisor_convolution_eq_sum_factor_pairs
        (fun n => mobiusSqReal n / (n : ℝ)) N
    _ ≤ ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        (mobiusSqReal p.1 / (p.1 : ℝ)) *
          (mobiusSqReal p.2 / (p.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p _ _
      exact mul_nonneg
        (div_nonneg (mobiusSqReal_nonneg p.1) (by positivity))
        (div_nonneg (mobiusSqReal_nonneg p.2) (by positivity))
    _ = (∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ)) ^ 2 := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

/-- Second inequality of Granville--Ramaré Lemma 10.3. -/
theorem sum_mobius_sq_card_divisors_div_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ)) ≤
      (4 / 9 : ℝ) * (Real.log N + 3) ^ 2 := by
  have hsq := sum_mobius_sq_card_divisors_div_le_sq N hN
  have hfirst :
      (∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ)) ≤
        (2 / 3 : ℝ) * (Real.log N + 3) := by
    simpa [mobiusSqReal] using sum_mobius_sq_div_le N hN
  have hleft : 0 ≤ ∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ) :=
    Finset.sum_nonneg fun n _ => div_nonneg (mobiusSqReal_nonneg n) (by positivity)
  have hlog : 0 ≤ Real.log N + 3 := by
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    linarith
  calc
    (∑ n ∈ Finset.Icc 1 N,
        mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ)) ≤
        (∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ)) ^ 2 := hsq
    _ ≤ ((2 / 3 : ℝ) * (Real.log N + 3)) ^ 2 :=
      pow_le_pow_left₀ hleft hfirst 2
    _ = (4 / 9 : ℝ) * (Real.log N + 3) ^ 2 := by ring

/-! ## The least-common-multiple quadratic form -/

/-- Multiples of a squarefree `d` can be divided by `d`; the Möbius function
then leaves precisely the terms coprime to `d`. -/
theorem sum_mobius_multiples_eq_coprime_sum
    {d z : ℕ} (hd : Squarefree d) (hdpos : 1 ≤ d) (hdz : d ≤ z) :
    (∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
        (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ))) =
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)) *
        ∑ c ∈ (Finset.Icc 1 (z / d)).filter (fun c => Nat.Coprime c d),
          (((ArithmeticFunction.moebius c : ℤ) : ℝ) / (c : ℝ)) := by
  classical
  have hsum :
      (∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
          (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ))) =
        ∑ c ∈ Finset.Icc 1 (z / d),
          (((ArithmeticFunction.moebius (d * c) : ℤ) : ℝ) /
            ((d * c : ℕ) : ℝ)) := by
    apply Finset.sum_bij'
      (i := fun b _ => b / d)
      (j := fun c _ => d * c)
    · intro b hb
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      have hdvd := hb.2
      have hd0 : 0 < d := hdpos
      rw [Finset.mem_Icc]
      exact ⟨(Nat.one_le_div_iff hd0).2
          (Nat.le_of_dvd (by omega) hdvd),
        Nat.div_le_div_right hb.1.2⟩
    · intro c hc
      rw [Finset.mem_Icc] at hc
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hdpos hc.1, ?_⟩, dvd_mul_right d c⟩
      have h := (Nat.le_div_iff_mul_le hdpos).1 hc.2
      simpa only [Nat.mul_comm] using h
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact Nat.mul_div_cancel' hb.2
    · intro c hc
      rw [Finset.mem_Icc] at hc
      exact Nat.mul_div_cancel_left c hdpos
    · intro b hb
      rw [Finset.mem_filter] at hb
      rw [Nat.mul_div_cancel' hb.2]
  rw [hsum]
  have hterm : ∀ c ∈ Finset.Icc 1 (z / d),
      (((ArithmeticFunction.moebius (d * c) : ℤ) : ℝ) /
          ((d * c : ℕ) : ℝ)) =
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)) *
          (if Nat.Coprime c d then
            (((ArithmeticFunction.moebius c : ℤ) : ℝ) / (c : ℝ)) else 0) := by
    intro c hc
    by_cases hcd : Nat.Coprime c d
    · rw [if_pos hcd]
      have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcd.symm
      rw [hmul]
      push_cast
      norm_num
      ring
    · rw [if_neg hcd]
      have hnSq : ¬Squarefree (d * c) := by
        intro hs
        exact hcd (Nat.coprime_of_squarefree_mul hs).symm
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnSq]
      norm_num
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_filter]

/-- Absolute-value form of the preceding identity, using Lemma 10.2. -/
theorem abs_sum_mobius_multiples_le
    {d z : ℕ} (hd : Squarefree d) (hdpos : 1 ≤ d) (hdz : d ≤ z) :
    |∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
        (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ))| ≤
      1 / (d : ℝ) := by
  rw [sum_mobius_multiples_eq_coprime_sum hd hdpos hdz, abs_mul]
  have hmu : |(((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ))| =
      1 / (d : ℝ) := by
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ))]
    have hmuZ := ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd
    have hmuR : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
      exact_mod_cast hmuZ
    rw [hmuR]
  rw [hmu]
  have hquot : 1 ≤ z / d := (Nat.one_le_div_iff hdpos).2 hdz
  have hc := abs_coprime_mobius_sum_le_one d (z / d) hquot
  simpa using mul_le_mul_of_nonneg_left hc
    (div_nonneg zero_le_one (Nat.cast_nonneg d))

/-- Expand a gcd by `gcd(a,b)=∑_{d∣gcd(a,b)} φ(d)` and reverse the two
finite sums. -/
theorem sum_mobius_mul_gcd_div_eq
    {a z : ℕ} (ha : 1 ≤ a) :
    (∑ b ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius b : ℤ) : ℝ) * (Nat.gcd a b : ℝ) /
          (b : ℝ)) =
      ∑ d ∈ a.divisors, (Nat.totient d : ℝ) *
        ∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
          (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ)) := by
  classical
  have hterm : ∀ b ∈ Finset.Icc 1 z,
      ((ArithmeticFunction.moebius b : ℤ) : ℝ) * (Nat.gcd a b : ℝ) /
          (b : ℝ) =
        ∑ d ∈ a.divisors,
          if d ∣ b then
            (Nat.totient d : ℝ) *
              (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ))
          else 0 := by
    intro b hb
    have hbpos : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hdivs : (Nat.gcd a b).divisors = a.divisors.filter (fun d => d ∣ b) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hdg, hg0⟩
        have hda : d ∣ a := dvd_trans hdg (Nat.gcd_dvd_left a b)
        have hdb : d ∣ b := dvd_trans hdg (Nat.gcd_dvd_right a b)
        exact ⟨⟨hda, by omega⟩, hdb⟩
      · rintro ⟨⟨hda, ha0⟩, hdb⟩
        exact ⟨Nat.dvd_gcd hda hdb, (Nat.gcd_pos_of_pos_left b ha).ne'⟩
    have hgcd := Nat.sum_totient (Nat.gcd a b)
    calc
      ((ArithmeticFunction.moebius b : ℤ) : ℝ) * (Nat.gcd a b : ℝ) /
          (b : ℝ) =
        (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ)) *
          ((∑ d ∈ (Nat.gcd a b).divisors, Nat.totient d : ℕ) : ℝ) := by
            rw [hgcd]
            ring
      _ = (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ)) *
          ∑ d ∈ a.divisors.filter (fun d => d ∣ b), (Nat.totient d : ℝ) := by
            rw [hdivs]
            push_cast
            rfl
      _ = ∑ d ∈ a.divisors,
          if d ∣ b then
            (Nat.totient d : ℝ) *
              (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ))
          else 0 := by
            rw [Finset.sum_filter, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _
            split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum, Finset.sum_filter]

/-- A squarefree first argument makes the gcd-weighted inner sum at most its
number of divisors. -/
theorem abs_sum_mobius_mul_gcd_div_le
    {a z : ℕ} (ha : Squarefree a) (hapos : 1 ≤ a) (haz : a ≤ z) :
    |∑ b ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius b : ℤ) : ℝ) * (Nat.gcd a b : ℝ) /
          (b : ℝ)| ≤ (a.divisors.card : ℝ) := by
  rw [sum_mobius_mul_gcd_div_eq hapos]
  calc
    |∑ d ∈ a.divisors, (Nat.totient d : ℝ) *
        ∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
          (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ))| ≤
      ∑ d ∈ a.divisors,
        |(Nat.totient d : ℝ) *
          ∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
            (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ a.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hda : d ∣ a := Nat.dvd_of_mem_divisors hd
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hda hapos
      have hdsq : Squarefree d := ha.squarefree_of_dvd hda
      have hdz : d ≤ z := (Nat.le_of_dvd (by omega) hda).trans haz
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        (Nat.totient d : ℝ) *
            |∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
              (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ))| ≤
          (Nat.totient d : ℝ) * (1 / (d : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (abs_sum_mobius_multiples_le hdsq hdpos hdz) (Nat.cast_nonneg _)
        _ ≤ (d : ℝ) * (1 / (d : ℝ)) := by
          gcongr
          exact_mod_cast Nat.totient_le d
        _ = 1 := by field_simp
    _ = (a.divisors.card : ℝ) := by simp

/-- One row of the least-common-multiple quadratic form. -/
theorem abs_sum_mobius_mul_mobius_div_lcm_le
    {a z : ℕ} (hapos : 1 ≤ a) (haz : a ≤ z) :
    |∑ b ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ) /
          (Nat.lcm a b : ℝ)| ≤
      mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ) := by
  classical
  by_cases ha : Squarefree a
  · have hrewrite :
        (∑ b ∈ Finset.Icc 1 z,
            ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
                ((ArithmeticFunction.moebius b : ℤ) : ℝ) /
              (Nat.lcm a b : ℝ)) =
          (((ArithmeticFunction.moebius a : ℤ) : ℝ) / (a : ℝ)) *
            ∑ b ∈ Finset.Icc 1 z,
              ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
                  (Nat.gcd a b : ℝ) / (b : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hbpos : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have haR : (a : ℝ) ≠ 0 := by positivity
      have hbR : (b : ℝ) ≠ 0 := by positivity
      have hgpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b hapos
      have hgR : (Nat.gcd a b : ℝ) ≠ 0 := by positivity
      have hlpos : 0 < Nat.lcm a b := Nat.lcm_pos hapos hbpos
      have hlR : (Nat.lcm a b : ℝ) ≠ 0 := by positivity
      field_simp
      have hgl : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) =
          (a : ℝ) * (b : ℝ) := by exact_mod_cast Nat.gcd_mul_lcm a b
      calc
        ((ArithmeticFunction.moebius b : ℤ) : ℝ) * (a : ℝ) * (b : ℝ) =
            ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
              ((a : ℝ) * (b : ℝ)) := by ring
        _ = ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
              ((Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ)) := by rw [hgl]
        _ = ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
              (Nat.lcm a b : ℝ) * (Nat.gcd a b : ℝ) := by ring
    rw [hrewrite, abs_mul]
    have hmu : |(((ArithmeticFunction.moebius a : ℤ) : ℝ) / (a : ℝ))| =
        1 / (a : ℝ) := by
      rw [abs_div, show |(a : ℝ)| = (a : ℝ) by
        exact abs_of_pos (by exact_mod_cast hapos)]
      have hmuZ := ArithmeticFunction.abs_moebius_eq_one_of_squarefree ha
      have hmuR : |((ArithmeticFunction.moebius a : ℤ) : ℝ)| = 1 := by
        exact_mod_cast hmuZ
      rw [hmuR]
    rw [hmu, mobiusSqReal_eq_one_of_squarefree ha, one_mul]
    have hinner := abs_sum_mobius_mul_gcd_div_le ha hapos haz
    exact (mul_le_mul_of_nonneg_left hinner
      (div_nonneg zero_le_one (Nat.cast_nonneg a))).trans_eq (by ring)
  · rw [mobiusSqReal_eq_zero_of_not_squarefree ha, zero_mul, zero_div]
    have hmu : ArithmeticFunction.moebius a = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree ha
    simp [hmu]

/-- The main lcm quadratic form is controlled by the second estimate of
Lemma 10.3. -/
theorem abs_lcm_mobius_quadratic_le (z : ℕ) (hz : 1 ≤ z) :
    |∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ) /
          (Nat.lcm a b : ℝ)| ≤
      (4 / 9 : ℝ) * (Real.log z + 3) ^ 2 := by
  calc
    |∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ) /
          (Nat.lcm a b : ℝ)| ≤
      ∑ a ∈ Finset.Icc 1 z,
        |∑ b ∈ Finset.Icc 1 z,
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
              ((ArithmeticFunction.moebius b : ℤ) : ℝ) /
            (Nat.lcm a b : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 z,
        mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact abs_sum_mobius_mul_mobius_div_lcm_le
        (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2
    _ ≤ (4 / 9 : ℝ) * (Real.log z + 3) ^ 2 :=
      sum_mobius_sq_card_divisors_div_le z hz

/-! ## Counting multiples in `(N,2N]` -/

def intervalMultipleCount (N q : ℕ) : ℕ :=
  ((Finset.Ioc N (2 * N)).filter fun n => q ∣ n).card

theorem intervalMultipleCount_eq (N q : ℕ) :
    intervalMultipleCount N q = (2 * N) / q - N / q := by
  classical
  let A := (Finset.Ioc 0 N).filter fun n => q ∣ n
  let B := (Finset.Ioc N (2 * N)).filter fun n => q ∣ n
  let C := (Finset.Ioc 0 (2 * N)).filter fun n => q ∣ n
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro n hnA hnB
    simp only [A, B, Finset.mem_filter, Finset.mem_Ioc] at hnA hnB
    omega
  have hunion : A ∪ B = C := by
    ext n
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro (h | h)
      · exact ⟨⟨h.1.1, by omega⟩, h.2⟩
      · exact ⟨⟨by omega, h.1.2⟩, h.2⟩
    · rintro ⟨hn, hq⟩
      by_cases hle : n ≤ N
      · exact Or.inl ⟨⟨hn.1, hle⟩, hq⟩
      · exact Or.inr ⟨⟨by omega, hn.2⟩, hq⟩
  have hA : A.card = N / q := by
    simpa only [A] using Nat.Ioc_filter_dvd_card_eq_div N q
  have hC : C.card = (2 * N) / q := by
    simpa only [C] using Nat.Ioc_filter_dvd_card_eq_div (2 * N) q
  have hcard : A.card + B.card = C.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdis]
  have hB : B.card = (2 * N) / q - N / q := by omega
  simpa only [B, intervalMultipleCount] using hB

/-- The count of multiples in `(N,2N]` differs from `N/q` by at most one. -/
theorem abs_intervalMultipleCount_sub_le_one
    {N q : ℕ} (hq : 1 ≤ q) :
    |(intervalMultipleCount N q : ℝ) - (N : ℝ) / (q : ℝ)| ≤ 1 := by
  rw [intervalMultipleCount_eq]
  let A := N / q
  let r := N % q
  have hdecomp : N = A * q + r := by
    dsimp [A, r]
    exact (Nat.div_add_mod' N q).symm
  have hr : r < q := Nat.mod_lt N hq
  have hdouble : (2 * N) / q = 2 * A + (2 * r) / q := by
    have hn : 2 * N = 2 * r + q * (2 * A) := by
      rw [hdecomp]
      ring
    rw [hn, Nat.add_mul_div_left (2 * r) (2 * A) hq]
    omega
  have hrem : (2 * r) / q ≤ 1 := by
    have : (2 * r) / q < 2 := (Nat.div_lt_iff_lt_mul hq).2 (by omega)
    omega
  have hnat : (2 * N) / q - N / q = A + (2 * r) / q := by
    change (2 * N) / q - A = A + (2 * r) / q
    rw [hdouble]
    simp [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hnat]
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hreal : (N : ℝ) / (q : ℝ) = (A : ℝ) + (r : ℝ) / (q : ℝ) := by
    rw [div_eq_iff (ne_of_gt hqR)]
    rw [hdecomp]
    push_cast
    field_simp
  rw [hreal]
  have hr0 : (0 : ℝ) ≤ (r : ℝ) / (q : ℝ) := by positivity
  have hr1 : (r : ℝ) / (q : ℝ) ≤ 1 := by
    rw [div_le_one hqR]
    exact_mod_cast hr.le
  have ht0 : (0 : ℝ) ≤ (((2 * r) / q : ℕ) : ℝ) := by positivity
  have ht1 : (((2 * r) / q : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hrem
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-! ## The rounding-error pairs -/

/-

noncomputable def squarefreeLcmPairs (z X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 z).product (Finset.Icc 1 z)).filter fun p =>
    Squarefree p.1 ∧ Squarefree p.2 ∧ Nat.lcm p.1 p.2 ≤ X

noncomputable def squarefreeFactorTriples (z X : ℕ) :
    Finset (Σ _r : ℕ, Σ _s : ℕ, ℕ) :=
  ((Finset.Icc 1 z).filter Squarefree).sigma fun r =>
    ((Finset.Icc 1 z).filter Squarefree).sigma fun s =>
      Finset.Icc 1 (X / (r * s))

theorem card_squarefreeLcmPairs_le_factorTriples (z X : ℕ) :
    (squarefreeLcmPairs z X).card ≤ (squarefreeFactorTriples z X).card := by
  classical
  let enc : ℕ × ℕ → (Σ _r : ℕ, Σ _s : ℕ, ℕ) := fun p =>
    ⟨p.1 / Nat.gcd p.1 p.2, ⟨p.2 / Nat.gcd p.1 p.2, Nat.gcd p.1 p.2⟩⟩
  refine Finset.card_le_card_of_injOn enc ?_ ?_
  · rintro ⟨a, b⟩ hp
    change (a, b) ∈ squarefreeLcmPairs z X at hp
    rw [squarefreeLcmPairs] at hp
    have hpf := Finset.mem_filter.mp hp
    have hpp := Finset.mem_product.mp hpf.1
    rw [Finset.mem_Icc] at hpp
    obtain ⟨⟨ha1, haz⟩, hb1, hbz⟩ := hpp
    obtain ⟨hsa, hsb, hl⟩ := hpf.2
    let g := Nat.gcd a b
    have hgpos : 1 ≤ g := Nat.gcd_pos_of_pos_left b ha1
    have hga : g ∣ a := Nat.gcd_dvd_left a b
    have hgb : g ∣ b := Nat.gcd_dvd_right a b
    have hra1 : 1 ≤ a / g :=
      (Nat.one_le_div_iff hgpos).2 (Nat.le_of_dvd (by omega) hga)
    have hrs1 : 1 ≤ b / g :=
      (Nat.one_le_div_iff hgpos).2 (Nat.le_of_dvd (by omega) hgb)
    have hraz : a / g ≤ z := (Nat.div_le_self _ _).trans haz
    have hrsz : b / g ≤ z := (Nat.div_le_self _ _).trans hbz
    have hrdiv : a / g ∣ a :=
      ⟨g, by simpa [Nat.mul_comm] using (Nat.div_mul_cancel hga).symm⟩
    have hsdiv : b / g ∣ b :=
      ⟨g, by simpa [Nat.mul_comm] using (Nat.div_mul_cancel hgb).symm⟩
    have hsqr : Squarefree (a / g) := hsa.squarefree_of_dvd hrdiv
    have hsqs : Squarefree (b / g) := hsb.squarefree_of_dvd hsdiv
    have hlcmform : Nat.lcm a b = g * (a / g * (b / g)) := by
      apply Nat.eq_of_mul_eq_mul_left hgpos
      rw [Nat.gcd_mul_lcm]
      dsimp only [g]
      rw [Nat.div_mul_cancel hga, Nat.div_mul_cancel hgb]
      ring
    have hprodpos : 0 < a / g * (b / g) := Nat.mul_pos hra1 hrs1
    have hgle : g ≤ X / (a / g * (b / g)) := by
      rw [Nat.le_div_iff_mul_le hprodpos]
      simpa [hlcmform, Nat.mul_assoc] using hl
    change enc (a, b) ∈ squarefreeFactorTriples z X
    simp only [enc, squarefreeFactorTriples, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_Icc]
    exact ⟨⟨⟨hra1, hraz⟩, hsqr⟩, ⟨⟨⟨hrs1, hrsz⟩, hsqs⟩, hgpos, hgle⟩⟩
  · intro p hp q hq heq
    have hpa : Nat.gcd p.1 p.2 ∣ p.1 := Nat.gcd_dvd_left _ _
    have hpb : Nat.gcd p.1 p.2 ∣ p.2 := Nat.gcd_dvd_right _ _
    have hqa : Nat.gcd q.1 q.2 ∣ q.1 := Nat.gcd_dvd_left _ _
    have hqb : Nat.gcd q.1 q.2 ∣ q.2 := Nat.gcd_dvd_right _ _
    have hr := congrArg (fun t => t.1) heq
    have hs := congrArg (fun t => t.2.1) heq
    have hg := congrArg (fun t => t.2.2) heq
    dsimp only [enc] at hr hs hg
    apply Prod.ext
    · calc
        p.1 = p.1 / Nat.gcd p.1 p.2 * Nat.gcd p.1 p.2 :=
          (Nat.div_mul_cancel hpa).symm
        _ = q.1 / Nat.gcd q.1 q.2 * Nat.gcd q.1 q.2 := by rw [hr, hg]
        _ = q.1 := Nat.div_mul_cancel hqa
    · calc
        p.2 = p.2 / Nat.gcd p.1 p.2 * Nat.gcd p.1 p.2 :=
          (Nat.div_mul_cancel hpb).symm
        _ = q.2 / Nat.gcd q.1 q.2 * Nat.gcd q.1 q.2 := by rw [hs, hg]
        _ = q.2 := Nat.div_mul_cancel hqb

theorem card_squarefreeFactorTriples_le (z X : ℕ) :
    ((squarefreeFactorTriples z X).card : ℝ) ≤
      (X : ℝ) *
        (∑ n ∈ Finset.Icc 1 z, mobiusSqReal n / (n : ℝ)) ^ 2 := by
  classical
  let S := (Finset.Icc 1 z).filter Squarefree
  have hsum : (∑ n ∈ S, (1 : ℝ) / (n : ℝ)) =
      ∑ n ∈ Finset.Icc 1 z, mobiusSqReal n / (n : ℝ) := by
    rw [show S = (Finset.Icc 1 z).filter Squarefree by rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs : Squarefree n
    · rw [if_pos hs, mobiusSqReal_eq_one_of_squarefree hs]
    · rw [if_neg hs, mobiusSqReal_eq_zero_of_not_squarefree hs, zero_div]
  simp only [squarefreeFactorTriples, Finset.card_sigma]
  push_cast
  change (∑ r ∈ S, (∑ s ∈ S, ((Finset.Icc 1 (X / (r * s))).card : ℝ))) ≤ _
  calc
    (∑ r ∈ S, (∑ s ∈ S, ((Finset.Icc 1 (X / (r * s))).card : ℝ))) ≤
        ∑ r ∈ S, ∑ s ∈ S, (X : ℝ) / ((r : ℝ) * (s : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      rw [Nat.card_Icc, Nat.add_sub_cancel]
      simpa only [Nat.cast_mul] using
        (Nat.cast_div_le : (((X / (r * s) : ℕ) : ℝ) ≤
          (X : ℝ) / ((r * s : ℕ) : ℝ)))
    _ = (X : ℝ) * (∑ n ∈ S, (1 : ℝ) / (n : ℝ)) ^ 2 := by
      have hinner : ∀ r ∈ S,
          (∑ s ∈ S, (X : ℝ) / ((r : ℝ) * (s : ℝ))) =
            ((X : ℝ) / (r : ℝ)) * ∑ s ∈ S, (1 : ℝ) / (s : ℝ) := by
        intro r hr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      rw [Finset.sum_congr rfl hinner, Finset.sum_mul]
      have hx : (∑ r ∈ S, (X : ℝ) / (r : ℝ)) =
          (X : ℝ) * ∑ r ∈ S, (1 : ℝ) / (r : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      rw [hx, pow_two]
      ring
    _ = (X : ℝ) *
        (∑ n ∈ Finset.Icc 1 z, mobiusSqReal n / (n : ℝ)) ^ 2 := by rw [hsum]
-/

/-! ## A positive quadratic-form bound -/

/-- Reindex a sum over multiples by dividing out the fixed divisor. -/
theorem sum_multiples_eq_sum_mul (f : ℕ → ℝ) {d z : ℕ}
    (hdpos : 1 ≤ d) :
    (∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b), f b) =
      ∑ c ∈ Finset.Icc 1 (z / d), f (d * c) := by
  classical
  apply Finset.sum_bij'
    (i := fun b _ => b / d)
    (j := fun c _ => d * c)
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hdpos).2
        (Nat.le_of_dvd (by omega) hb.2), Nat.div_le_div_right hb.1.2⟩
  · intro c hc
    rw [Finset.mem_Icc] at hc
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos hdpos hc.1, ?_⟩, dvd_mul_right d c⟩
    have h := (Nat.le_div_iff_mul_le hdpos).1 hc.2
    simpa only [Nat.mul_comm] using h
  · intro b hb
    rw [Finset.mem_filter] at hb
    exact Nat.mul_div_cancel' hb.2
  · intro c hc
    exact Nat.mul_div_cancel_left c hdpos
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [Nat.mul_div_cancel' hb.2]

/-- Removing a fixed factor can only increase the squarefree indicator. -/
theorem mobiusSqReal_mul_le_right (d c : ℕ) :
    mobiusSqReal (d * c) ≤ mobiusSqReal c := by
  by_cases h : Squarefree (d * c)
  · have hc : Squarefree c := h.squarefree_of_dvd (dvd_mul_left c d)
    rw [mobiusSqReal_eq_one_of_squarefree h,
      mobiusSqReal_eq_one_of_squarefree hc]
  · rw [mobiusSqReal_eq_zero_of_not_squarefree h]
    exact mobiusSqReal_nonneg c

/-- A positive squarefree reciprocal sum over multiples. -/
theorem sum_mobiusSqReal_multiples_le {d z : ℕ}
    (hdpos : 1 ≤ d) (hdz : d ≤ z) :
    (∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
        mobiusSqReal b / (b : ℝ)) ≤
      (1 / (d : ℝ)) * ((2 / 3 : ℝ) * (Real.log z + 3)) := by
  rw [sum_multiples_eq_sum_mul
    (fun b => mobiusSqReal b / (b : ℝ)) hdpos]
  calc
    (∑ c ∈ Finset.Icc 1 (z / d),
        mobiusSqReal (d * c) / ((d * c : ℕ) : ℝ)) ≤
      (1 / (d : ℝ)) *
        ∑ c ∈ Finset.Icc 1 (z / d), mobiusSqReal c / (c : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c hc
      have hcpos : 1 ≤ c := (Finset.mem_Icc.mp hc).1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
      push_cast
      calc
        mobiusSqReal (d * c) / ((d : ℝ) * (c : ℝ)) ≤
            mobiusSqReal c / ((d : ℝ) * (c : ℝ)) := by
          gcongr
          exact mobiusSqReal_mul_le_right d c
        _ = (1 / (d : ℝ)) * (mobiusSqReal c / (c : ℝ)) := by ring
    _ ≤ (1 / (d : ℝ)) *
        ((2 / 3 : ℝ) * (Real.log ((z / d : ℕ) : ℝ) + 3)) := by
      gcongr
      have hquot : 1 ≤ z / d := (Nat.one_le_div_iff hdpos).2 hdz
      simpa [mobiusSqReal] using sum_mobius_sq_div_le (z / d) hquot
    _ ≤ (1 / (d : ℝ)) * ((2 / 3 : ℝ) * (Real.log z + 3)) := by
      have hquot : 1 ≤ z / d := (Nat.one_le_div_iff hdpos).2 hdz
      have hzpos : 1 ≤ z := hdpos.trans hdz
      have hle : ((z / d : ℕ) : ℝ) ≤ (z : ℝ) := by
        exact_mod_cast Nat.div_le_self z d
      have hqR : (0 : ℝ) < ((z / d : ℕ) : ℝ) := by exact_mod_cast hquot
      have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hzpos
      have hlog : Real.log ((z / d : ℕ) : ℝ) ≤ Real.log (z : ℝ) :=
        Real.strictMonoOn_log.monotoneOn hqR hzR hle
      have hadd : Real.log ((z / d : ℕ) : ℝ) + 3 ≤ Real.log (z : ℝ) + 3 := by
        linarith
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hadd (by norm_num))
        (by positivity)

/-- The gcd expansion, for an arbitrary real coefficient sequence. -/
theorem sum_mul_gcd_div_eq_general (f : ℕ → ℝ) {a z : ℕ} (ha : 1 ≤ a) :
    (∑ b ∈ Finset.Icc 1 z, f b * (Nat.gcd a b : ℝ) / (b : ℝ)) =
      ∑ d ∈ a.divisors, (Nat.totient d : ℝ) *
        ∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b), f b / (b : ℝ) := by
  classical
  have hterm : ∀ b ∈ Finset.Icc 1 z,
      f b * (Nat.gcd a b : ℝ) / (b : ℝ) =
        ∑ d ∈ a.divisors,
          if d ∣ b then (Nat.totient d : ℝ) * (f b / (b : ℝ)) else 0 := by
    intro b hb
    have hdivs : (Nat.gcd a b).divisors =
        a.divisors.filter (fun d => d ∣ b) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hdg, hg0⟩
        exact ⟨⟨dvd_trans hdg (Nat.gcd_dvd_left a b), by omega⟩,
          dvd_trans hdg (Nat.gcd_dvd_right a b)⟩
      · rintro ⟨⟨hda, ha0⟩, hdb⟩
        exact ⟨Nat.dvd_gcd hda hdb, (Nat.gcd_pos_of_pos_left b ha).ne'⟩
    have hgcd := Nat.sum_totient (Nat.gcd a b)
    calc
      f b * (Nat.gcd a b : ℝ) / (b : ℝ) =
          (f b / (b : ℝ)) *
            ((∑ d ∈ (Nat.gcd a b).divisors, Nat.totient d : ℕ) : ℝ) := by
        rw [hgcd]
        ring
      _ = (f b / (b : ℝ)) *
          ∑ d ∈ a.divisors.filter (fun d => d ∣ b), (Nat.totient d : ℝ) := by
        rw [hdivs]
        push_cast
        rfl
      _ = ∑ d ∈ a.divisors,
          if d ∣ b then (Nat.totient d : ℝ) * (f b / (b : ℝ)) else 0 := by
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum, Finset.sum_filter]

/-- A row of the positive lcm form. -/
theorem sum_mobiusSqReal_gcd_div_le {a z : ℕ}
    (ha : Squarefree a) (hapos : 1 ≤ a) (haz : a ≤ z) :
    (∑ b ∈ Finset.Icc 1 z,
        mobiusSqReal b * (Nat.gcd a b : ℝ) / (b : ℝ)) ≤
      (a.divisors.card : ℝ) * ((2 / 3 : ℝ) * (Real.log z + 3)) := by
  rw [sum_mul_gcd_div_eq_general mobiusSqReal hapos]
  calc
    (∑ d ∈ a.divisors, (Nat.totient d : ℝ) *
        ∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
          mobiusSqReal b / (b : ℝ)) ≤
      ∑ _d ∈ a.divisors, ((2 / 3 : ℝ) * (Real.log z + 3)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hda : d ∣ a := Nat.dvd_of_mem_divisors hd
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hda hapos
      have hdz : d ≤ z := (Nat.le_of_dvd (by omega) hda).trans haz
      calc
        (Nat.totient d : ℝ) *
            ∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
              mobiusSqReal b / (b : ℝ) ≤
          (Nat.totient d : ℝ) *
            ((1 / (d : ℝ)) * ((2 / 3 : ℝ) * (Real.log z + 3))) := by
          gcongr
          exact sum_mobiusSqReal_multiples_le hdpos hdz
        _ ≤ (d : ℝ) *
            ((1 / (d : ℝ)) * ((2 / 3 : ℝ) * (Real.log z + 3))) := by
          gcongr
          exact_mod_cast Nat.totient_le d
        _ = (2 / 3 : ℝ) * (Real.log z + 3) := by
          have : (d : ℝ) ≠ 0 := by positivity
          field_simp
    _ = (a.divisors.card : ℝ) *
        ((2 / 3 : ℝ) * (Real.log z + 3)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- A row of the positive least-common-multiple quadratic form. -/
theorem sum_mobiusSqReal_lcm_row_le {a z : ℕ}
    (hapos : 1 ≤ a) (haz : a ≤ z) :
    (∑ b ∈ Finset.Icc 1 z,
        mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) ≤
      (mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ)) *
        ((2 / 3 : ℝ) * (Real.log z + 3)) := by
  by_cases ha : Squarefree a
  · have hrewrite :
        (∑ b ∈ Finset.Icc 1 z,
            mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) =
          (mobiusSqReal a / (a : ℝ)) *
            ∑ b ∈ Finset.Icc 1 z,
              mobiusSqReal b * (Nat.gcd a b : ℝ) / (b : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hbpos : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have hgl : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) =
          (a : ℝ) * (b : ℝ) := by exact_mod_cast Nat.gcd_mul_lcm a b
      have haR : (a : ℝ) ≠ 0 := by positivity
      have hbR : (b : ℝ) ≠ 0 := by positivity
      have hlR : (Nat.lcm a b : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.lcm_pos hapos hbpos).ne'
      field_simp
      calc
        mobiusSqReal a * mobiusSqReal b * (a : ℝ) * (b : ℝ) =
            mobiusSqReal a * mobiusSqReal b * ((a : ℝ) * (b : ℝ)) := by ring
        _ =
            mobiusSqReal a * mobiusSqReal b *
              ((Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ)) := by rw [hgl]
        _ = mobiusSqReal a * mobiusSqReal b * (Nat.lcm a b : ℝ) *
              (Nat.gcd a b : ℝ) := by ring
    rw [hrewrite]
    have hinner := sum_mobiusSqReal_gcd_div_le ha hapos haz
    calc
      (mobiusSqReal a / (a : ℝ)) *
          ∑ b ∈ Finset.Icc 1 z,
            mobiusSqReal b * (Nat.gcd a b : ℝ) / (b : ℝ) ≤
        (mobiusSqReal a / (a : ℝ)) *
          ((a.divisors.card : ℝ) * ((2 / 3 : ℝ) * (Real.log z + 3))) := by
        gcongr
        exact div_nonneg (mobiusSqReal_nonneg a) (Nat.cast_nonneg a)
      _ = (mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ)) *
          ((2 / 3 : ℝ) * (Real.log z + 3)) := by ring
  · rw [mobiusSqReal_eq_zero_of_not_squarefree ha]
    simp

/-- The positive lcm form costs one additional logarithm. -/
theorem sum_mobiusSqReal_lcm_le (z : ℕ) (hz : 1 ≤ z) :
    (∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) ≤
      (8 / 27 : ℝ) * (Real.log z + 3) ^ 3 := by
  let C : ℝ := (2 / 3 : ℝ) * (Real.log z + 3)
  calc
    (∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) ≤
      ∑ a ∈ Finset.Icc 1 z,
        (mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ)) * C := by
      apply Finset.sum_le_sum
      intro a ha
      exact sum_mobiusSqReal_lcm_row_le
        (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2
    _ = (∑ a ∈ Finset.Icc 1 z,
        mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ)) * C := by
      rw [Finset.sum_mul]
    _ ≤ ((4 / 9 : ℝ) * (Real.log z + 3) ^ 2) * C := by
      gcongr
      exact sum_mobius_sq_card_divisors_div_le z hz
    _ = (8 / 27 : ℝ) * (Real.log z + 3) ^ 3 := by
      dsimp [C]
      ring

end Erdos175
