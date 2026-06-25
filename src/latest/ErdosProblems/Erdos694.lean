/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 694.
https://www.erdosproblems.com/forum/thread/694

Formalization status:
- Conditional on: mertens_product
- Conditional on: linnik_dvd

Informal authors:
- GPT-5.5 Pro
- Liam Price

Formal authors:
- Claude Code 4.7
- GPT-5.5 Pro
- Pawan Sasanka Ammanamanchi

URLs:
- https://www.erdosproblems.com/forum/thread/694#post-6202
- https://www.overleaf.com/read/fgmhvywvdjkt#54ca5d
- https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P694/Proof.lean
- https://raw.githubusercontent.com/Shashi456/erdos-formalizations/refs/heads/main/Erdos/P694/Proof.lean
-/
/-
STANDALONE VERSION of Erdős Problem #694 — TOTIENT FIBRE EXTREMES.

Trust boundary:
  Mathlib core (propext, Classical.choice, Quot.sound)
  + mertens_product       (Mertens' product theorem, shared trusted input)
  + linnik_dvd            (Linnik's theorem, divisibility form, shared trusted input)

Both trusted inputs are classical unconditional theorems (Mertens 1874, Linnik 1944);
Mathlib v4.27/v4.28 has surrounding infrastructure but not these named statements.
-/

import Mathlib
import ErdosProblems.Axioms

namespace Erdos694

open Filter Asymptotics Topology
open scoped BigOperators Nat

/-! ## Scratch helpers (totient ratio bookkeeping) -/

lemma ratio_totient_eq_prod_primeFactors_q (m : ℕ) (hm : m ≠ 0) :
    (m : ℚ) / Nat.totient m =
      ∏ p ∈ m.primeFactors, ((p : ℚ) / (p - 1)) := by
  have hφ : (Nat.totient m : ℚ) =
      (m : ℚ) * ∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors m
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hprod_nonzero :
      (∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpne1 : (p : ℚ) ≠ 1 := by
      norm_num [hpprime.ne_one]
    have hpne0 : (p : ℚ) ≠ 0 := by
      norm_num [hpprime.ne_zero]
    have hrewrite : (1 - (p : ℚ)⁻¹) = ((p : ℚ) - 1) / p := by
      field_simp [hpne0]
    rw [hrewrite]
    exact div_ne_zero (sub_ne_zero.mpr hpne1) hpne0
  have hφne : (Nat.totient m : ℚ) ≠ 0 := by
    rw [hφ]
    exact mul_ne_zero hmQ hprod_nonzero
  calc
    (m : ℚ) / Nat.totient m
        = (∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹))⁻¹ := by
          rw [hφ]
          field_simp [hmQ, hprod_nonzero]
    _ = ∏ p ∈ m.primeFactors, ((p : ℚ) / (p - 1)) := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpne0 : (p : ℚ) ≠ 0 := by
        norm_num [hpprime.ne_zero]
      have hpne1 : (p : ℚ) ≠ 1 := by
        norm_num [hpprime.ne_one]
      field_simp [hpne0, hpne1]

lemma ratio_totient_eq_prod_primeFactors_real (m : ℕ) (hm : m ≠ 0) :
    (m : ℝ) / Nat.totient m =
      ∏ p ∈ m.primeFactors, ((p : ℝ) / (p - 1)) := by
  have hq := congrArg (fun q : ℚ => (q : ℝ)) (ratio_totient_eq_prod_primeFactors_q m hm)
  simpa [Rat.cast_prod] using hq

noncomputable def primeEulerProdNat (Y : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, ((p : ℝ) / (p - 1))

lemma one_le_prime_factor (p : ℕ) (hp : Nat.Prime p) :
    1 ≤ (p : ℝ) / (p - 1) := by
  have hden : 0 < (p : ℝ) - 1 := by
    norm_num [hp.one_lt]
  rw [one_le_div hden]
  norm_num

lemma prime_factor_le_succ_div_self {Y p : ℕ} (hY : 1 ≤ Y) (hp : Nat.Prime p) (hYp : Y < p) :
    (p : ℝ) / (p - 1) ≤ ((Y + 1 : ℕ) : ℝ) / Y := by
  have hpden : 0 < (p : ℝ) - 1 := by
    norm_num [hp.one_lt]
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  rw [div_le_div_iff₀ hpden hYpos]
  have hle : (Y + 1 : ℝ) ≤ p := by exact_mod_cast hYp
  norm_num at hle ⊢
  nlinarith

lemma ratio_totient_le_split_bound (m Y : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y) :
    (m : ℝ) / Nat.totient m ≤
      primeEulerProdNat Y * (((Y + 1 : ℕ) : ℝ) / Y) ^
        (m.primeFactors.filter fun p => Y < p).card := by
  classical
  set S := m.primeFactors with hS
  set small := S.filter (fun p => p ≤ Y) with hsmall
  set large := S.filter (fun p => ¬ p ≤ Y) with hlarge
  have hsplit :
      (∏ p ∈ S, ((p : ℝ) / (p - 1))) =
        (∏ p ∈ small, ((p : ℝ) / (p - 1))) *
          (∏ p ∈ large, ((p : ℝ) / (p - 1))) := by
    rw [hsmall, hlarge]
    exact (Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ Y)
      (fun p => ((p : ℝ) / (p - 1)))).symm
  have hsmall_subset : small ⊆ (Finset.Icc 1 Y).filter Nat.Prime := by
    intro p hp
    rw [hsmall] at hp
    rcases Finset.mem_filter.mp hp with ⟨hpS, hpY⟩
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpprime.one_le, hpY⟩, hpprime⟩
  have hsmall_le :
      (∏ p ∈ small, ((p : ℝ) / (p - 1))) ≤ primeEulerProdNat Y := by
    unfold primeEulerProdNat
    let all := (Finset.Icc 1 Y).filter Nat.Prime
    have hnonneg_small : 0 ≤ ∏ p ∈ small, ((p : ℝ) / (p - 1)) := by
      refine Finset.prod_nonneg ?_
      intro p hp
      have hpS : p ∈ S := by
        rw [hsmall] at hp
        exact (Finset.mem_filter.mp hp).1
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
      exact zero_le_one.trans (one_le_prime_factor p hpprime)
    have hone_rest : 1 ≤ ∏ p ∈ all \ small, ((p : ℝ) / (p - 1)) := by
      have aux : ∀ t : Finset ℕ, t ⊆ all \ small →
          1 ≤ ∏ p ∈ t, ((p : ℝ) / (p - 1)) := by
        intro t ht
        induction t using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.prod_insert ha]
            have ha_mem : a ∈ all \ small := ht (Finset.mem_insert_self a s)
            have hs_sub : s ⊆ all \ small := fun x hx => ht (Finset.mem_insert_of_mem hx)
            exact one_le_mul_of_one_le_of_one_le
              (one_le_prime_factor a (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha_mem).1).2)
              (ih hs_sub)
      exact aux (all \ small) (fun _ h => h)
    calc
      (∏ p ∈ small, ((p : ℝ) / (p - 1)))
          ≤ (∏ p ∈ small, ((p : ℝ) / (p - 1))) *
              ∏ p ∈ all \ small, ((p : ℝ) / (p - 1)) := by
            exact le_mul_of_one_le_right hnonneg_small hone_rest
      _ = ∏ p ∈ all, ((p : ℝ) / (p - 1)) := by
            rw [mul_comm, Finset.prod_sdiff hsmall_subset]
  have hlarge_le :
      (∏ p ∈ large, ((p : ℝ) / (p - 1))) ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^ large.card := by
    calc
      (∏ p ∈ large, ((p : ℝ) / (p - 1)))
          ≤ ∏ _p ∈ large, (((Y + 1 : ℕ) : ℝ) / Y) := by
            refine Finset.prod_le_prod ?nonneg ?le
            · intro p hp
              have hpS : p ∈ S := by
                rw [hlarge] at hp
                exact (Finset.mem_filter.mp hp).1
              have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
              exact zero_le_one.trans (one_le_prime_factor p hpprime)
            · intro p hp
              rw [hlarge] at hp
              rcases Finset.mem_filter.mp hp with ⟨hpS, hpYp⟩
              have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
              exact prime_factor_le_succ_div_self hY hpprime (Nat.lt_of_not_ge hpYp)
      _ = (((Y + 1 : ℕ) : ℝ) / Y) ^ large.card := by
        rw [Finset.prod_const]
  rw [ratio_totient_eq_prod_primeFactors_real m hm, hS, hsplit]
  have hlarge_le' :
      (∏ p ∈ large, ((p : ℝ) / (p - 1))) ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^
          (m.primeFactors.filter fun p => Y < p).card := by
    simpa [hlarge, hS, not_le] using hlarge_le
  exact mul_le_mul hsmall_le hlarge_le'
    (Finset.prod_nonneg fun p hp => by
      have hpS : p ∈ S := by
        rw [hlarge] at hp
        exact (Finset.mem_filter.mp hp).1
      have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (by simpa [hS] using hpS)
      exact zero_le_one.trans (one_le_prime_factor p hpprime))
    (by
      unfold primeEulerProdNat
      exact Finset.prod_nonneg fun p hp => by
        exact zero_le_one.trans (one_le_prime_factor p (Finset.mem_filter.mp hp).2))

lemma large_primeFactors_card_le_log (m Y : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y) :
    ((m.primeFactors.filter fun p => Y < p).card : ℝ) ≤
      Real.log m / Real.log (Y + 1) := by
  classical
  set L := m.primeFactors.filter fun p => Y < p with hL
  have hL_subset : L ⊆ m.primeFactors := by
    rw [hL]
    exact Finset.filter_subset _ _
  have hpow_le_prod : (Y + 1) ^ L.card ≤ ∏ p ∈ L, p := by
    calc
      (Y + 1) ^ L.card = ∏ _p ∈ L, (Y + 1) := by
        rw [Finset.prod_const]
      _ ≤ ∏ p ∈ L, p := by
        refine Finset.prod_le_prod ?nonneg ?le
        · intro p hp
          exact Nat.zero_le (Y + 1)
        · intro p hp
          have hpY : Y < p := by
            rw [hL] at hp
            exact (Finset.mem_filter.mp hp).2
          exact Nat.succ_le_of_lt hpY
  have hprod_le_all : (∏ p ∈ L, p) ≤ ∏ p ∈ m.primeFactors, p := by
    refine Finset.prod_le_prod_of_subset_of_one_le' hL_subset ?_
    intro p hpall hpnot
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hpall
    exact hpprime.one_le
  have hprod_all_le_m : (∏ p ∈ m.primeFactors, p) ≤ m := by
    exact Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hm) (Nat.prod_primeFactors_dvd m)
  have hpow_le_m : (Y + 1) ^ L.card ≤ m :=
    hpow_le_prod.trans (hprod_le_all.trans hprod_all_le_m)
  have hbase_gt_one : (1 : ℝ) < (Y + 1 : ℕ) := by
    norm_num
    exact Nat.succ_le_iff.mp hY
  have hlog_pos : 0 < Real.log ((Y + 1 : ℕ) : ℝ) := Real.log_pos hbase_gt_one
  have hpow_pos : 0 < (((Y + 1) ^ L.card : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (Nat.succ_pos Y) L.card
  have hm_pos_real : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr hm
  have hlog_le :
      Real.log (((Y + 1) ^ L.card : ℕ) : ℝ) ≤ Real.log (m : ℝ) := by
    exact Real.log_le_log hpow_pos (by exact_mod_cast hpow_le_m)
  have hlog_pow :
      Real.log (((Y + 1) ^ L.card : ℕ) : ℝ) =
        (L.card : ℝ) * Real.log ((Y + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hL]
  rw [hlog_pow] at hlog_le
  simpa [Nat.cast_add, Nat.cast_one] using (le_div_iff₀ hlog_pos).mpr hlog_le

lemma ratio_totient_le_log_split_bound (m Y : ℕ) (hm : m ≠ 0) (hY : 1 ≤ Y) :
    (m : ℝ) / Nat.totient m ≤
      primeEulerProdNat Y *
        ((((Y + 1 : ℕ) : ℝ) / Y) ^ (Real.log m / Real.log (Y + 1))) := by
  have hsplit := ratio_totient_le_split_bound m Y hm hY
  have hcard := large_primeFactors_card_le_log m Y hm hY
  have hbase_ge_one : 1 ≤ (((Y + 1 : ℕ) : ℝ) / Y) := by
    have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
    rw [one_le_div hYpos]
    norm_num
  have hpow_le :
      (((Y + 1 : ℕ) : ℝ) / Y) ^
          (m.primeFactors.filter fun p => Y < p).card ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^ (Real.log m / Real.log (Y + 1)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase_ge_one hcard
  exact hsplit.trans (mul_le_mul_of_nonneg_left hpow_le (by
    unfold primeEulerProdNat
    exact Finset.prod_nonneg fun p hp => by
      exact zero_le_one.trans (one_le_prime_factor p (Finset.mem_filter.mp hp).2)))

/-! ## Main proof body -/

/- ## Section 1 — Preliminaries -/

/-- **Fibre-finiteness inequality.** For every `m ≥ 1`, `m ≤ 2 · φ(m)²`.
This gives the bound `m ≤ 2 n²` whenever `φ(m) = n`, ensuring totient fibres are finite.

Proof strategy (PDF Section 1):
- Per prime power `p^k`: `φ(p^k)² = p^(2k-2)(p-1)² ≥ p^k` for odd `p`, and
  `φ(2^k)² = 2^(2k-2) ≥ 2^(k-1)` for `p = 2`.
- Multiplicatively (using `Nat.recOnPosPrimePosCoprime`): the global `2` accounts for
  the at-most-one-factor-of-2 in `m`. The coprime step uses the strengthened
  invariant `if Odd m then m ≤ φ(m)² else m ≤ 2 φ(m)²` — i.e., the factor-of-2
  appears only when `m` is even, and disappears under multiplication of two odd numbers. -/
private lemma totient_sq_ge_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp_odd : Odd p) (hk : 0 < k) :
    p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
  -- Now k = j + 1
  rw [Nat.totient_prime_pow_succ hp]
  have hp3 : 3 ≤ p := by
    rcases hp_odd with ⟨t, ht⟩
    have h2 := hp.two_le
    omega
  have hp_pos : 0 < p := hp.pos
  -- Goal: p ^ (j+1) ≤ (p ^ j * (p - 1)) ^ 2
  -- (p ^ j * (p - 1)) ^ 2 = p^(2j) * (p-1)^2
  -- We have (p-1)^2 ≥ p for p ≥ 3
  -- So p^j * (p-1)^2 ≥ p^j * p = p^(j+1). And p^(2j) ≥ p^j since j ≥ 0, p ≥ 1.
  have hp_minus_one_sq_ge : p ≤ (p - 1) ^ 2 := by
    -- p ≥ 3, so set q := p - 1 ≥ 2. Goal: q + 1 ≤ q^2.
    set q := p - 1 with hq
    have hq2 : 2 ≤ q := by omega
    have hpeq : p = q + 1 := by omega
    rw [hpeq]
    -- Goal: q + 1 ≤ q^2. q^2 = q*q ≥ 2*q = q + q ≥ q + 2 > q + 1
    have h1 : q * q ≥ 2 * q := Nat.mul_le_mul_right q hq2
    have h2 : 2 * q ≥ q + q := by omega
    have h3 : q + q ≥ q + 1 := by omega
    calc q + 1 ≤ q + q := h3
      _ ≤ 2 * q := by omega
      _ ≤ q * q := h1
      _ = q ^ 2 := by ring
  have hpj_pos : 0 < p ^ j := pow_pos hp_pos _
  calc p ^ (j + 1) = p ^ j * p := by ring
    _ ≤ p ^ j * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hp_minus_one_sq_ge
    _ ≤ p ^ j * (p ^ j * (p - 1) ^ 2) := Nat.le_mul_of_pos_left _ hpj_pos
    _ = (p ^ j * (p - 1)) ^ 2 := by ring

private lemma totient_sq_ge_half_pow_two (k : ℕ) (hk : 0 < k) :
    2 ^ k ≤ 2 * (Nat.totient (2 ^ k)) ^ 2 := by
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
  rw [Nat.totient_prime_pow_succ Nat.prime_two]
  -- Goal: 2 ^ (j+1) ≤ 2 * (2 ^ j * (2 - 1)) ^ 2 = 2 * (2^j)^2 = 2^(2j+1)
  change 2 ^ (j + 1) ≤ 2 * (2 ^ j * (2 - 1)) ^ 2
  have heq : 2 * (2 ^ j * (2 - 1 : ℕ)) ^ 2 = 2 ^ (2 * j + 1) := by
    have h21 : (2 - 1 : ℕ) = 1 := rfl
    rw [h21, mul_one]
    rw [show (2 : ℕ) * (2 ^ j) ^ 2 = 2 ^ (2 * j + 1) from by
      rw [pow_succ]
      ring]
  rw [heq]
  apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
  omega

theorem totient_sq_ge_half (m : ℕ) (_hm : 1 ≤ m) : m ≤ 2 * (Nat.totient m) ^ 2 := by
  -- Strengthened invariant
  suffices h : ∀ n : ℕ, n ≤ 2 * (Nat.totient n) ^ 2 ∧ (Odd n → n ≤ (Nat.totient n) ^ 2) by
    exact (h m).1
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨totient_sq_ge_half_pow_two k hk, ?_⟩
      intro hodd
      exfalso
      have heven : Even (2 ^ k) := by
        rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
        exact ⟨2 ^ j, by
          rw [pow_succ]
          ring⟩
      exact (Nat.not_odd_iff_even.mpr heven) hodd
    · have hp_odd : Odd p := hp.odd_of_ne_two hp2
      have hge : p ^ k ≤ (Nat.totient (p ^ k)) ^ 2 :=
        totient_sq_ge_odd_prime_pow p k hp hp_odd hk
      refine ⟨?_, fun _ => hge⟩
      have hle : (Nat.totient (p ^ k)) ^ 2 ≤ 2 * (Nat.totient (p ^ k)) ^ 2 := by
        have := Nat.zero_le ((Nat.totient (p ^ k)) ^ 2)
        omega
      exact hge.trans hle
  | zero =>
    refine ⟨?_, ?_⟩
    · exact Nat.zero_le _
    · intro hodd
      exfalso
      exact (Nat.not_odd_iff_even.mpr Even.zero) hodd
  | one =>
    refine ⟨?_, fun _ => ?_⟩
    · -- 1 ≤ 2 * φ(1)^2 = 2 * 1 = 2
      rw [Nat.totient_one]
      norm_num
    · rw [Nat.totient_one]
      norm_num
  | coprime a b ha hb hcop iha ihb =>
    obtain ⟨iha1, iha2⟩ := iha
    obtain ⟨ihb1, ihb2⟩ := ihb
    have hφmul : Nat.totient (a * b) = Nat.totient a * Nat.totient b := Nat.totient_mul hcop
    have hsq : (Nat.totient a * Nat.totient b) ^ 2 =
        (Nat.totient a) ^ 2 * (Nat.totient b) ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · -- First conjunct: a*b ≤ 2 * φ(a*b)^2
      by_cases ha_odd : Odd a
      · -- a odd: a ≤ φ(a)^2 and b ≤ 2*φ(b)^2
        have ha_le : a ≤ (Nat.totient a) ^ 2 := iha2 ha_odd
        rw [hφmul, hsq]
        calc a * b ≤ (Nat.totient a) ^ 2 * (2 * (Nat.totient b) ^ 2) :=
              Nat.mul_le_mul ha_le ihb1
          _ = 2 * ((Nat.totient a) ^ 2 * (Nat.totient b) ^ 2) := by ring
      · -- a even: by coprimality b must be odd
        have ha_even : Even a := Nat.not_odd_iff_even.mp ha_odd
        have h2dvda : 2 ∣ a := ha_even.two_dvd
        have hb_odd : Odd b := by
          rw [Nat.odd_iff]
          by_contra hbe
          push Not at hbe
          have : 2 ∣ b := by omega
          have h2dvd_gcd : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h2dvda this
          rw [hcop] at h2dvd_gcd
          omega
        have hb_le : b ≤ (Nat.totient b) ^ 2 := ihb2 hb_odd
        rw [hφmul, hsq]
        calc a * b ≤ (2 * (Nat.totient a) ^ 2) * (Nat.totient b) ^ 2 :=
              Nat.mul_le_mul iha1 hb_le
          _ = 2 * ((Nat.totient a) ^ 2 * (Nat.totient b) ^ 2) := by ring
    · -- Second conjunct: Odd (a*b) → a*b ≤ φ(a*b)^2
      intro hab_odd
      have ha_odd : Odd a := (Nat.odd_mul.mp hab_odd).1
      have hb_odd : Odd b := (Nat.odd_mul.mp hab_odd).2
      rw [hφmul, hsq]
      exact Nat.mul_le_mul (iha2 ha_odd) (ihb2 hb_odd)

/-- Corollary: if `φ(m) = n`, then `m ≤ 2 n²`. -/
theorem totient_preimage_bound {m n : ℕ} (hm : 1 ≤ m) (h : Nat.totient m = n) :
    m ≤ 2 * n ^ 2 := by
  rw [← h]
  exact totient_sq_ge_half m hm

/-! ### Shared trusted prerequisites

Mathlib v4.27 has neither:
  1. Linnik's theorem in the divisibility form used here
     (`linnik_dvd`); nor
  2. the Mertens product asymptotic `∏_{p ≤ y}(1 - 1/p)^{-1} ~ e^γ log y`
     (`mertens_product`).

We rely on exactly these two classical inputs from `ErdosProblems.Axioms`.
Both are well-known
unconditional results (Linnik 1944, Mertens 1874) for which Mathlib v4.27 has
the surrounding infrastructure (e.g., `Nat.Primes.not_summable_one_div`,
`Chebyshev.theta`, `Nat.forall_exists_prime_gt_and_modEq`) but not the named
quantitative theorems themselves. When they land in Mathlib these declarations can
be deleted and replaced with imports.

The original PDF additionally invokes the PNT in the form `ϑ(y) ~ y`. This
formalization avoids that dependency: the lower-bound size estimate uses the
cruder bound `A_Y ≤ P_Y ≤ 4^Y` (provable from `Nat.primorial_le_4_pow`,
already in Mathlib), which is enough for the final `log log x` asymptotic.

Both shared inputs are transitively used by `totient_fibre_extremes`:
`mertens_product` is consumed by `landau_max_ratio` for the upper bound and
by the lower-bound construction; `linnik_dvd` is consumed by the lower-bound
construction at the height-to-`x` rescaling step. -/

/-! ## Lemma 1.1 — Landau's max-ratio asymptotic

`max_{1 ≤ m ≤ T} m/φ(m) = (e^γ + o(1)) log log T`

**Proof strategy used here** (different from PDF; analytic split-at-Y):

For any threshold `Y`, every `m ≥ 1` satisfies (see `Erdos694Scratch`):
```
  m / φ(m) ≤ ∏_{p ≤ Y, p prime} p/(p-1)  ·  ((Y+1)/Y) ^ (log m / log(Y+1)).
```
Choosing `Y = Y(T) → ∞` slowly enough that `((Y+1)/Y)^(log T/log(Y+1)) → 1` and
applying `mertens_product` to the first factor gives the asymptotic.
-/

/- ### Landau's lemma — proof

We choose `Y(T) := ⌊log T / log 4⌋`. Key properties:
- `Y(T) → ∞` as `T → ∞` (slowly).
- `primorial Y ≤ 4^Y ≤ T`, so `primorial Y ∈ [1, ⌊T⌋]`.
- `m/φ(m)` at `m = primorial Y` equals `primeEulerProdNat Y` (lower witness).
- For every `m ∈ [1, ⌊T⌋]`, `m/φ(m) ≤ primeEulerProdNat Y · ((Y+1)/Y)^(log T/log(Y+1))`.
- The extra factor `((Y+1)/Y)^(log T/log(Y+1)) → 1` and
  `primeEulerProdNat Y / (e^γ log Y) → 1` (Mertens), `log Y / log log T → 1`.
-/

private noncomputable def landauY (T : ℝ) : ℕ := ⌊Real.log T / Real.log 4⌋₊

private lemma landauY_log4_le (T : ℝ) (hT : 1 ≤ T) :
    (landauY T : ℝ) * Real.log 4 ≤ Real.log T := by
  unfold landauY
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogT_nn : 0 ≤ Real.log T := Real.log_nonneg hT
  have h := Nat.floor_le (a := Real.log T / Real.log 4) (by positivity)
  have heq : (Real.log T / Real.log 4) * Real.log 4 = Real.log T := by
    field_simp
  calc (⌊Real.log T / Real.log 4⌋₊ : ℝ) * Real.log 4
      ≤ (Real.log T / Real.log 4) * Real.log 4 :=
        mul_le_mul_of_nonneg_right h hlog4_pos.le
    _ = Real.log T := heq

private lemma landauY_tendsto :
    Tendsto landauY atTop atTop := by
  unfold landauY
  -- log T / log 4 → ∞, then ⌊·⌋₊ → ∞.
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h1 : Tendsto (fun T : ℝ => Real.log T / Real.log 4) atTop atTop := by
    have := Real.tendsto_log_atTop
    exact this.atTop_div_const hlog4_pos
  exact tendsto_nat_floor_atTop.comp h1

private lemma landauY_ge_one_eventually :
    ∀ᶠ T : ℝ in atTop, 1 ≤ landauY T := landauY_tendsto.eventually_ge_atTop 1

private lemma landauY_ge_two_eventually :
    ∀ᶠ T : ℝ in atTop, 2 ≤ landauY T := landauY_tendsto.eventually_ge_atTop 2

private lemma four_pow_landauY_le (T : ℝ) (hT : 1 ≤ T) :
    ((4 : ℝ) ^ landauY T) ≤ T := by
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hT_pos : 0 < T := by linarith
  have hY_le : (landauY T : ℝ) * Real.log 4 ≤ Real.log T := landauY_log4_le T hT
  -- From Y * log 4 ≤ log T, deduce 4^Y ≤ T.
  have h1 : Real.log ((4 : ℝ) ^ landauY T) = (landauY T : ℝ) * Real.log 4 := by
    rw [Real.log_pow]
  have h4_pos : (0 : ℝ) < (4 : ℝ) ^ landauY T := by positivity
  have h2 : Real.log ((4 : ℝ) ^ landauY T) ≤ Real.log T := by
    rw [h1]
    exact hY_le
  exact (Real.log_le_log_iff h4_pos hT_pos).mp h2

/-- Primorial Y has prime factors exactly {primes ≤ Y}, so its m/φ(m) ratio equals
`primeEulerProdNat Y`. -/
private lemma ratio_totient_primorial (Y : ℕ) (_hY : 1 ≤ Y) :
    (primorial Y : ℝ) / Nat.totient (primorial Y) =
      primeEulerProdNat Y := by
  classical
  set m := primorial Y
  have hm_pos : 0 < m := primorial_pos Y
  have hm_ne : m ≠ 0 := hm_pos.ne'
  -- primeFactors(m) = (Finset.range (Y+1)).filter Nat.Prime
  have hfacts : m.primeFactors = (Finset.range (Y + 1)).filter Nat.Prime := by
    change (∏ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, p).primeFactors =
        (Finset.range (Y + 1)).filter Nat.Prime
    apply Nat.primeFactors_prod
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  rw [ratio_totient_eq_prod_primeFactors_real m hm_ne]
  rw [hfacts]
  unfold primeEulerProdNat
  -- Need: ∏ p ∈ (range (Y+1)).filter Prime, ... = ∏ p ∈ (Icc 1 Y).filter Prime, ...
  -- These finsets are equal (primes p satisfy 1 ≤ p ≤ Y iff p ∈ range(Y+1) ∧ p prime, modulo
  -- the fact that primes are ≥ 2 ≥ 1).
  apply Finset.prod_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hpr, hppri⟩
    refine ⟨⟨hppri.one_le, ?_⟩, hppri⟩
    omega
  · rintro ⟨⟨_, hpY⟩, hppri⟩
    exact ⟨by omega, hppri⟩

/-- `log Y → ∞` as `Y → ∞` (over `ℕ`). -/
private lemma log_landauY_tendsto :
    Tendsto (fun T : ℝ => Real.log (landauY T : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop).comp landauY_tendsto)

/-- `log log T / log Y(T) → 1`, i.e., `log Y(T) / log log T → 1`. -/
private lemma log_landauY_div_loglog_tendsto :
    Tendsto (fun T : ℝ => Real.log (landauY T : ℝ) / Real.log (Real.log T)) atTop (𝓝 1) := by
  -- Y(T) = ⌊log T / log 4⌋, so log Y(T) = log(log T / log 4) + o(1)
  --       = log log T - log log 4 + o(1).
  -- So log Y(T) / log log T = 1 - log log 4 / log log T + o(1/log log T) → 1.
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  -- We squeeze: (log T / log 4 - 1) ≤ Y ≤ log T / log 4, so for large T,
  -- log Y is within o(1) of log log T - log log 4.
  -- Easier: log Y / log(log T / log 4) → 1 (since Y / (log T / log 4) → 1).
  -- Then log(log T / log 4) / log log T → 1.
  -- Step 1: log Y - log(log T / log 4) → 0.
  have h_step1 :
      Tendsto
        (fun T : ℝ => Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4))
      atTop (𝓝 0) := by
    -- = log (Y / (log T / log 4)). And Y / (log T / log 4) → 1 (since |x - ⌊x⌋| ≤ 1 and x → ∞).
    -- Use: log Y - log x = log (Y/x) → log 1 = 0.
    -- For T large enough, both Y ≥ 1 and log T / log 4 ≥ 1.
    have h_ratio : Tendsto
        (fun T : ℝ => (landauY T : ℝ) / (Real.log T / Real.log 4)) atTop (𝓝 1) := by
      -- |Y - log T / log 4| ≤ 1 ≤ small relative to log T / log 4.
      -- Use squeeze: Y / x ∈ [(x-1)/x, x/x] = [1 - 1/x, 1].
      have h_sandwich_lower : ∀ᶠ T : ℝ in atTop,
          1 - 1 / (Real.log T / Real.log 4) ≤ (landauY T : ℝ) / (Real.log T / Real.log 4) := by
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with T hT_gt
        have hT1 : 1 ≤ T := le_of_lt hT_gt
        have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
        have hx_pos : 0 < Real.log T / Real.log 4 := by positivity
        unfold landauY
        have h_floor_ge : Real.log T / Real.log 4 - 1 < ⌊Real.log T / Real.log 4⌋₊ + 1 := by
          have := Nat.lt_floor_add_one (a := Real.log T / Real.log 4)
          linarith
        have h_floor_ge' : Real.log T / Real.log 4 - 1 ≤ (⌊Real.log T / Real.log 4⌋₊ : ℝ) := by
          have h := Nat.sub_one_lt_floor (Real.log T / Real.log 4)
          linarith
        rw [le_div_iff₀ hx_pos]
        have h1 : (1 - 1 / (Real.log T / Real.log 4)) * (Real.log T / Real.log 4) =
            Real.log T / Real.log 4 - 1 := by
          field_simp
        rw [h1]
        exact h_floor_ge'
      have h_sandwich_upper : ∀ᶠ T : ℝ in atTop,
          (landauY T : ℝ) / (Real.log T / Real.log 4) ≤ 1 := by
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with T hT_gt
        have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
        have hx_pos : 0 < Real.log T / Real.log 4 := by positivity
        rw [div_le_one hx_pos]
        unfold landauY
        exact Nat.floor_le (by positivity)
      have h_lower_to_one :
          Tendsto (fun T : ℝ => 1 - 1 / (Real.log T / Real.log 4)) atTop (𝓝 1) := by
        have h_inner : Tendsto (fun T : ℝ => Real.log T / Real.log 4) atTop atTop :=
          Real.tendsto_log_atTop.atTop_div_const hlog4_pos
        have h_inv : Tendsto (fun T : ℝ => 1 / (Real.log T / Real.log 4)) atTop (𝓝 0) := by
          have hi := h_inner.inv_tendsto_atTop
          have : (fun T : ℝ => 1 / (Real.log T / Real.log 4)) =
              (fun T : ℝ => (Real.log T / Real.log 4)⁻¹) := by
            ext T
            rw [one_div]
          rw [this]
          exact hi
        have : Tendsto (fun T : ℝ => 1 - 1 / (Real.log T / Real.log 4)) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub h_inv
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_to_one tendsto_const_nhds
        h_sandwich_lower h_sandwich_upper
    -- Now log of ratio → log 1 = 0.
    have h_log_ratio : Tendsto
        (fun T : ℝ => Real.log ((landauY T : ℝ) / (Real.log T / Real.log 4))) atTop (𝓝 0) := by
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h_ratio
      simpa [Real.log_one] using this
    -- log(Y / x) = log Y - log x for Y > 0, x > 0.
    have h_eventual : ∀ᶠ T : ℝ in atTop,
        Real.log ((landauY T : ℝ) / (Real.log T / Real.log 4)) =
          Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4) := by
      filter_upwards [landauY_ge_one_eventually, Filter.eventually_gt_atTop (1 : ℝ)] with T hY1 hT
      have hY_pos : (0 : ℝ) < (landauY T : ℝ) := by exact_mod_cast hY1
      have hlogT_pos : 0 < Real.log T := Real.log_pos hT
      have hx_pos : (0 : ℝ) < Real.log T / Real.log 4 := by positivity
      rw [Real.log_div hY_pos.ne' hx_pos.ne']
    exact (Filter.Tendsto.congr' h_eventual h_log_ratio)
  -- Step 2: log(log T / log 4) / log log T → 1.
  have h_step2 : Tendsto (fun T : ℝ => Real.log (Real.log T / Real.log 4) / Real.log (Real.log T))
      atTop (𝓝 1) := by
    -- log(log T / log 4) = log log T - log log 4. Divide by log log T → 1.
    have h_loglog_inf : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    have h_eq : ∀ᶠ T : ℝ in atTop,
        Real.log (Real.log T / Real.log 4) / Real.log (Real.log T) =
          1 - Real.log (Real.log 4) / Real.log (Real.log T) := by
      filter_upwards [Filter.eventually_gt_atTop (Real.exp 2)] with T hT
      have hexp2_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
      have hT_pos : 0 < T := lt_of_lt_of_le hexp2_pos hT.le
      have h_logT_gt : 2 < Real.log T := by
        have := Real.log_lt_log hexp2_pos hT
        simpa [Real.log_exp] using this
      have hlogT_pos : 0 < Real.log T := by linarith
      have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
      have h_loglogT_pos : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
      rw [Real.log_div hlogT_pos.ne' hlog4_pos.ne']
      field_simp
    have h_inner_tendsto : Tendsto
        (fun T : ℝ => 1 - Real.log (Real.log 4) / Real.log (Real.log T)) atTop (𝓝 1) := by
      have h_inv : Tendsto (fun T : ℝ => Real.log (Real.log 4) / Real.log (Real.log T))
          atTop (𝓝 0) := by
        have := h_loglog_inf.inv_tendsto_atTop
        have h2 := this.const_mul (Real.log (Real.log 4))
        simpa [div_eq_mul_inv] using h2
      have : Tendsto (fun T : ℝ => 1 - Real.log (Real.log 4) / Real.log (Real.log T)) atTop
          (𝓝 (1 - 0)) := tendsto_const_nhds.sub h_inv
      simpa using this
    exact h_inner_tendsto.congr' (h_eq.mono (fun _ => Eq.symm))
  -- Combine: (log Y - log(log T / log 4)) → 0, and log(log T / log 4) / log log T → 1.
  -- log Y / log log T = (log Y - log(log T / log 4)) / log log T + log(log T / log 4)/ log log T
  --                   → 0 + 1 = 1.
  have h_loglog_inf : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h_diff_div : Tendsto
      (fun T : ℝ => (Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4))
        / Real.log (Real.log T)) atTop (𝓝 0) := by
    have := h_step1.div_atTop h_loglog_inf
    simpa using this
  have h_sum : Tendsto
      (fun T : ℝ => (Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4))
        / Real.log (Real.log T)
        + Real.log (Real.log T / Real.log 4) / Real.log (Real.log T)) atTop (𝓝 (0 + 1)) :=
    h_diff_div.add h_step2
  have h_eq2 : ∀ᶠ T : ℝ in atTop,
      (Real.log (landauY T : ℝ) - Real.log (Real.log T / Real.log 4)) / Real.log (Real.log T)
        + Real.log (Real.log T / Real.log 4) / Real.log (Real.log T)
        = Real.log (landauY T : ℝ) / Real.log (Real.log T) := by
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 2)] with T hT
    have hexp2_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
    have h_logT_gt : 2 < Real.log T := by
      have := Real.log_lt_log hexp2_pos hT
      simpa [Real.log_exp] using this
    have hlogT_pos : 0 < Real.log T := by linarith
    have h_loglogT_pos : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
    have h := h_loglogT_pos.ne'
    field_simp
    ring
  have h_final : Tendsto (fun T : ℝ => Real.log (landauY T : ℝ) / Real.log (Real.log T))
      atTop (𝓝 1) := by
    have := Filter.Tendsto.congr' h_eq2 h_sum
    simpa using this
  exact h_final

theorem landau_max_ratio :
    Tendsto
      (fun T : ℝ => (⨆ m ∈ Set.Icc 1 ⌊T⌋₊,
        (m : ℝ) / Nat.totient m) / (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log T)))
      atTop (𝓝 1) := by
  -- Notation
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  -- Y(T) := ⌊log T / log 4⌋. Y → ∞, primorial Y ≤ 4^Y ≤ T.
  set Y : ℝ → ℕ := landauY with hY_def
  -- denominator: γc * log log T.
  set D : ℝ → ℝ := fun T => γc * Real.log (Real.log T) with hD_def
  -- sup function S.
  set S : ℝ → ℝ := fun T => ⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m with hS_def
  -- "primeEulerProdNat Y(T)" — lower bound.
  set L : ℝ → ℝ := fun T => primeEulerProdNat (Y T) with hL_def
  -- Upper bound factor ((Y+1)/Y)^(log T / log(Y+1)).
  set F : ℝ → ℝ := fun T => (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
    (Real.log T / Real.log ((Y T : ℝ) + 1)) with hF_def
  -- Mertens applied to ℕ→ℝ via Y.
  have h_loglog_inf : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have h_logT_pos_ev : ∀ᶠ T : ℝ in atTop, 0 < Real.log T := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with T hT
    exact Real.log_pos hT
  have h_loglog_pos_ev : ∀ᶠ T : ℝ in atTop, 0 < Real.log (Real.log T) := by
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with T hT
    have h1 : 1 < Real.log T := by
      have := Real.log_lt_log (Real.exp_pos _) hT
      simpa [Real.log_exp] using this
    exact Real.log_pos h1
  -- Mertens for our Y: primeEulerProdNat(Y(T)) / (γc * log Y(T)) → 1.
  have h_mertens_Y :
      Tendsto (fun T : ℝ => L T / (γc * Real.log (Y T : ℝ))) atTop (𝓝 1) := by
    -- mertens_product: (∏_{p ∈ filter Prime (Icc 1 ⌊y⌋₊)} p/(p-1)) / (γc * log y) → 1 as y → ∞.
    -- Compose with y = (Y T : ℝ). Then ⌊(Y T : ℝ)⌋₊ = Y T (since Y T : ℕ).
    have h_yT_to_inf : Tendsto (fun T : ℝ => ((Y T : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp landauY_tendsto
    have h := _root_.mertens_product.comp h_yT_to_inf
    -- This gives: (∏_{p ∈ filter Prime (Icc 1 ⌊(Y T : ℝ)⌋₊)} ...) / (γc * log (Y T : ℝ)) → 1.
    -- Need to convert to L T / (γc * log Y T).
    have h_eq : ∀ᶠ T : ℝ in atTop,
        (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊((Y T : ℕ) : ℝ)⌋₊), ((p : ℝ) / (p - 1))) /
            (Real.exp Real.eulerMascheroniConstant * Real.log ((Y T : ℕ) : ℝ)) =
          L T / (γc * Real.log (Y T : ℝ)) := by
      filter_upwards with T
      have hfloor : ⌊((Y T : ℕ) : ℝ)⌋₊ = Y T := Nat.floor_natCast (Y T)
      rw [hfloor]
      rfl
    exact h.congr' h_eq
  -- log Y(T) / log log T → 1.
  have h_logY_div : Tendsto (fun T : ℝ => Real.log (Y T : ℝ) / Real.log (Real.log T))
      atTop (𝓝 1) := log_landauY_div_loglog_tendsto
  -- L(T) / D(T) → 1.
  have h_LD : Tendsto (fun T => L T / D T) atTop (𝓝 1) := by
    -- L/D = (L / (γc log Y)) * (log Y / log log T) — provided log log T ≠ 0.
    have h_prod : Tendsto
        (fun T : ℝ => (L T / (γc * Real.log (Y T : ℝ))) *
          (Real.log (Y T : ℝ) / Real.log (Real.log T))) atTop (𝓝 (1 * 1)) :=
      h_mertens_Y.mul h_logY_div
    have h_eq : ∀ᶠ T : ℝ in atTop,
        (L T / (γc * Real.log (Y T : ℝ))) *
          (Real.log (Y T : ℝ) / Real.log (Real.log T)) = L T / D T := by
      filter_upwards [landauY_ge_two_eventually, h_loglog_pos_ev] with T hY2 hloglog_pos
      have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
      have hY_gt_one : (1 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 1 < Y T)
      have h_logY_pos : 0 < Real.log (Y T : ℝ) := Real.log_pos hY_gt_one
      change (L T / (γc * Real.log (Y T : ℝ))) *
          (Real.log (Y T : ℝ) / Real.log (Real.log T)) = L T / D T
      rw [hD_def]
      simp only
      field_simp
    have := h_prod.congr' h_eq
    simpa using this
  -- F(T) → 1.
  -- log F(T) = (log T / log(Y+1)) * log((Y+1)/Y).
  -- For Y ≥ 2: 0 ≤ log F T ≤ log T / (Y log(Y+1)) → 0.
  have hF_pos_ev : ∀ᶠ T : ℝ in atTop, 0 < F T := by
    filter_upwards [landauY_ge_one_eventually] with T hY1
    have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
    have hbase_pos : 0 < ((Y T : ℝ) + 1) / (Y T : ℝ) := by positivity
    exact Real.rpow_pos_of_pos hbase_pos _
  have hF_to_one : Tendsto F atTop (𝓝 1) := by
    -- F = exp(log F) and we'll show log F → 0.
    have h_logF_eq : ∀ᶠ T : ℝ in atTop,
        Real.log (F T) =
          Real.log T / Real.log ((Y T : ℝ) + 1) *
            Real.log (((Y T : ℝ) + 1) / (Y T : ℝ)) := by
      filter_upwards [landauY_ge_one_eventually] with T hY1
      have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
      have hbase_pos : 0 < ((Y T : ℝ) + 1) / (Y T : ℝ) := by positivity
      change Real.log ((((Y T : ℝ) + 1) / (Y T : ℝ)) ^
        (Real.log T / Real.log ((Y T : ℝ) + 1))) = _
      rw [Real.log_rpow hbase_pos]
    -- Bound: 0 ≤ log F ≤ log T / (Y · log(Y+1)).
    have h_logF_nn_ev : ∀ᶠ T : ℝ in atTop, 0 ≤ Real.log (F T) := by
      filter_upwards [h_logF_eq, landauY_ge_two_eventually,
        Filter.eventually_gt_atTop (1 : ℝ)] with T heq hY2 hT_gt
      rw [heq]
      have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
      have hYp1_pos : (0 : ℝ) < (Y T : ℝ) + 1 := by linarith
      have hY_gt_one : (1 : ℝ) < (Y T : ℝ) + 1 := by linarith
      have hlog_Yp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := Real.log_pos hY_gt_one
      have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
      -- log T / log(Y+1) ≥ 0; (Y+1)/Y ≥ 1, so log ≥ 0.
      have h_div_nn : 0 ≤ Real.log T / Real.log ((Y T : ℝ) + 1) :=
        div_nonneg hlogT_pos.le hlog_Yp1_pos.le
      have h_base_ge_one : 1 ≤ ((Y T : ℝ) + 1) / (Y T : ℝ) := by
        rw [le_div_iff₀ hY_pos]
        linarith
      have h_log_base_nn : 0 ≤ Real.log (((Y T : ℝ) + 1) / (Y T : ℝ)) := by
        exact Real.log_nonneg h_base_ge_one
      exact mul_nonneg h_div_nn h_log_base_nn
    have h_logF_le_ev : ∀ᶠ T : ℝ in atTop,
        Real.log (F T) ≤ Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) := by
      filter_upwards [h_logF_eq, landauY_ge_two_eventually,
        Filter.eventually_gt_atTop (1 : ℝ)] with T heq hY2 hT_gt
      rw [heq]
      have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
      have hYp1_pos : (0 : ℝ) < (Y T : ℝ) + 1 := by linarith
      have hY_gt_one_succ : (1 : ℝ) < (Y T : ℝ) + 1 := by linarith
      have hlog_Yp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := Real.log_pos hY_gt_one_succ
      have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
      -- log((Y+1)/Y) = log(1 + 1/Y) ≤ 1/Y (since log(1+x) ≤ x for x ≥ 0).
      have h_one_plus : ((Y T : ℝ) + 1) / (Y T : ℝ) = 1 + 1 / (Y T : ℝ) := by
        field_simp
      have h_log_le : Real.log (((Y T : ℝ) + 1) / (Y T : ℝ)) ≤ 1 / (Y T : ℝ) := by
        rw [h_one_plus]
        have h_inv_nn : 0 ≤ 1 / (Y T : ℝ) := by positivity
        exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by
          have : 1 + 1 / (Y T : ℝ) - 1 = 1 / (Y T : ℝ) := by ring
          linarith)
      have h_div_nn : 0 ≤ Real.log T / Real.log ((Y T : ℝ) + 1) :=
        div_nonneg hlogT_pos.le hlog_Yp1_pos.le
      calc Real.log T / Real.log ((Y T : ℝ) + 1) *
            Real.log (((Y T : ℝ) + 1) / (Y T : ℝ))
          ≤ Real.log T / Real.log ((Y T : ℝ) + 1) * (1 / (Y T : ℝ)) :=
            mul_le_mul_of_nonneg_left h_log_le h_div_nn
        _ = Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) := by
            field_simp
    -- Now show log T / (Y · log(Y+1)) → 0.
    -- We have Y ≥ log T / log 4 - 1, so Y · log(Y+1) ≥ (log T / log 4 - 1) · log(2).
    -- Actually for ε > 0, we want log T / (Y · log(Y+1)) ≤ ε eventually.
    -- For T large, Y ≥ log T / (2 log 4), and Y+1 ≥ 2, so log(Y+1) ≥ log 2.
    -- So Y · log(Y+1) ≥ (log T / (2 log 4)) · log 2.
    -- log T / (Y · log(Y+1)) ≤ log T / ((log T)·log 2/(2 log 4)) = 2 log 4 / log 2.
    -- Wait, that doesn't go to 0! We need a better lower bound on Y · log(Y+1).
    -- Since Y → ∞, log(Y+1) → ∞, so Y · log(Y+1) ≥ Y · log Y ≥ (log T)·(log log T) /(C),
    -- which dominates log T. So ratio → 0.
    have h_upper_to_zero : Tendsto
        (fun T : ℝ => Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1))) atTop (𝓝 0) := by
      -- Bound: For T large, Y ≥ log T / (2 log 4) and log(Y+1) ≥ log Y.
      -- Y · log(Y+1) ≥ Y · log Y.
      -- Actually use a cleaner approach: the limit
      -- log T / (Y log Y) — replace Y with a real-valued thing close to log T / log 4.
      -- Cleaner: log T / (Y · log(Y+1)) = (log 4) · (log T / log 4) / (Y · log(Y+1))
      --                                ≤ (log 4) · (Y+1) / (Y · log(Y+1))
      --                                = (log 4) · (1 + 1/Y) / log(Y+1)
      --                                → log 4 · 1 / ∞ = 0.
      -- Use: log T ≤ (Y+1) log 4 from Y ≥ log T/log 4 - 1.
      have h_logT_bound : ∀ᶠ T : ℝ in atTop,
          Real.log T ≤ ((Y T : ℝ) + 1) * Real.log 4 := by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
        have h := landauY_log4_le T hT
        -- (Y) * log 4 ≤ log T, so log T ≤ (Y+1) log 4 needs Y+1 ≥ log T / log 4, true since
        -- Y = ⌊log T / log 4⌋ and ⌊x⌋ + 1 > x.
        have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
        have h2 : Real.log T / Real.log 4 < (landauY T : ℝ) + 1 := Nat.lt_floor_add_one _
        -- log T = (log T / log 4) * log 4 < ((Y T : ℝ) + 1) * log 4.
        have heq : Real.log T = (Real.log T / Real.log 4) * Real.log 4 := by
          field_simp
        rw [heq]
        exact (mul_le_mul_of_nonneg_right h2.le hlog4_pos.le)
      have h_main_bd : ∀ᶠ T : ℝ in atTop,
          Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) ≤
            Real.log 4 * ((1 + 1 / (Y T : ℝ)) / Real.log ((Y T : ℝ) + 1)) := by
        filter_upwards [h_logT_bound, landauY_ge_two_eventually] with T hbd hY2
        have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
        have hYp1_pos : (0 : ℝ) < (Y T : ℝ) + 1 := by linarith
        have hY_gt_one_succ : (1 : ℝ) < (Y T : ℝ) + 1 := by linarith
        have hlog_Yp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := Real.log_pos hY_gt_one_succ
        have hdenom_pos : 0 < (Y T : ℝ) * Real.log ((Y T : ℝ) + 1) :=
          mul_pos hY_pos hlog_Yp1_pos
        rw [div_le_iff₀ hdenom_pos]
        have heq : Real.log 4 * ((1 + 1 / (Y T : ℝ)) / Real.log ((Y T : ℝ) + 1)) *
              ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) =
            Real.log 4 * ((1 + 1 / (Y T : ℝ)) * (Y T : ℝ)) := by
          field_simp
        rw [heq]
        have : Real.log 4 * ((1 + 1 / (Y T : ℝ)) * (Y T : ℝ)) =
            Real.log 4 * ((Y T : ℝ) + 1) := by
          field_simp
        rw [this, mul_comm (Real.log 4) _]
        exact hbd
      -- Now show RHS → 0.
      have h_rhs_to_zero : Tendsto
          (fun T : ℝ => Real.log 4 * ((1 + 1 / (Y T : ℝ)) / Real.log ((Y T : ℝ) + 1)))
          atTop (𝓝 (Real.log 4 * 0)) := by
        apply Tendsto.const_mul
        -- (1 + 1/Y) → 1, log(Y+1) → ∞, so (1+1/Y)/log(Y+1) → 0.
        have h_num : Tendsto (fun T : ℝ => 1 + 1 / (Y T : ℝ)) atTop (𝓝 (1 + 0)) := by
          apply Tendsto.const_add
          have h_inv : Tendsto (fun T : ℝ => 1 / (Y T : ℝ)) atTop (𝓝 0) := by
            have hYTend : Tendsto (fun T : ℝ => ((Y T : ℕ) : ℝ)) atTop atTop :=
              tendsto_natCast_atTop_atTop.comp landauY_tendsto
            have := hYTend.inv_tendsto_atTop
            have : (fun T : ℝ => 1 / (Y T : ℝ)) = fun T : ℝ => ((Y T : ℝ))⁻¹ := by
              ext T
              rw [one_div]
            rw [this]
            exact hYTend.inv_tendsto_atTop
          exact h_inv
        have h_denom : Tendsto (fun T : ℝ => Real.log ((Y T : ℝ) + 1)) atTop atTop := by
          have hYTend : Tendsto (fun T : ℝ => ((Y T : ℕ) : ℝ)) atTop atTop :=
            tendsto_natCast_atTop_atTop.comp landauY_tendsto
          have hYp1 : Tendsto (fun T : ℝ => (Y T : ℝ) + 1) atTop atTop :=
            hYTend.atTop_add tendsto_const_nhds
          exact Real.tendsto_log_atTop.comp hYp1
        have := h_num.div_atTop h_denom
        simpa using this
      have h_zero_eq : Real.log 4 * 0 = 0 := by ring
      rw [h_zero_eq] at h_rhs_to_zero
      -- Squeeze: 0 ≤ log T / (Y log(Y+1)) ≤ RHS, with both ends → 0.
      have h_lhs_nn : ∀ᶠ T : ℝ in atTop,
          0 ≤ Real.log T / ((Y T : ℝ) * Real.log ((Y T : ℝ) + 1)) := by
        filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), landauY_ge_two_eventually] with
          T hT_gt hY2
        have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
        have hY_gt_one_succ : (1 : ℝ) < (Y T : ℝ) + 1 := by linarith
        have hlog_Yp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := Real.log_pos hY_gt_one_succ
        have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt
        positivity
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_rhs_to_zero
        h_lhs_nn h_main_bd
    -- Squeeze log F: 0 ≤ log F ≤ ... → 0. So log F → 0.
    have h_logF_to_zero : Tendsto (fun T => Real.log (F T)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper_to_zero
        h_logF_nn_ev h_logF_le_ev
    -- F = exp(log F), so F → exp 0 = 1.
    have h_F_eq : ∀ᶠ T : ℝ in atTop, Real.exp (Real.log (F T)) = F T := by
      filter_upwards [hF_pos_ev] with T hF_pos
      exact Real.exp_log hF_pos
    have h_exp : Tendsto (fun T => Real.exp (Real.log (F T))) atTop (𝓝 (Real.exp 0)) :=
      Real.continuous_exp.tendsto _ |>.comp h_logF_to_zero
    have : Tendsto F atTop (𝓝 (Real.exp 0)) := h_exp.congr' h_F_eq
    simpa using this
  -- U(T)/D(T) := L(T) * F(T) / D(T) = (L(T)/D(T)) * F(T) → 1 * 1 = 1.
  have h_UD : Tendsto (fun T => L T * F T / D T) atTop (𝓝 1) := by
    have h := h_LD.mul hF_to_one
    have h_eq : ∀ᶠ T : ℝ in atTop, L T / D T * F T = L T * F T / D T := by
      filter_upwards with T
      ring
    have := h.congr' h_eq
    simpa using this
  -- Now bounds: L T ≤ S T ≤ L T * F T eventually.
  -- S T is the sup; ratio_totient_le_log_split_bound gives upper, primorial gives lower.
  -- Need: BddAbove the sup family for ciSup_le.
  have h_bound_ev : ∀ᶠ T : ℝ in atTop,
      L T / D T ≤ S T / D T ∧ S T / D T ≤ L T * F T / D T := by
    filter_upwards [landauY_ge_one_eventually, h_loglog_pos_ev,
      Filter.eventually_ge_atTop (1 : ℝ)] with T hY1 hloglog_pos hT1
    -- Set up positivity facts.
    have hY_pos : (0 : ℝ) < (Y T : ℝ) := by exact_mod_cast (by linarith : 0 < Y T)
    have hYp1_pos : (0 : ℝ) < (Y T : ℝ) + 1 := by linarith
    have hbase_ge_one : 1 ≤ ((Y T : ℝ) + 1) / (Y T : ℝ) := by
      rw [le_div_iff₀ hY_pos]
      linarith
    have hbase_pos : 0 < ((Y T : ℝ) + 1) / (Y T : ℝ) := by positivity
    have hT_pos : 0 < T := by linarith
    have hlogT_nn : 0 ≤ Real.log T := Real.log_nonneg hT1
    have h_floor_T_pos : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT1)
    -- L T ≥ 1 (it's a product of factors ≥ 1).
    have hL_ge_one : 1 ≤ L T := by
      change 1 ≤ primeEulerProdNat (Y T)
      unfold primeEulerProdNat
      -- Use a generic helper: prove for any finset of primes, product of p/(p-1) ≥ 1.
      have aux : ∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p) →
          (1 : ℝ) ≤ ∏ p ∈ s, (p : ℝ) / (p - 1) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            intro _
            simp
        | insert p s' hps ih =>
            intro hpp
            rw [Finset.prod_insert hps]
            have hp_prime : Nat.Prime p := hpp p (Finset.mem_insert_self _ _)
            have hp1 : (1 : ℝ) ≤ (p : ℝ) / (p - 1) :=
              one_le_prime_factor p hp_prime
            have hs'_each : ∀ q ∈ s', Nat.Prime q := fun q hq =>
              hpp q (Finset.mem_insert_of_mem hq)
            have hs' : (1 : ℝ) ≤ ∏ q ∈ s', (q : ℝ) / (q - 1) := ih hs'_each
            calc (1 : ℝ) = 1 * 1 := by ring
              _ ≤ (p : ℝ) / (p - 1) * ∏ q ∈ s', (q : ℝ) / (q - 1) :=
                mul_le_mul hp1 hs' zero_le_one (zero_le_one.trans hp1)
      apply aux
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hL_pos : 0 < L T := by linarith
    -- BddAbove for the sup family.
    have hbdd_inner :
        BddAbove (Set.range (fun (m : ℕ) =>
          ⨆ (_ : m ∈ Set.Icc 1 ⌊T⌋₊), (m : ℝ) / Nat.totient m)) := by
      refine ⟨L T * F T, ?_⟩
      rintro _ ⟨m, rfl⟩
      simp only
      by_cases hm : m ∈ Set.Icc 1 ⌊T⌋₊
      · rw [ciSup_pos hm]
        -- bound m/φ(m) ≤ L T * F T using ratio_totient_le_log_split_bound.
        have hm_pos : 1 ≤ m := hm.1
        have hm_ne : m ≠ 0 := by omega
        have h_split := ratio_totient_le_log_split_bound m (Y T) hm_ne hY1
        -- h_split says: m/φ(m) ≤ L T * ((Y+1)/Y)^(log m / log(Y+1)).
        -- We want: m/φ(m) ≤ L T * F T = L T * ((Y+1)/Y)^(log T / log(Y+1)).
        -- Since base ≥ 1 and log m ≤ log T (m ≤ ⌊T⌋ ≤ T), the exponent is at most log T/log(Y+1).
        have hm_le_T : (m : ℝ) ≤ T := by
          have := hm.2
          have hm_le_floor_R : (m : ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast this
          calc (m : ℝ) ≤ (⌊T⌋₊ : ℝ) := hm_le_floor_R
            _ ≤ T := Nat.floor_le (by linarith : (0 : ℝ) ≤ T)
        have hlog_le : Real.log m ≤ Real.log T := by
          have hm_pos_R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
          exact Real.log_le_log hm_pos_R hm_le_T
        have hlogYp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := by
          apply Real.log_pos
          linarith
        have hexp_le : Real.log m / Real.log ((Y T : ℝ) + 1) ≤
            Real.log T / Real.log ((Y T : ℝ) + 1) := by
          exact div_le_div_of_nonneg_right hlog_le hlogYp1_pos.le
        have h_pow_le :
            (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
                (Real.log m / Real.log ((Y T : ℝ) + 1)) ≤
            (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
                (Real.log T / Real.log ((Y T : ℝ) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_le
        -- Combine.
        have h_split' : (m : ℝ) / Nat.totient m ≤
            L T * (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
              (Real.log m / Real.log ((Y T : ℝ) + 1)) := by
          have hh := h_split
          push_cast at hh
          exact hh
        have h_chain : (m : ℝ) / Nat.totient m ≤
            L T * (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
              (Real.log T / Real.log ((Y T : ℝ) + 1)) := by
          calc (m : ℝ) / Nat.totient m ≤ _ := h_split'
            _ ≤ L T * _ := mul_le_mul_of_nonneg_left h_pow_le hL_pos.le
        change (m : ℝ) / Nat.totient m ≤ L T * F T
        exact h_chain
      · rw [ciSup_neg hm, Real.sSup_empty]
        have : 0 ≤ L T * F T := by
          have hF_nn : 0 ≤ F T := by
            exact (Real.rpow_pos_of_pos hbase_pos _).le
          exact mul_nonneg hL_pos.le hF_nn
        exact this
    -- Now S T ≤ L T * F T.
    have hS_le_LF : S T ≤ L T * F T := by
      change (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) ≤ L T * F T
      apply ciSup_le
      intro m
      by_cases hm : m ∈ Set.Icc 1 ⌊T⌋₊
      · rw [ciSup_pos hm]
        -- bound m/φ(m) ≤ L T * F T (re-prove).
        have hm_pos : 1 ≤ m := hm.1
        have hm_ne : m ≠ 0 := by omega
        have h_split := ratio_totient_le_log_split_bound m (Y T) hm_ne hY1
        have hm_le_T : (m : ℝ) ≤ T := by
          have := hm.2
          have hm_le_floor_R : (m : ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast this
          calc (m : ℝ) ≤ (⌊T⌋₊ : ℝ) := hm_le_floor_R
            _ ≤ T := Nat.floor_le (by linarith : (0 : ℝ) ≤ T)
        have hm_pos_R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
        have hlog_le : Real.log m ≤ Real.log T := Real.log_le_log hm_pos_R hm_le_T
        have hlogYp1_pos : 0 < Real.log ((Y T : ℝ) + 1) := by
          apply Real.log_pos
          linarith
        have hexp_le : Real.log m / Real.log ((Y T : ℝ) + 1) ≤
            Real.log T / Real.log ((Y T : ℝ) + 1) :=
          div_le_div_of_nonneg_right hlog_le hlogYp1_pos.le
        have h_pow_le :
            (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
                (Real.log m / Real.log ((Y T : ℝ) + 1)) ≤
            (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
                (Real.log T / Real.log ((Y T : ℝ) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_le
        have h_split' : (m : ℝ) / Nat.totient m ≤
            L T * (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
              (Real.log m / Real.log ((Y T : ℝ) + 1)) := by
          have hh := h_split
          push_cast at hh
          exact hh
        calc (m : ℝ) / Nat.totient m ≤ _ := h_split'
          _ ≤ L T * (((Y T : ℝ) + 1) / (Y T : ℝ)) ^
              (Real.log T / Real.log ((Y T : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left h_pow_le hL_pos.le
          _ = L T * F T := by rfl
      · rw [ciSup_neg hm, Real.sSup_empty]
        have hF_nn : 0 ≤ F T := by
          exact (Real.rpow_pos_of_pos hbase_pos _).le
        exact mul_nonneg hL_pos.le hF_nn
    -- Now S T ≥ L T (using m = primorial Y T as a witness).
    have hS_ge_L : L T ≤ S T := by
      have hY1_real : 1 ≤ Y T := hY1
      -- m_witness = primorial (Y T).
      set m := primorial (Y T) with hm_def
      have hm_pos : 1 ≤ m := primorial_pos (Y T)
      have hm_ratio_eq : (m : ℝ) / Nat.totient m = L T := by
        change (m : ℝ) / Nat.totient m = primeEulerProdNat (Y T)
        exact ratio_totient_primorial (Y T) hY1
      -- m ≤ 4^Y ≤ T.
      have hm_le_4Y : (m : ℝ) ≤ ((4 : ℝ) ^ (Y T)) := by
        exact_mod_cast primorial_le_four_pow (Y T)
      have h4Y_le_T : ((4 : ℝ) ^ (Y T)) ≤ T := four_pow_landauY_le T hT1
      have hm_le_T : (m : ℝ) ≤ T := le_trans hm_le_4Y h4Y_le_T
      have hm_le_floor : m ≤ ⌊T⌋₊ := Nat.le_floor hm_le_T
      have hm_in : m ∈ Set.Icc 1 ⌊T⌋₊ := ⟨hm_pos, hm_le_floor⟩
      have : (m : ℝ) / Nat.totient m ≤ S T := by
        change (m : ℝ) / Nat.totient m ≤ ⨆ m' ∈ Set.Icc 1 ⌊T⌋₊, (m' : ℝ) / Nat.totient m'
        have h_inner_eq :
            (⨆ (_ : m ∈ Set.Icc 1 ⌊T⌋₊),
                (m : ℝ) / Nat.totient m) = (m : ℝ) / Nat.totient m :=
          ciSup_pos hm_in
        rw [← h_inner_eq]
        exact le_ciSup hbdd_inner m
      linarith [hm_ratio_eq]
    have hD_pos : 0 < D T := mul_pos hγc_pos hloglog_pos
    refine ⟨?_, ?_⟩
    · exact div_le_div_of_nonneg_right hS_ge_L hD_pos.le
    · exact div_le_div_of_nonneg_right hS_le_LF hD_pos.le
  -- Apply squeeze.
  have h_lower : ∀ᶠ T : ℝ in atTop, L T / D T ≤ S T / D T :=
    h_bound_ev.mono (fun _ h => h.1)
  have h_upper : ∀ᶠ T : ℝ in atTop, S T / D T ≤ L T * F T / D T :=
    h_bound_ev.mono (fun _ h => h.2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_LD h_UD h_lower h_upper

/- ## Section 2 — The asymptotic formula -/

/-- The maximal totient-fibre ratio at scale `x`. -/
noncomputable def R (x : ℕ) : ℝ :=
  ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
    let mmax := sSup {m | Nat.totient m = n}
    let mmin := sInf {m | Nat.totient m = n}
    (mmax : ℝ) / mmin

/-- **Theorem 2.1 (upper bound).** `R(x) ≤ (e^γ + o(1)) log log x`.

Proof: for `n ≤ x` and `M = f_max(n)`, `m = f_min(n)`, the inequality
`M/m ≤ M/φ(M)` (since `m/φ(m) ≥ 1`) plus fibre-finiteness `M ≤ 2n² ≤ 2x²`
plus Lemma 1.1 give the bound.
-/
theorem R_upper_bound :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≤ (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log x) := by
  intro ε hε_pos
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  have hε2_pos : 0 < ε / 2 := by positivity
  have hδ_pos : 0 < ε / (2 * γc) := by positivity
  -- Step 1: Get eventually-for-real-T bound on S(T) := ⨆ m ∈ Icc 1 ⌊T⌋₊, m/φ(m).
  have h_evlt :
      ∀ᶠ T : ℝ in atTop,
        (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) /
          (γc * Real.log (Real.log T)) ≤ 1 + ε / (2 * γc) := by
    have hone_lt : (1 : ℝ) < 1 + ε / (2 * γc) := by linarith
    exact landau_max_ratio.eventually_le_const hone_lt
  have h_pos_log_log : ∀ᶠ T : ℝ in atTop, 0 < Real.log (Real.log T) := by
    filter_upwards [Filter.eventually_gt_atTop (Real.exp 1)] with T hT
    have hexp_pos : (0:ℝ) < Real.exp 1 := Real.exp_pos _
    have hlogT : 1 < Real.log T := by
      have := Real.log_lt_log hexp_pos hT
      simpa [Real.log_exp] using this
    exact Real.log_pos hlogT
  have h_landau_bound :
      ∀ᶠ T : ℝ in atTop,
        (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) ≤
          (γc + ε/2) * Real.log (Real.log T) := by
    filter_upwards [h_evlt, h_pos_log_log] with T hT_le hT_llog_pos
    have hg_pos : 0 < γc * Real.log (Real.log T) := mul_pos hγc_pos hT_llog_pos
    have hf_le : (⨆ m ∈ Set.Icc 1 ⌊T⌋₊, (m : ℝ) / Nat.totient m) ≤
        (1 + ε / (2 * γc)) * (γc * Real.log (Real.log T)) :=
      (div_le_iff₀ hg_pos).mp hT_le
    have heq : (1 + ε / (2 * γc)) * (γc * Real.log (Real.log T)) =
        (γc + ε/2) * Real.log (Real.log T) := by
      field_simp
    rw [heq] at hf_le
    exact hf_le
  -- Step 2: precompose with T(x) = 2 * x^2.
  have htends_2xsq : Tendsto (fun x : ℕ => (2 : ℝ) * (x : ℝ)^2) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => ((x : ℝ))) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun x : ℕ => ((x : ℝ))^2) atTop atTop :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).comp h1
    exact Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) h2
  have h_landau_at_T :
      ∀ᶠ x : ℕ in atTop,
        (⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m) ≤
          (γc + ε/2) * Real.log (Real.log ((2 : ℝ) * (x : ℝ)^2)) :=
    htends_2xsq.eventually h_landau_bound
  -- Step 3: For x ≥ 2, log log(2x²) ≤ log 4 + log log x.
  have h_loglog_bound :
      ∀ᶠ x : ℕ in atTop,
        Real.log (Real.log ((2 : ℝ) * (x : ℝ)^2)) ≤ Real.log 4 + Real.log (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    have hx_ge_2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hx_pos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le_logx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx_ge_2
    have heq1 : Real.log ((2 : ℝ) * (x : ℝ)^2) = Real.log 2 + 2 * Real.log x := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have hlogargs : Real.log 2 + 2 * Real.log x ≤ 4 * Real.log x := by linarith
    have hlog_inner_pos : 0 < Real.log 2 + 2 * Real.log x := by linarith
    have h_le_log : Real.log (Real.log 2 + 2 * Real.log x) ≤ Real.log (4 * Real.log x) :=
      Real.log_le_log hlog_inner_pos hlogargs
    have heq2 : Real.log (4 * Real.log x) = Real.log 4 + Real.log (Real.log x) := by
      rw [Real.log_mul (by norm_num) hlogx_pos.ne']
    rw [heq1]
    linarith
  -- Step 4: log log x → ∞ as ℕ → ∞.
  have h_loglog_to_inf : Tendsto (fun x : ℕ => Real.log (Real.log x)) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => ((x : ℝ))) atTop atTop := tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)
  -- Step 5: eventually log log x ≥ 2(γc + ε/2)log 4 / ε.
  have h_loglog_large :
      ∀ᶠ x : ℕ in atTop,
        (γc + ε/2) * Real.log 4 ≤ (ε / 2) * Real.log (Real.log x) := by
    -- want eventually log log x ≥ K where K = (γc+ε/2) log 4 * 2 / ε.
    set K : ℝ := (γc + ε/2) * Real.log 4 * 2 / ε
    have hK_eventually : ∀ᶠ x : ℕ in atTop, K ≤ Real.log (Real.log x) :=
      h_loglog_to_inf.eventually_ge_atTop K
    filter_upwards [hK_eventually] with x hxK
    have hε_pos' : (0 : ℝ) < ε := hε_pos
    have hKeq : (γc + ε/2) * Real.log 4 = (ε / 2) * K := by
      change (γc + ε/2) * Real.log 4 = (ε / 2) * ((γc + ε/2) * Real.log 4 * 2 / ε)
      field_simp
    rw [hKeq]
    have hε_half_pos : (0 : ℝ) < ε / 2 := hε2_pos
    exact (mul_le_mul_of_nonneg_left hxK hε_half_pos.le)
  -- Step 6: combine all bounds, plus R x ≤ S(2x²).
  -- R x ≤ S(2x²) — to be proved.
  have h_R_le_S :
      ∀ᶠ x : ℕ in atTop,
        R x ≤ (⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx1
    -- Notation
    set S2x : ℝ := ⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m with hS2x_def
    -- Boundedness for the inner family
    have hfloor_pos : 1 ≤ ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := by
      apply Nat.le_floor
      have hx_pos : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
      have : (1 : ℝ) ≤ (2 : ℝ) * (x : ℝ)^2 := by nlinarith
      exact_mod_cast this
    -- BddAbove for the inner family (m/φ m ≤ m ≤ ⌊2x²⌋₊).
    have hbdd_inner :
        BddAbove (Set.range (fun (m : ℕ) =>
          ⨆ (_ : m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊), (m : ℝ) / Nat.totient m)) := by
      refine ⟨((⌊(2 : ℝ) * (x : ℝ)^2⌋₊ : ℕ) : ℝ), ?_⟩
      rintro _ ⟨m, rfl⟩
      simp only
      by_cases hm : m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊
      · rw [ciSup_pos hm]
        have hφ_pos : 0 < Nat.totient m := Nat.totient_pos.mpr hm.1
        have h_div_le : (m : ℝ) / Nat.totient m ≤ m := by
          rw [div_le_iff₀ (by exact_mod_cast hφ_pos)]
          have h1 : (1 : ℝ) ≤ (Nat.totient m : ℝ) := by exact_mod_cast hφ_pos
          have h2 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast m.zero_le
          nlinarith
        have h_le : (m : ℝ) ≤ ((⌊(2 : ℝ) * (x : ℝ)^2⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm.2
        linarith
      · rw [ciSup_neg hm, Real.sSup_empty]
        exact_mod_cast Nat.zero_le _
    -- S2x ≥ 0 (witness m=1).
    have hS2x_nonneg : 0 ≤ S2x := by
      have h1mem : (1 : ℕ) ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := ⟨le_refl _, hfloor_pos⟩
      have h1_term : (1 : ℝ) / Nat.totient 1 = 1 := by simp
      have h_ge : (1 : ℝ) ≤ S2x := by
        rw [hS2x_def]
        calc
          (1 : ℝ) = (1 : ℝ) / Nat.totient 1 := h1_term.symm
          _ ≤ ⨆ (_ : (1 : ℕ) ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊),
              ((1 : ℕ) : ℝ) / Nat.totient 1 := by
            rw [ciSup_pos h1mem]
            norm_num
          _ ≤ _ := le_ciSup hbdd_inner 1
      linarith
    -- Now R x = iSup over n of inner. Apply ciSup_le for outer (Nonempty ℕ).
    unfold R
    apply ciSup_le
    intro n
    -- Inner: ⨆ (_ : n ∈ S_x), (mmax:ℝ)/mmin where S_x is the predicate set.
    by_cases hmem : n ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}
    · rw [ciSup_pos hmem]
      -- Now compute mmax, mmin and bound mmax/mmin ≤ S2x.
      obtain ⟨hn_in_Icc, m_wit, hφm⟩ := hmem
      -- The set A = {m | φ m = n}.
      set A : Set ℕ := {m | Nat.totient m = n} with hA_def
      have hn_pos : 1 ≤ n := hn_in_Icc.1
      have hn_le_x : n ≤ x := hn_in_Icc.2
      -- m_wit ∈ A. m_wit ≥ 1 since φ m_wit = n ≥ 1 implies m_wit ≥ 1.
      have hm_wit_pos : 1 ≤ m_wit := by
        rcases Nat.eq_zero_or_pos m_wit with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφm
          omega
        · exact hpos
      -- A is nonempty.
      have hA_ne : A.Nonempty := ⟨m_wit, hφm⟩
      -- A is bounded above by 2n².
      have hA_bdd : BddAbove A := by
        refine ⟨2 * n ^ 2, ?_⟩
        intro m hm
        have hm_pos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · have hm' : Nat.totient m = n := hm
            rw [h0, Nat.totient_zero] at hm'
            omega
          · exact hpos
        exact totient_preimage_bound hm_pos hm
      -- mmax := sSup A is in A by Nat.sSup_mem.
      set mmax : ℕ := sSup A with hmmax_def
      have hmmax_in : mmax ∈ A := Nat.sSup_mem hA_ne hA_bdd
      have hφmmax : Nat.totient mmax = n := hmmax_in
      have hmmax_pos : 1 ≤ mmax := by
        rcases Nat.eq_zero_or_pos mmax with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmax
          omega
        · exact hpos
      -- mmax ≤ 2n² ≤ 2x².
      have hmmax_le_2nsq : mmax ≤ 2 * n ^ 2 := totient_preimage_bound hmmax_pos hφmmax
      have hmmax_le_2xsq_R : (mmax : ℝ) ≤ (2 : ℝ) * (x : ℝ)^2 := by
        have h1 : (mmax : ℝ) ≤ (2 * n^2 : ℕ) := by exact_mod_cast hmmax_le_2nsq
        have h2 : ((2 * n^2 : ℕ) : ℝ) ≤ (2 : ℝ) * (x : ℝ)^2 := by
          push_cast
          have hn_le_x_R : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hn_le_x
          have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
          nlinarith
        linarith
      have hmmax_le_floor : mmax ≤ ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := Nat.le_floor hmmax_le_2xsq_R
      have hmmax_in_Icc : mmax ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊ := ⟨hmmax_pos, hmmax_le_floor⟩
      -- mmin := sInf A in A.
      set mmin : ℕ := sInf A with hmmin_def
      have hmmin_in : mmin ∈ A := Nat.sInf_mem hA_ne
      have hφmmin : Nat.totient mmin = n := hmmin_in
      have hmmin_pos : 1 ≤ mmin := by
        rcases Nat.eq_zero_or_pos mmin with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmin
          omega
        · exact hpos
      -- mmin ≥ n (since n = φ mmin ≤ mmin).
      have hmmin_ge_n : n ≤ mmin := by
        have := Nat.totient_le mmin
        rw [hφmmin] at this
        exact this
      -- (mmax:ℝ)/mmin ≤ (mmax:ℝ)/n = (mmax:ℝ)/φ(mmax) ≤ S2x.
      change (mmax : ℝ) / mmin ≤ S2x
      have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have hmmin_pos_R : (0 : ℝ) < mmin := by exact_mod_cast hmmin_pos
      have hmmax_nn_R : (0 : ℝ) ≤ mmax := by exact_mod_cast Nat.zero_le _
      have hmmin_ge_n_R : (n : ℝ) ≤ (mmin : ℝ) := by exact_mod_cast hmmin_ge_n
      have h_div_le : (mmax : ℝ) / mmin ≤ (mmax : ℝ) / n := by
        apply div_le_div_of_nonneg_left hmmax_nn_R hn_pos_R hmmin_ge_n_R
      have h_n_eq : ((n : ℝ)) = (Nat.totient mmax : ℝ) := by exact_mod_cast hφmmax.symm
      rw [h_n_eq] at h_div_le
      have h_term_le_S : (mmax : ℝ) / Nat.totient mmax ≤ S2x := by
        have h_inner_eq :
            (⨆ (_ : mmax ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊),
                (mmax : ℝ) / Nat.totient mmax) = (mmax : ℝ) / Nat.totient mmax :=
          ciSup_pos hmmax_in_Icc
        rw [hS2x_def, ← h_inner_eq]
        exact le_ciSup hbdd_inner mmax
      linarith
    · rw [ciSup_neg hmem]
      rw [Real.sSup_empty]
      exact hS2x_nonneg
  -- Step 7: assemble.
  have hllog_pos_ev : ∀ᶠ x : ℕ in atTop, 0 ≤ Real.log (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with x hx
    have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hexp_lt_three : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have hlog3_lt_logx : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
    have h1 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos _) hexp_lt_three
      simpa [Real.log_exp] using h
    have h2 : 1 ≤ Real.log x := by linarith
    exact (Real.log_nonneg h2)
  filter_upwards [h_landau_at_T, h_loglog_bound, h_loglog_large, h_R_le_S, hllog_pos_ev]
    with x h1 h2 h3 h4 h5
  -- have h1 : S(2x²) ≤ (γc + ε/2) * log log (2x²)
  -- have h2 : log log(2x²) ≤ log 4 + log log x
  -- have h3 : (γc + ε/2) * log 4 ≤ (ε/2) * log log x
  -- have h4 : R x ≤ S(2x²)
  -- have h5 : 0 ≤ log log x
  -- want: R x ≤ (γc + ε) * log log x.
  -- (γc + ε/2)(log 4 + log log x) = (γc + ε/2) log 4 + (γc + ε/2) log log x
  --   ≤ (ε/2) log log x + (γc + ε/2) log log x = (γc + ε) log log x.
  have hγε2_pos : 0 ≤ γc + ε / 2 := by linarith
  calc R x
      ≤ (⨆ m ∈ Set.Icc 1 ⌊(2 : ℝ) * (x : ℝ)^2⌋₊, (m : ℝ) / Nat.totient m) := h4
    _ ≤ (γc + ε/2) * Real.log (Real.log ((2 : ℝ) * (x : ℝ)^2)) := h1
    _ ≤ (γc + ε/2) * (Real.log 4 + Real.log (Real.log x)) :=
        mul_le_mul_of_nonneg_left h2 hγε2_pos
    _ = (γc + ε/2) * Real.log 4 + (γc + ε/2) * Real.log (Real.log x) := by ring
    _ ≤ (ε/2) * Real.log (Real.log x) + (γc + ε/2) * Real.log (Real.log x) := by linarith
    _ = (γc + ε) * Real.log (Real.log x) := by ring

/- **Theorem 2.1 (lower bound).** `R(x) ≥ (e^γ + o(1)) log log x`.

The formal proof uses Linnik with modulus `A_Y * P_Y`, giving a prime `ℓ`
with `A_Y * P_Y ∣ ℓ - 1`. In particular `A_Y ∣ ℓ - 1`, so the construction
`U_Y = (ℓ - 1)/A_Y`, `Q_Y = ∏_{q | U_Y, Y < q} q`, `a_Y = ℓ Q_Y`,
`b_Y = P_Y U_Y Q_Y` works.

The deterministic part proves:
`φ(a_Y) = φ(b_Y)`,
`b_Y/a_Y = primeEulerProdNat Y · (ℓ - 1)/ℓ`, and
`n_Y ≤ A_Y · ℓ²`.

For height control, the proof avoids PNT/theta and uses
`A_Y ≤ P_Y ≤ 4^Y`, hence `n_Y ≤ exp(K·Y)` for a constant `K`.
Taking `Y = ⌊log x / (2K)⌋` gives `n_Y ≤ x` eventually and
`log Y = log log x + O(1)`.
-/
/- ## Lower-bound construction (Phase 1+2: foundations)

This namespace builds the deterministic ingredients for the totient-collision
construction, deferring all asymptotic content to later phases. The deterministic
phase (Phases 1-6) is independent of `mertens_product`, `linnik_dvd`, and any
external theorem; it is pure prime-factor bookkeeping. The asymptotic wrapper at
the end of the namespace consumes both shared inputs.
-/

namespace LowerConstruction

open Filter
open scoped BigOperators Nat

/-- Primes up to `Y`. -/
noncomputable def smallPrimes (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter Nat.Prime

/-- `P_Y = ∏_{p≤Y} p`. -/
noncomputable def P (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, p

/-- `A_Y = ∏_{p≤Y} (p - 1)`. -/
noncomputable def A (Y : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes Y, (p - 1)

/-- Large prime factors of `U`, namely those above `Y`. -/
noncomputable def largeFactors (Y U : ℕ) : Finset ℕ :=
  U.primeFactors.filter fun q => Y < q

/-- `Q_Y(U) = ∏_{q | U, q > Y} q`. -/
noncomputable def Q (Y U : ℕ) : ℕ :=
  ∏ q ∈ largeFactors Y U, q

lemma A_pos (Y : ℕ) : 0 < A Y := by
  unfold A
  refine Finset.prod_pos ?_
  intro p hp
  rw [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  have h2 : 2 ≤ p := hpprime.two_le
  omega

lemma P_pos (Y : ℕ) : 0 < P Y := by
  unfold P
  refine Finset.prod_pos ?_
  intro p hp
  rw [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  exact hpprime.pos

lemma Q_pos (Y U : ℕ) : 0 < Q Y U := by
  unfold Q
  refine Finset.prod_pos ?_
  intro q hq
  rw [largeFactors] at hq
  rcases Finset.mem_filter.mp hq with ⟨hqU, _⟩
  exact (Nat.prime_of_mem_primeFactors hqU).pos

lemma A_le_P (Y : ℕ) : A Y ≤ P Y := by
  unfold A P
  refine Finset.prod_le_prod ?_ ?_
  · intro p hp
    rw [smallPrimes] at hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
    have h2 : 2 ≤ p := hpprime.two_le
    omega
  · intro p _
    omega

lemma P_eq_primorial (Y : ℕ) : P Y = primorial Y := by
  unfold P smallPrimes primorial
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hpY⟩, hpprime⟩
      exact ⟨by omega, hpprime⟩
    · rintro ⟨hpY, hpprime⟩
      have h1 : 1 ≤ p := hpprime.one_le
      exact ⟨⟨h1, by omega⟩, hpprime⟩
  · intros
    rfl

lemma P_le_four_pow (Y : ℕ) : P Y ≤ 4 ^ Y := by
  rw [P_eq_primorial]
  exact primorial_le_four_pow Y

lemma A_le_four_pow (Y : ℕ) : A Y ≤ 4 ^ Y :=
  (A_le_P Y).trans (P_le_four_pow Y)

/-- `Q Y U` divides `U`, since it is a product of distinct prime factors of `U`. -/
lemma Q_dvd_U (Y U : ℕ) (_hU : U ≠ 0) : Q Y U ∣ U := by
  unfold Q largeFactors
  -- Q = ∏ q ∈ U.primeFactors.filter (Y < ·), q.
  -- This divides ∏ q ∈ U.primeFactors, q, which divides U.
  refine dvd_trans ?_ (Nat.prod_primeFactors_dvd U)
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

/-- If `0 < U < ℓ` and `ℓ` is prime, then `ℓ` is NOT a prime factor of `U`. -/
lemma ell_not_mem_largeFactors {Y U ℓ : ℕ} (_hℓ : Nat.Prime ℓ) (hU_pos : 0 < U)
    (hU_lt : U < ℓ) : ℓ ∉ largeFactors Y U := by
  intro hmem
  have h1 : ℓ ∈ U.primeFactors := (Finset.mem_filter.mp hmem).1
  have h2 : ℓ ∣ U := Nat.dvd_of_mem_primeFactors h1
  have h3 : ℓ ≤ U := Nat.le_of_dvd hU_pos h2
  exact (lt_irrefl _) (h3.trans_lt hU_lt)

/-- The prime factors of `Q Y U` are exactly `largeFactors Y U`. -/
lemma primeFactors_Q (Y U : ℕ) (_hU : U ≠ 0) :
    (Q Y U).primeFactors = largeFactors Y U := by
  unfold Q
  apply Nat.primeFactors_prod
  intro q hq
  rw [largeFactors] at hq
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1

/-- The prime factors of `P Y` are exactly `smallPrimes Y`. -/
lemma primeFactors_P (Y : ℕ) :
    (P Y).primeFactors = smallPrimes Y := by
  unfold P
  apply Nat.primeFactors_prod
  intro p hp
  rw [smallPrimes] at hp
  exact (Finset.mem_filter.mp hp).2

/-- The prime factors of `ℓ * Q Y U` (when `ℓ` is prime, `0 < U < ℓ`) are exactly
`{ℓ} ∪ largeFactors Y U`. -/
lemma primeFactors_a (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U) (_hU_lt : U < ℓ) :
    (ℓ * Q Y U).primeFactors = insert ℓ (largeFactors Y U) := by
  have hU_ne : U ≠ 0 := Nat.pos_iff_ne_zero.mp hU_pos
  have hQ_ne : Q Y U ≠ 0 := Nat.pos_iff_ne_zero.mp (Q_pos Y U)
  rw [Nat.primeFactors_mul hℓ.ne_zero hQ_ne, hℓ.primeFactors,
    primeFactors_Q Y U hU_ne]
  ext r
  simp [Finset.mem_insert]

/-- The prime factors of `P Y * U * Q Y U` are exactly `smallPrimes Y ∪ largeFactors Y U`,
provided `U > 0` and `Q Y U` divides `U`. -/
lemma primeFactors_b (Y U : ℕ) (hU_pos : 0 < U) (_hU_dvd : Q Y U ∣ U) :
    (P Y * U * Q Y U).primeFactors = smallPrimes Y ∪ largeFactors Y U := by
  have hU_ne : U ≠ 0 := Nat.pos_iff_ne_zero.mp hU_pos
  have hP_ne : P Y ≠ 0 := Nat.pos_iff_ne_zero.mp (P_pos Y)
  have hQ_ne : Q Y U ≠ 0 := Nat.pos_iff_ne_zero.mp (Q_pos Y U)
  have hPU_ne : P Y * U ≠ 0 := mul_ne_zero hP_ne hU_ne
  rw [Nat.primeFactors_mul hPU_ne hQ_ne, Nat.primeFactors_mul hP_ne hU_ne,
    primeFactors_P, primeFactors_Q Y U hU_ne]
  ext r
  simp only [Finset.mem_union]
  constructor
  · rintro ((hr | hr) | hr)
    · exact Or.inl hr
    · -- r ∈ U.primeFactors. Case on r ≤ Y or r > Y.
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrU : r ∣ U := Nat.dvd_of_mem_primeFactors hr
      by_cases hY : Y < r
      · refine Or.inr ?_
        rw [largeFactors]
        exact Finset.mem_filter.mpr ⟨hr, hY⟩
      · refine Or.inl ?_
        rw [smallPrimes]
        push Not at hY
        have h1 : 1 ≤ r := hrp.one_le
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hY⟩, hrp⟩
    · exact Or.inr hr
  · rintro (hr | hr)
    · exact Or.inl (Or.inl hr)
    · exact Or.inr hr

/-- The bridge to `mertens_product`: `(P Y : ℝ) / A Y` equals the
`primeEulerProdNat Y` defined in `Erdos694Scratch`. -/
lemma P_div_A_eq_primeEulerProdNat (Y : ℕ) :
    (P Y : ℝ) / (A Y : ℝ) = primeEulerProdNat Y := by
  unfold P A primeEulerProdNat
  rw [show ((Finset.Icc 1 Y).filter Nat.Prime) = smallPrimes Y from rfl]
  rw [Nat.cast_prod, Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [smallPrimes] at hp
  rcases Finset.mem_filter.mp hp with ⟨_, hpprime⟩
  have h1 : 1 ≤ p := hpprime.one_le
  rw [Nat.cast_sub h1]
  push_cast
  rfl

/-! ### Phase 4: Totient equalities for the construction -/

/-- `smallPrimes Y` and `largeFactors Y U` are disjoint, since one consists of primes `≤ Y`
and the other of primes `> Y`. -/
lemma smallPrimes_disjoint_largeFactors (Y U : ℕ) :
    Disjoint (smallPrimes Y) (largeFactors Y U) := by
  rw [Finset.disjoint_left]
  intro p hp_small hp_large
  rw [smallPrimes, Finset.mem_filter, Finset.mem_Icc] at hp_small
  rw [largeFactors, Finset.mem_filter] at hp_large
  have h1 : p ≤ Y := hp_small.1.2
  have h2 : Y < p := hp_large.2
  omega

/-- The product of primes in `largeFactors Y U` equals `Q Y U`. -/
lemma prod_largeFactors_eq_Q (Y U : ℕ) :
    ∏ q ∈ largeFactors Y U, q = Q Y U := rfl

/-- The product of primes in `smallPrimes Y` equals `P Y`. -/
lemma prod_smallPrimes_eq_P (Y : ℕ) :
    ∏ p ∈ smallPrimes Y, p = P Y := rfl

/-- The product of `(p - 1)` over `smallPrimes Y` equals `A Y`. -/
lemma prod_smallPrimes_sub_one_eq_A (Y : ℕ) :
    ∏ p ∈ smallPrimes Y, (p - 1) = A Y := rfl

/-- `φ(ℓ · Q) = (ℓ - 1) · ∏_{q ∈ largeFactors Y U} (q - 1)`. -/
lemma totient_a_eq (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U) (hU_lt : U < ℓ)
    (_hQ_dvd : Q Y U ∣ U) :
    (Nat.totient (ℓ * Q Y U) : ℕ) =
      (ℓ - 1) * ∏ q ∈ largeFactors Y U, (q - 1) := by
  have hℓ_ne : ℓ ≠ 0 := hℓ.ne_zero
  have hQ_ne : Q Y U ≠ 0 := (Q_pos Y U).ne'
  have hN_ne : ℓ * Q Y U ≠ 0 := mul_ne_zero hℓ_ne hQ_ne
  -- Key formula: φ(N) * ∏ p = N * ∏ (p - 1).
  have hkey := Nat.totient_mul_prod_primeFactors (ℓ * Q Y U)
  rw [primeFactors_a Y U ℓ hℓ hU_pos hU_lt] at hkey
  have hℓ_notin : ℓ ∉ largeFactors Y U := ell_not_mem_largeFactors hℓ hU_pos hU_lt
  rw [Finset.prod_insert hℓ_notin, Finset.prod_insert hℓ_notin] at hkey
  -- ∏_{p ∈ insert ℓ S} p = ℓ * ∏ q = ℓ * Q
  -- Now: φ(ℓ Q) * (ℓ * ∏q) = (ℓ * Q) * ((ℓ - 1) * ∏ (q - 1))
  -- The left side product ∏ q over largeFactors equals Q.
  rw [prod_largeFactors_eq_Q] at hkey
  -- hkey : φ(ℓ Q) * (ℓ * Q) = (ℓ * Q) * ((ℓ - 1) * ∏ (q - 1))
  have hN_pos : 0 < ℓ * Q Y U := Nat.pos_of_ne_zero hN_ne
  have : (ℓ * Q Y U) * Nat.totient (ℓ * Q Y U) =
      (ℓ * Q Y U) * ((ℓ - 1) * ∏ q ∈ largeFactors Y U, (q - 1)) := by
    rw [mul_comm (ℓ * Q Y U) (Nat.totient (ℓ * Q Y U))]
    convert hkey using 1
  exact Nat.eq_of_mul_eq_mul_left hN_pos this

/-- For the construction, `φ(P_Y · U · Q_Y(U)) = A_Y · U · ∏_{q ∈ largeFactors} (q - 1)`. -/
lemma totient_b_eq_under_construction (Y U ℓ : ℕ) (_hℓ : Nat.Prime ℓ)
    (hU_pos : 0 < U) (_hU_lt : U < ℓ)
    (_hAU : A Y * U = ℓ - 1) :
    (Nat.totient (P Y * U * Q Y U) : ℕ) =
      A Y * U * ∏ q ∈ largeFactors Y U, (q - 1) := by
  have hP_ne : P Y ≠ 0 := (P_pos Y).ne'
  have hU_ne : U ≠ 0 := hU_pos.ne'
  have hQ_ne : Q Y U ≠ 0 := (Q_pos Y U).ne'
  have hQ_dvd : Q Y U ∣ U := Q_dvd_U Y U hU_ne
  have hPU_ne : P Y * U ≠ 0 := mul_ne_zero hP_ne hU_ne
  have hN_ne : P Y * U * Q Y U ≠ 0 := mul_ne_zero hPU_ne hQ_ne
  have hN_pos : 0 < P Y * U * Q Y U := Nat.pos_of_ne_zero hN_ne
  -- Key formula: φ(N) * ∏ p = N * ∏ (p - 1) where the products are over N.primeFactors.
  have hkey := Nat.totient_mul_prod_primeFactors (P Y * U * Q Y U)
  rw [primeFactors_b Y U hU_pos hQ_dvd] at hkey
  have hdisj : Disjoint (smallPrimes Y) (largeFactors Y U) :=
    smallPrimes_disjoint_largeFactors Y U
  rw [Finset.prod_union hdisj, Finset.prod_union hdisj] at hkey
  -- hkey : φ(N) * (P Y * Q Y U) = N * (A Y * ∏ (q-1))
  rw [prod_smallPrimes_eq_P, prod_largeFactors_eq_Q,
      prod_smallPrimes_sub_one_eq_A] at hkey
  -- hkey : φ(N) * (P Y * Q Y U) = (P Y * U * Q Y U) * (A Y * ∏ (q - 1))
  -- We want: φ(N) = A Y * U * ∏ (q - 1).
  -- Multiply target by (P Y * Q Y U): A Y * U * ∏ (q-1) * (P Y * Q Y U) =
  -- (P Y * U * Q Y U) * (A Y * ∏ (q-1)). Same as hkey RHS.
  have hPQ_pos : 0 < P Y * Q Y U := Nat.mul_pos (P_pos Y) (Q_pos Y U)
  have hcancel :
      Nat.totient (P Y * U * Q Y U) * (P Y * Q Y U) =
        (A Y * U * ∏ q ∈ largeFactors Y U, (q - 1)) * (P Y * Q Y U) := by
    rw [hkey]
    ring
  exact Nat.eq_of_mul_eq_mul_right hPQ_pos hcancel

/-- The crucial collision: `φ(ℓ · Q) = φ(P_Y · U · Q)` for the construction. -/
lemma totient_a_eq_totient_b (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (hU_pos : 0 < U) (hU_lt : U < ℓ) (hAU : A Y * U = ℓ - 1) :
    Nat.totient (ℓ * Q Y U) = Nat.totient (P Y * U * Q Y U) := by
  have hU_ne : U ≠ 0 := hU_pos.ne'
  rw [totient_a_eq Y U ℓ hℓ hU_pos hU_lt (Q_dvd_U Y U hU_ne),
      totient_b_eq_under_construction Y U ℓ hℓ hU_pos hU_lt hAU, ← hAU]

/-! ### Phase 5: Ratio identity -/

/-- `b/a = (P_Y/A_Y) · ((ℓ-1)/ℓ)` for the construction. -/
lemma collision_ratio (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U)
    (_hU_lt : U < ℓ) (hAU : A Y * U = ℓ - 1) :
    ((P Y * U * Q Y U : ℕ) : ℝ) / ((ℓ * Q Y U : ℕ) : ℝ) =
      primeEulerProdNat Y * ((ℓ - 1 : ℝ) / ℓ) := by
  have hℓ_pos : 0 < ℓ := hℓ.pos
  have hQ_pos : 0 < Q Y U := Q_pos Y U
  have hA_pos : 0 < A Y := A_pos Y
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ_pos.ne'
  have hQR : (Q Y U : ℝ) ≠ 0 := by exact_mod_cast hQ_pos.ne'
  have hAR : (A Y : ℝ) ≠ 0 := by exact_mod_cast hA_pos.ne'
  -- Cast (ℓ - 1) using the Nat subtraction-vs-ℝ bridge.
  have hℓ_one : 1 ≤ ℓ := hℓ.one_le
  have hℓm1_cast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub hℓ_one]
    norm_num
  -- (P Y * U * Q Y U : ℝ) / (ℓ * Q Y U : ℝ) = (P Y * U) / ℓ.
  push_cast
  have step1 : ((P Y : ℝ) * U * Q Y U) / ((ℓ : ℝ) * Q Y U) =
      ((P Y : ℝ) * U) / (ℓ : ℝ) := by
    field_simp
  rw [step1]
  -- Use A Y * U = ℓ - 1 in ℝ: cast.
  have hAU_R : (A Y : ℝ) * (U : ℝ) = (ℓ : ℝ) - 1 := by
    rw [← hℓm1_cast, ← Nat.cast_mul]
    exact_mod_cast hAU
  -- So U = (ℓ - 1) / A Y in ℝ.
  have hU_R : (U : ℝ) = ((ℓ : ℝ) - 1) / (A Y : ℝ) := by
    field_simp
    linarith [hAU_R]
  rw [hU_R]
  -- Now LHS = P Y * ((ℓ - 1) / A Y) / ℓ = (P Y / A Y) * ((ℓ - 1) / ℓ).
  rw [← P_div_A_eq_primeEulerProdNat]
  field_simp

/-! ### Phase 6: Crude size bound -/

/-- The constructed totient value is bounded: `φ(ℓ · Q) ≤ A_Y · U²`. -/
lemma collision_n_le_A_mul_U_sq (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U)
    (hU_lt : U < ℓ) (hAU : A Y * U = ℓ - 1) :
    Nat.totient (ℓ * Q Y U) ≤ A Y * U * U := by
  have hU_ne : U ≠ 0 := hU_pos.ne'
  have hQ_dvd : Q Y U ∣ U := Q_dvd_U Y U hU_ne
  rw [totient_a_eq Y U ℓ hℓ hU_pos hU_lt hQ_dvd, ← hAU]
  -- (A Y * U) * ∏ (q - 1) ≤ A Y * U * U
  -- Suffices: ∏ (q - 1) ≤ U.
  have hprod_le_Q : ∏ q ∈ largeFactors Y U, (q - 1) ≤ Q Y U := by
    unfold Q
    refine Finset.prod_le_prod (fun q _ => Nat.zero_le _) ?_
    intro q _
    omega
  have hQ_le_U : Q Y U ≤ U := Nat.le_of_dvd hU_pos hQ_dvd
  have hprod_le_U : ∏ q ∈ largeFactors Y U, (q - 1) ≤ U :=
    le_trans hprod_le_Q hQ_le_U
  calc A Y * U * ∏ q ∈ largeFactors Y U, (q - 1)
      ≤ A Y * U * U := Nat.mul_le_mul_left _ hprod_le_U

/-- The constructed totient value is bounded by `A_Y · ℓ²`. -/
lemma collision_n_le_A_mul_ell_sq (Y U ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hU_pos : 0 < U)
    (hU_lt : U < ℓ) (hAU : A Y * U = ℓ - 1) :
    Nat.totient (ℓ * Q Y U) ≤ A Y * (ℓ * ℓ) := by
  have h1 := collision_n_le_A_mul_U_sq Y U ℓ hℓ hU_pos hU_lt hAU
  have hU_le_ℓ : U ≤ ℓ := hU_lt.le
  calc Nat.totient (ℓ * Q Y U)
      ≤ A Y * U * U := h1
    _ ≤ A Y * ℓ * ℓ := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left _ hU_le_ℓ) hU_le_ℓ
    _ = A Y * (ℓ * ℓ) := by ring

end LowerConstruction

/-! ### Helper lemmas for `collision_at_height` -/

/-- Mertens product, lifted along `ℕ → ℝ` (in terms of `primeEulerProdNat`). -/
private lemma mertens_product_nat :
    Tendsto
      (fun Y : ℕ =>
        (primeEulerProdNat Y) /
          (Real.exp Real.eulerMascheroniConstant * Real.log (Y : ℝ)))
      atTop (𝓝 1) := by
  have h_yT_to_inf : Tendsto (fun Y : ℕ => ((Y : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := _root_.mertens_product.comp h_yT_to_inf
  have h_eq : ∀ᶠ Y : ℕ in atTop,
      (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊((Y : ℕ) : ℝ)⌋₊),
            ((p : ℝ) / (p - 1))) /
          (Real.exp Real.eulerMascheroniConstant * Real.log ((Y : ℕ) : ℝ)) =
        (primeEulerProdNat Y) /
          (Real.exp Real.eulerMascheroniConstant * Real.log (Y : ℝ)) := by
    filter_upwards with Y
    have hfloor : ⌊((Y : ℕ) : ℝ)⌋₊ = Y := Nat.floor_natCast Y
    rw [hfloor]
    rfl
  exact h.congr' h_eq

/-- `LowerConstruction.P` tends to infinity as `Y → ∞`. -/
private lemma lc_P_atTop : Tendsto (fun Y : ℕ => LowerConstruction.P Y) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro M
  obtain ⟨p, hpM, hp_prime⟩ := Nat.exists_infinite_primes M
  refine ⟨p, fun Y hY => ?_⟩
  -- For Y ≥ p, P Y = primorial Y ≥ primorial p ≥ p ≥ M.
  rw [LowerConstruction.P_eq_primorial]
  -- primorial is monotone in Y.
  have h_mono : primorial p ≤ primorial Y := by
    unfold primorial
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro q hq
      rw [Finset.mem_filter] at hq ⊢
      refine ⟨?_, hq.2⟩
      have hq_lt : q < p + 1 := Finset.mem_range.mp hq.1
      exact Finset.mem_range.mpr (by omega)
    · intros q hq _
      rw [Finset.mem_filter] at hq
      exact hq.2.one_le
  -- p ≤ primorial p (since p ∈ filter Prime (range (p+1))).
  have h_p_le : p ≤ primorial p := by
    unfold primorial
    have hp_mem : p ∈ Finset.filter Nat.Prime (Finset.range (p + 1)) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_self p), hp_prime⟩
    have h_prod_singleton : p = ∏ x ∈ ({p} : Finset ℕ), id x := by simp
    calc p = ∏ x ∈ ({p} : Finset ℕ), id x := h_prod_singleton
      _ ≤ ∏ x ∈ Finset.filter Nat.Prime (Finset.range (p + 1)), id x := by
          refine Finset.prod_le_prod_of_subset_of_one_le'
            (Finset.singleton_subset_iff.mpr hp_mem) ?_
          intros q hq _
          rw [Finset.mem_filter] at hq
          exact hq.2.one_le
      _ = ∏ x ∈ Finset.filter Nat.Prime (Finset.range (p + 1)), x := by
          simp
  linarith

/-- Size bound for the construction: `n ≤ exp((2 log C + (4L+1) log 4 + 1) · Y)`. -/
private lemma collision_size_bound (Y U ℓ : ℕ) (C : ℝ) (L : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hℓ_prime : Nat.Prime ℓ) (hU_pos : 0 < U) (hU_lt_ℓ : U < ℓ)
    (hAU : LowerConstruction.A Y * U = ℓ - 1)
    (hℓ_le : (ℓ : ℝ) ≤ C * ((LowerConstruction.A Y * LowerConstruction.P Y : ℕ) : ℝ) ^ L)
    (hY1 : 1 ≤ Y) :
    (Nat.totient (ℓ * LowerConstruction.Q Y U) : ℝ) ≤
      Real.exp ((2 * Real.log C + (4 * L + 1) * Real.log 4 + 1) * Y) := by
  classical
  set K : ℝ := 2 * Real.log C + (4 * L + 1) * Real.log 4 + 1 with hK_def
  have hℓ_pos : 0 < ℓ := hℓ_prime.pos
  have hA_pos : 0 < LowerConstruction.A Y := LowerConstruction.A_pos Y
  have hP_pos : 0 < LowerConstruction.P Y := LowerConstruction.P_pos Y
  -- Step 1: φ(ℓ Q) ≤ A Y · ℓ².
  have h_n_le : Nat.totient (ℓ * LowerConstruction.Q Y U) ≤
      LowerConstruction.A Y * (ℓ * ℓ) :=
    LowerConstruction.collision_n_le_A_mul_ell_sq Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU
  have h_n_le_R :
      (Nat.totient (ℓ * LowerConstruction.Q Y U) : ℝ) ≤
        (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) := by
    have h0 := (Nat.cast_le (α := ℝ)).mpr h_n_le
    push_cast at h0
    linarith [h0]
  -- Step 2: A Y ≤ 4^Y, P Y ≤ 4^Y, in ℝ.
  have hA_le4 : (LowerConstruction.A Y : ℝ) ≤ (4 : ℝ) ^ Y := by
    have := LowerConstruction.A_le_four_pow Y
    have h := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at h
    exact h
  have hP_le4 : (LowerConstruction.P Y : ℝ) ≤ (4 : ℝ) ^ Y := by
    have := LowerConstruction.P_le_four_pow Y
    have h := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at h
    exact h
  have hP_nn : (0 : ℝ) ≤ (LowerConstruction.P Y : ℝ) := by exact_mod_cast Nat.zero_le _
  have h4_pow_pos : (0 : ℝ) < (4 : ℝ) ^ Y := by positivity
  -- A Y * P Y ≤ 4^(2Y).
  have hAP_le : ((LowerConstruction.A Y * LowerConstruction.P Y : ℕ) : ℝ) ≤
      (4 : ℝ) ^ (2 * Y) := by
    push_cast
    calc (LowerConstruction.A Y : ℝ) * (LowerConstruction.P Y : ℝ)
        ≤ (4 : ℝ) ^ Y * (4 : ℝ) ^ Y :=
          mul_le_mul hA_le4 hP_le4 hP_nn (by positivity)
      _ = (4 : ℝ) ^ (Y + Y) := by rw [pow_add]
      _ = (4 : ℝ) ^ (2 * Y) := by ring_nf
  have hAP_nn : (0 : ℝ) ≤ ((LowerConstruction.A Y * LowerConstruction.P Y : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le _
  -- ℓ ≤ C · 4^(2LY).
  have hℓ_le2 : (ℓ : ℝ) ≤ C * ((4 : ℝ) ^ (2 * Y)) ^ L := by
    apply hℓ_le.trans
    apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ C)
    exact pow_le_pow_left₀ hAP_nn hAP_le L
  have h4_pow_id : ((4 : ℝ) ^ (2 * Y)) ^ L = (4 : ℝ) ^ (2 * Y * L) := by
    rw [← pow_mul]
  rw [h4_pow_id] at hℓ_le2
  have hℓ_nn : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast Nat.zero_le _
  -- ℓ² ≤ C² · 4^(4YL).
  have hℓ_sq_le : (ℓ : ℝ) * (ℓ : ℝ) ≤ C ^ 2 * (4 : ℝ) ^ (4 * Y * L) := by
    have h_step : (ℓ : ℝ) * (ℓ : ℝ) ≤
        (C * (4 : ℝ) ^ (2 * Y * L)) * (C * (4 : ℝ) ^ (2 * Y * L)) :=
      mul_le_mul hℓ_le2 hℓ_le2 hℓ_nn (by positivity)
    have h_eq : (C * (4 : ℝ) ^ (2 * Y * L)) * (C * (4 : ℝ) ^ (2 * Y * L)) =
        C ^ 2 * (4 : ℝ) ^ (4 * Y * L) := by
      rw [show (4 * Y * L) = (2 * Y * L) + (2 * Y * L) by ring, pow_add]
      ring
    linarith [h_eq ▸ h_step]
  -- A Y · ℓ² ≤ C² · 4^((4L+1)Y).
  have h_total : (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) ≤
      C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) := by
    have hsq_nn : (0 : ℝ) ≤ (ℓ : ℝ) * (ℓ : ℝ) := mul_nonneg hℓ_nn hℓ_nn
    have h_step1 : (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) ≤
        (4 : ℝ) ^ Y * (C ^ 2 * (4 : ℝ) ^ (4 * Y * L)) := by
      exact mul_le_mul hA_le4 hℓ_sq_le hsq_nn (by positivity)
    have h_eq2 : (4 : ℝ) ^ Y * (C ^ 2 * (4 : ℝ) ^ (4 * Y * L)) =
        C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) := by
      rw [show ((4 * L + 1) * Y) = Y + (4 * Y * L) by ring, pow_add]
      ring
    linarith [h_eq2 ▸ h_step1]
  -- Now bound C² · 4^((4L+1)Y) ≤ exp(K·Y).
  have hC_pos : 0 < C := by linarith
  have hlogC_nn : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h_C2_pos : 0 < C ^ 2 := pow_pos hC_pos 2
  have h_4pow_pos : (0 : ℝ) < (4 : ℝ) ^ ((4 * L + 1) * Y) := by positivity
  have h_lhs_pos : (0 : ℝ) < C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) :=
    mul_pos h_C2_pos h_4pow_pos
  have hL_pos_R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hY_R : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
  have hY_nn : (0 : ℝ) ≤ (Y : ℝ) := by linarith
  have h_log_lhs : Real.log (C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y)) =
      2 * Real.log C + ((4 * L + 1) * Y : ℕ) * Real.log 4 := by
    rw [Real.log_mul h_C2_pos.ne' h_4pow_pos.ne', Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h_KY_ge_log : Real.log (C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y)) ≤ K * Y := by
    rw [h_log_lhs, hK_def]
    push_cast
    -- Want: 2 log C + (4L+1) Y log 4 ≤ (2 log C + (4L+1) log 4 + 1) * Y.
    nlinarith [hlogC_nn, hY_R, hlog4_pos, hL_pos_R,
      mul_nonneg hlogC_nn (by linarith : (0:ℝ) ≤ (Y:ℝ) - 1)]
  -- Combine.
  calc (Nat.totient (ℓ * LowerConstruction.Q Y U) : ℝ)
      ≤ (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) := h_n_le_R
    _ ≤ C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) := h_total
    _ = Real.exp (Real.log (C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y))) :=
        (Real.exp_log h_lhs_pos).symm
    _ ≤ Real.exp (K * Y) := Real.exp_le_exp.mpr h_KY_ge_log

/-- **Auxiliary height theorem — analytic combination of Mertens + a Linnik
hypothesis.**

This theorem is the height-form version of the lower-bound construction. It
takes a Linnik-style prime-existence hypothesis as an *explicit argument* (so
the closed theorem itself does not depend on the shared `linnik_dvd` input —
that input enters only at `totient_collision_construction` below, where this
theorem is instantiated).

Concretely: given absolute constants `C, L ≥ 1` and a Linnik-form input
(existence of a prime `ℓ` with `M ∣ ℓ - 1` and polynomial bound `ℓ ≤ C · M^L`
for every `M ≥ 1`), there exists `K > 0` such that for every sufficiently large
`Y`, the explicit construction `a := ℓ · Q_Y(U)`, `b := P_Y · U · Q_Y(U)` (with
`U := (ℓ - 1) / A_Y` and `ℓ` the Linnik prime for `M = A_Y · P_Y`) yields a
totient collision with the right ratio and `n ≤ exp(K · Y)`.

The proof packages the analytic combination (Mertens product asymptotic on
`(P_Y / A_Y) · ((ℓ-1)/ℓ)`, plus the size bound `A_Y ≤ 4^Y` and
`ℓ ≤ C · (A_Y P_Y)^L ≤ C · 16^(LY)`) into a single height-level statement,
leaving the rescaling to `x` to be done in pure Lean below.

Trust boundary: depends on `mertens_product` only (the Linnik input is taken
as an explicit hypothesis rather than from the shared declaration). -/
theorem collision_at_height :
    ∀ (C : ℝ) (L : ℕ), 1 ≤ C → 1 ≤ L →
      (∀ M : ℕ, 1 ≤ M →
        ∃ ℓ : ℕ, Nat.Prime ℓ ∧ M ∣ ℓ - 1 ∧ (ℓ : ℝ) ≤ C * (M : ℝ) ^ L) →
      ∀ ε : ℝ, 0 < ε →
        ∃ K : ℝ, 0 < K ∧
          ∀ᶠ Y : ℕ in atTop,
            ∃ a b n : ℕ,
              1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧
              Nat.totient a = n ∧ Nat.totient b = n ∧
              (b : ℝ) / a ≥
                (Real.exp Real.eulerMascheroniConstant - ε) * Real.log Y ∧
              (n : ℝ) ≤ Real.exp (K * Y) := by
  intro C L hC hL hLinnik ε hε
  classical
  -- Set K := 2 log C + (4L+1) log 4 + 1.
  set K : ℝ := 2 * Real.log C + (4 * L + 1) * Real.log 4 + 1 with hK_def
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogC_nn : 0 ≤ Real.log C := Real.log_nonneg hC
  have hL_pos_R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hK_pos : 0 < K := by
    have h2 : 0 < (4 * (L : ℝ) + 1) * Real.log 4 :=
      mul_pos (by linarith) hlog4_pos
    linarith
  refine ⟨K, hK_pos, ?_⟩
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  -- Helper: build the collision triple with size bound.
  -- The construction is the same in both cases; only the ratio bound differs.
  -- For each Y ≥ 1, given the Linnik input, we extract (ℓ, U) and pack the triple.
  -- We prove the conclusion in two cases on γc vs ε.
  by_cases hcase : γc ≤ ε
  · -- Easy case: (γc - ε) log Y ≤ 0, any nonneg ratio works.
    filter_upwards [Filter.eventually_ge_atTop 1] with Y hY1
    have hAP_pos : 1 ≤ LowerConstruction.A Y * LowerConstruction.P Y :=
      Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (LowerConstruction.A_pos Y).ne' (LowerConstruction.P_pos Y).ne')
    obtain ⟨ℓ, hℓ_prime, hℓ_dvd, hℓ_le⟩ :=
      hLinnik (LowerConstruction.A Y * LowerConstruction.P Y) hAP_pos
    have hℓ_pos : 0 < ℓ := hℓ_prime.pos
    have hℓ_two : 2 ≤ ℓ := hℓ_prime.two_le
    have hA_dvd : LowerConstruction.A Y ∣ ℓ - 1 :=
      dvd_trans ⟨LowerConstruction.P Y, rfl⟩ hℓ_dvd
    have hA_pos : 0 < LowerConstruction.A Y := LowerConstruction.A_pos Y
    have hP_pos : 0 < LowerConstruction.P Y := LowerConstruction.P_pos Y
    set U : ℕ := (ℓ - 1) / LowerConstruction.A Y with hU_def
    have hAU : LowerConstruction.A Y * U = ℓ - 1 := by
      rw [hU_def]
      exact Nat.mul_div_cancel' hA_dvd
    have hP_dvd_U : LowerConstruction.P Y ∣ U := by
      have h1 : LowerConstruction.A Y * LowerConstruction.P Y ∣ LowerConstruction.A Y * U := by
        rw [hAU]
        exact hℓ_dvd
      exact (Nat.mul_dvd_mul_iff_left hA_pos).mp h1
    have hU_pos : 0 < U := Nat.pos_of_ne_zero fun h => by
      have hℓm1_zero : ℓ - 1 = 0 := by rw [← hAU, h, Nat.mul_zero]
      have hℓ_le_one : ℓ ≤ 1 := by omega
      exact (Nat.lt_irrefl 1) (lt_of_lt_of_le hℓ_prime.one_lt hℓ_le_one)
    have hU_lt_ℓ : U < ℓ := by
      have hA_ge_1 : 1 ≤ LowerConstruction.A Y := hA_pos
      have h1 : U ≤ LowerConstruction.A Y * U := Nat.le_mul_of_pos_left _ hA_ge_1
      omega
    refine ⟨ℓ * LowerConstruction.Q Y U, LowerConstruction.P Y * U * LowerConstruction.Q Y U,
        Nat.totient (ℓ * LowerConstruction.Q Y U),
        ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero hℓ_prime.ne_zero (LowerConstruction.Q_pos Y U).ne')
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero hP_pos.ne' hU_pos.ne') (LowerConstruction.Q_pos Y U).ne')
    · have hpos : 0 < ℓ * LowerConstruction.Q Y U :=
        Nat.mul_pos hℓ_pos (LowerConstruction.Q_pos Y U)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hpos).ne'
    · exact (LowerConstruction.totient_a_eq_totient_b Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU).symm
    · -- ratio nonneg ≥ (γc - ε) log Y (which is ≤ 0).
      have hℓQ_pos : 0 < ℓ * LowerConstruction.Q Y U :=
        Nat.mul_pos hℓ_pos (LowerConstruction.Q_pos Y U)
      have hℓQR_pos : (0 : ℝ) < ((ℓ * LowerConstruction.Q Y U : ℕ) : ℝ) :=
        by exact_mod_cast hℓQ_pos
      have hPUQR_nn : (0 : ℝ) ≤ ((LowerConstruction.P Y * U * LowerConstruction.Q Y U : ℕ) : ℝ) :=
        by exact_mod_cast Nat.zero_le _
      have h_ratio_nn :
          0 ≤ ((LowerConstruction.P Y * U * LowerConstruction.Q Y U : ℕ) : ℝ) /
              ((ℓ * LowerConstruction.Q Y U : ℕ) : ℝ) :=
        div_nonneg hPUQR_nn hℓQR_pos.le
      have hYR_nn : (0 : ℝ) ≤ Real.log (Y : ℝ) := by
        have : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
        exact Real.log_nonneg this
      have h_rhs_nonpos : (γc - ε) * Real.log (Y : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hYR_nn
      linarith
    · exact collision_size_bound Y U ℓ C L hC hL hℓ_prime hU_pos hU_lt_ℓ hAU hℓ_le hY1
  · -- Main case: γc > ε. Use Mertens to get the ratio bound.
    push Not at hcase
    have hγc_eps_pos : 0 < γc - ε := by linarith
    have hε2_pos : 0 < ε / 2 := by linarith
    have hγc_eps2_pos : 0 < γc - ε / 2 := by linarith
    -- From Mertens: primeEulerProdNat Y ≥ (γc - ε/2) log Y eventually.
    -- Strategy: ratio (ppN / γc·logY) → 1, so eventually ratio ≥ (γc - ε/2) / γc.
    have h_thresh1_lt : (γc - ε / 2) / γc < 1 := by
      rw [div_lt_one hγc_pos]
      linarith
    have h_mertens_ge :
        ∀ᶠ Y : ℕ in atTop,
          (γc - ε / 2) / γc ≤
            (primeEulerProdNat Y) /
              (Real.exp Real.eulerMascheroniConstant * Real.log (Y : ℝ)) := by
      -- ratio → 1 > (γc - ε/2) / γc, so eventually ratio ≥ (γc - ε/2)/γc.
      have h_lt : (γc - ε / 2) / γc < 1 := h_thresh1_lt
      exact mertens_product_nat.eventually_const_le h_lt
    have h_logY_pos : ∀ᶠ Y : ℕ in atTop, 0 < Real.log (Y : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with Y hY2
      have : (1 : ℝ) < (Y : ℝ) := by exact_mod_cast hY2
      exact Real.log_pos this
    have h_prime_ge : ∀ᶠ Y : ℕ in atTop,
        (γc - ε / 2) * Real.log (Y : ℝ) ≤ primeEulerProdNat Y := by
      filter_upwards [h_mertens_ge, h_logY_pos] with Y hmer hlogY
      have hγc_logY_pos : 0 < γc * Real.log (Y : ℝ) := mul_pos hγc_pos hlogY
      -- hmer: (γc - ε/2)/γc ≤ ppN/(γc·logY).
      -- Multiply both sides by γc·logY > 0.
      have h1 := mul_le_mul_of_nonneg_right hmer hγc_logY_pos.le
      have h_lhs_eq : (γc - ε / 2) / γc * (γc * Real.log (Y : ℝ)) =
          (γc - ε / 2) * Real.log (Y : ℝ) := by
        field_simp
      have h_rhs_eq :
          primeEulerProdNat Y / (γc * Real.log (Y : ℝ)) *
            (γc * Real.log (Y : ℝ)) = primeEulerProdNat Y := by
        field_simp
      -- combine
      have : (γc - ε / 2) * Real.log (Y : ℝ) ≤ primeEulerProdNat Y := by
        rw [← h_lhs_eq, ← h_rhs_eq]
        exact h1
      exact this
    -- Now bound (ℓ-1)/ℓ ≥ rat := (γc - ε)/(γc - ε/2). For this we need ℓ ≥ M₀.
    set rat : ℝ := (γc - ε) / (γc - ε / 2) with hrat_def
    have hrat_lt_one : rat < 1 := by
      rw [hrat_def, div_lt_one hγc_eps2_pos]
      linarith
    have hrat_pos : 0 < rat := div_pos hγc_eps_pos hγc_eps2_pos
    have h1mr_pos : 0 < 1 - rat := by linarith
    set M₀ : ℕ := ⌈(1 - rat)⁻¹⌉₊ + 1 with hM₀_def
    -- For ℓ ≥ M₀, (ℓ-1)/ℓ ≥ rat.
    have h_ratio_bound : ∀ ℓ : ℕ, M₀ ≤ ℓ →
        rat ≤ ((ℓ - 1 : ℕ) : ℝ) / (ℓ : ℝ) := by
      intro ℓ hℓM₀
      have hℓ_pos : 0 < ℓ := by
        rw [hM₀_def] at hℓM₀
        omega
      have hℓ_one : 1 ≤ ℓ := hℓ_pos
      have hℓR_pos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
      have hℓm1_cast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
        rw [Nat.cast_sub hℓ_one]
        push_cast
        ring
      rw [hℓm1_cast, le_div_iff₀ hℓR_pos]
      -- Want rat * ℓ ≤ ℓ - 1, i.e., (1 - rat) * ℓ ≥ 1.
      have h_ge_inv : (1 - rat)⁻¹ ≤ (ℓ : ℝ) := by
        have h1 : ((⌈(1 - rat)⁻¹⌉₊ : ℕ) : ℝ) ≤ (ℓ : ℝ) := by
          have : ⌈(1 - rat)⁻¹⌉₊ ≤ ℓ := by
            rw [hM₀_def] at hℓM₀
            omega
          exact_mod_cast this
        exact (Nat.le_ceil _).trans h1
      have h_one_le : 1 ≤ (1 - rat) * (ℓ : ℝ) := by
        have h1 : (1 - rat)⁻¹ * (1 - rat) = 1 := inv_mul_cancel₀ h1mr_pos.ne'
        have h2 : (1 - rat)⁻¹ * (1 - rat) ≤ (ℓ : ℝ) * (1 - rat) :=
          mul_le_mul_of_nonneg_right h_ge_inv h1mr_pos.le
        rw [h1] at h2
        linarith
      linarith
    -- For Y large, the Linnik prime ℓ ≥ A·P + 1 ≥ P + 1 ≥ M₀.
    -- Since P Y → ∞, we get P Y ≥ M₀ eventually.
    have h_P_ge_M₀ : ∀ᶠ Y : ℕ in atTop, M₀ ≤ LowerConstruction.P Y :=
      lc_P_atTop.eventually_ge_atTop M₀
    -- Combine all eventual conditions.
    filter_upwards [h_prime_ge, h_logY_pos, h_P_ge_M₀, Filter.eventually_ge_atTop 1]
      with Y hPrime hLogY hPM₀ hY1
    have hAP_pos : 1 ≤ LowerConstruction.A Y * LowerConstruction.P Y :=
      Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (LowerConstruction.A_pos Y).ne' (LowerConstruction.P_pos Y).ne')
    obtain ⟨ℓ, hℓ_prime, hℓ_dvd, hℓ_le⟩ :=
      hLinnik (LowerConstruction.A Y * LowerConstruction.P Y) hAP_pos
    have hℓ_pos : 0 < ℓ := hℓ_prime.pos
    have hℓ_two : 2 ≤ ℓ := hℓ_prime.two_le
    have hA_dvd : LowerConstruction.A Y ∣ ℓ - 1 :=
      dvd_trans ⟨LowerConstruction.P Y, rfl⟩ hℓ_dvd
    have hA_pos : 0 < LowerConstruction.A Y := LowerConstruction.A_pos Y
    have hP_pos : 0 < LowerConstruction.P Y := LowerConstruction.P_pos Y
    -- ℓ ≥ A·P + 1: from A·P ∣ ℓ - 1 and ℓ - 1 ≥ 1.
    have hAP_dvd_lm1 : LowerConstruction.A Y * LowerConstruction.P Y ∣ ℓ - 1 := hℓ_dvd
    have hℓm1_pos : 1 ≤ ℓ - 1 := by omega
    have hAP_le_lm1 : LowerConstruction.A Y * LowerConstruction.P Y ≤ ℓ - 1 :=
      Nat.le_of_dvd (by omega) hAP_dvd_lm1
    have hP_le_lm1 : LowerConstruction.P Y ≤ ℓ - 1 := by
      have h1 : LowerConstruction.P Y ≤ LowerConstruction.A Y * LowerConstruction.P Y :=
        Nat.le_mul_of_pos_left _ hA_pos
      linarith
    have hM₀_le_ℓ : M₀ ≤ ℓ := by
      have : M₀ ≤ LowerConstruction.P Y := hPM₀
      omega
    set U : ℕ := (ℓ - 1) / LowerConstruction.A Y with hU_def
    have hAU : LowerConstruction.A Y * U = ℓ - 1 := by
      rw [hU_def]
      exact Nat.mul_div_cancel' hA_dvd
    have hP_dvd_U : LowerConstruction.P Y ∣ U := by
      have h1 : LowerConstruction.A Y * LowerConstruction.P Y ∣ LowerConstruction.A Y * U := by
        rw [hAU]
        exact hℓ_dvd
      exact (Nat.mul_dvd_mul_iff_left hA_pos).mp h1
    have hU_pos : 0 < U := Nat.pos_of_ne_zero fun h => by
      have hℓm1_zero : ℓ - 1 = 0 := by rw [← hAU, h, Nat.mul_zero]
      have hℓ_le_one : ℓ ≤ 1 := by omega
      exact (Nat.lt_irrefl 1) (lt_of_lt_of_le hℓ_prime.one_lt hℓ_le_one)
    have hU_lt_ℓ : U < ℓ := by
      have hA_ge_1 : 1 ≤ LowerConstruction.A Y := hA_pos
      have h1 : U ≤ LowerConstruction.A Y * U := Nat.le_mul_of_pos_left _ hA_ge_1
      omega
    refine ⟨ℓ * LowerConstruction.Q Y U, LowerConstruction.P Y * U * LowerConstruction.Q Y U,
        Nat.totient (ℓ * LowerConstruction.Q Y U),
        ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero hℓ_prime.ne_zero (LowerConstruction.Q_pos Y U).ne')
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero hP_pos.ne' hU_pos.ne') (LowerConstruction.Q_pos Y U).ne')
    · have hpos : 0 < ℓ * LowerConstruction.Q Y U :=
        Nat.mul_pos hℓ_pos (LowerConstruction.Q_pos Y U)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hpos).ne'
    · exact (LowerConstruction.totient_a_eq_totient_b Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU).symm
    · -- The main ratio bound: b/a ≥ (γc - ε) log Y.
      -- b/a = primeEulerProdNat Y · (ℓ-1)/ℓ ≥ (γc - ε/2) log Y · rat = (γc - ε) log Y.
      have h_ratio_eq :
          ((LowerConstruction.P Y * U * LowerConstruction.Q Y U : ℕ) : ℝ) /
            ((ℓ * LowerConstruction.Q Y U : ℕ) : ℝ) =
              primeEulerProdNat Y * ((ℓ - 1 : ℝ) / ℓ) :=
        LowerConstruction.collision_ratio Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU
      rw [ge_iff_le, h_ratio_eq]
      -- Cast (ℓ - 1 : ℕ) = (ℓ : ℝ) - 1.
      have hℓ_one : 1 ≤ ℓ := hℓ_prime.one_le
      have hℓm1_cast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
        rw [Nat.cast_sub hℓ_one]
        push_cast
        ring
      have h_rat_le : rat ≤ ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
        rw [← hℓm1_cast]
        exact h_ratio_bound ℓ hM₀_le_ℓ
      -- primeEulerProdNat Y ≥ (γc - ε/2) log Y > 0.
      have hPpN_pos : 0 ≤ primeEulerProdNat Y := by
        have h1 : (γc - ε / 2) * Real.log (Y : ℝ) ≥ 0 :=
          mul_nonneg hγc_eps2_pos.le hLogY.le
        linarith [hPrime]
      have h_prod_lb :
          (γc - ε) * Real.log (Y : ℝ) ≤
            ((γc - ε / 2) * Real.log (Y : ℝ)) * rat := by
        -- (γc - ε/2) * rat = γc - ε.
        have h_prod_eq : (γc - ε / 2) * rat = γc - ε := by
          rw [hrat_def, mul_div_assoc']
          rw [mul_div_cancel_left₀ _ hγc_eps2_pos.ne']
        rw [show ((γc - ε / 2) * Real.log (Y : ℝ)) * rat =
            ((γc - ε / 2) * rat) * Real.log (Y : ℝ) by ring]
        rw [h_prod_eq]
      -- Combine: ppN · (ℓ-1)/ℓ ≥ (γc - ε/2) log Y · rat ≥ (γc - ε) log Y.
      have h_ratio_lb :
          (γc - ε / 2) * Real.log (Y : ℝ) * rat ≤
            primeEulerProdNat Y * ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
        have hℓR_pos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
        -- ppN · (ℓ-1)/ℓ ≥ (γc - ε/2) log Y · rat:
        -- Use: ppN ≥ (γc - ε/2) log Y ≥ 0, (ℓ-1)/ℓ ≥ rat ≥ 0.
        have h1 : 0 ≤ ((γc - ε / 2) * Real.log (Y : ℝ)) := mul_nonneg hγc_eps2_pos.le hLogY.le
        have h2 : 0 ≤ rat := hrat_pos.le
        have h3 : 0 ≤ ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
          have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ_one
          have h_lm1_nn : 0 ≤ (ℓ : ℝ) - 1 := by linarith
          exact div_nonneg h_lm1_nn hℓR_pos.le
        have h_first : (γc - ε / 2) * Real.log (Y : ℝ) * rat ≤
            primeEulerProdNat Y * rat :=
          mul_le_mul_of_nonneg_right hPrime h2
        have h_second : primeEulerProdNat Y * rat ≤
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_left h_rat_le hPpN_pos
        have : (γc - ε / 2) * Real.log (Y : ℝ) * rat ≤
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) :=
          le_trans h_first h_second
        rw [show primeEulerProdNat Y * ((ℓ : ℝ) - 1) / (ℓ : ℝ) =
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) by ring]
        exact this
      -- Goal currently: (γc - ε) * log Y ≤ ppN * ((ℓ - 1) / ℓ).
      -- ((ℓ : ℝ) - 1)/(ℓ : ℝ) is what shows up after the rewrite.
      have h_combined :
          (γc - ε) * Real.log (Y : ℝ) ≤
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by
        calc (γc - ε) * Real.log (Y : ℝ)
            ≤ (γc - ε / 2) * Real.log (Y : ℝ) * rat := h_prod_lb
          _ ≤ primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by
              have : primeEulerProdNat Y * ((ℓ : ℝ) - 1) / (ℓ : ℝ) =
                  primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by ring
              linarith [this ▸ h_ratio_lb]
      exact h_combined
    · exact collision_size_bound Y U ℓ C L hC hL hℓ_prime hU_pos hU_lt_ℓ hAU hℓ_le hY1

/-- **Totient-collision construction (Section 2 lower bound).**
Now a *theorem* (formerly a top-level trusted declaration): derived from the
height-form `collision_at_height` together with `linnik_dvd`, by the
substitution `Y(x) := ⌊log x / (2K)⌋` (so that `n ≤ exp(K·Y) ≤ √x ≤ x`, while
`log Y(x) = log log x + O(1)`). -/
theorem totient_collision_construction :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧ n ≤ x ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        (b : ℝ) / a ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  intro ε hε
  -- Extract Linnik constants.
  obtain ⟨C, L, hC, hL, hLinnik⟩ := _root_.linnik_dvd
  -- Apply the height-level theorem with halved tolerance ε/2.
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨K, hK_pos, hY⟩ := collision_at_height C L hC hL hLinnik (ε / 2) hε2
  -- Substitute Y(x) := ⌊log x / (2K)⌋, x ≥ exp(2K) ensures Y(x) ≥ 1, and
  -- exp(K·Y(x)) ≤ exp(log x / 2) = √x ≤ x.
  -- log Y(x) = log log x - log (2K) + o(1), and (e^γ - ε/2) (log log x - C') ≥
  -- (e^γ - ε) log log x for x large.
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  have h2K_pos : 0 < 2 * K := by linarith
  -- Define the threshold map x ↦ Y(x). To translate `∀ᶠ Y, P Y` over ℕ into
  -- `∀ᶠ x, P (Y(x))`, use that Y(x) → ∞ as x → ∞ (it's monotone in x).
  -- Convert hY (eventually-in-Y) to eventually-in-x via composition.
  rw [Filter.eventually_atTop] at hY
  obtain ⟨Y₀, hY_main⟩ := hY
  -- Pick a base x-threshold large enough.
  -- We need: (a) Y(x) := ⌊log x / (2K)⌋ ≥ Y₀, (b) Y(x) ≥ 1, (c) exp(K·Y(x)) ≤ x,
  -- (d) log Y(x) ≥ 1 (so positive), and (e) the ratio bound (e^γ - ε/2) log Y(x) ≥
  --     (e^γ - ε) log log x. For (e), since log Y(x) ≤ log log x and we want
  --     (e^γ - ε/2) log Y(x) ≥ (e^γ - ε) log log x, equivalent to
  --     (e^γ - ε/2) (log log x - log(2K)) ≥ (e^γ - ε) log log x, i.e.,
  --     (ε/2) log log x ≥ (e^γ - ε/2) log(2K) + ... (eventually true).
  -- Define Yx as a Nat-valued function. Use Nat.floor of a real.
  let Yx : ℕ → ℕ := fun x => ⌊Real.log (x : ℝ) / (2 * K)⌋₊
  -- Step A: Yx tends to atTop.
  have hYx_tendsto : Tendsto Yx atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ) / (2 * K)) atTop atTop := by
      have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact hlog.atTop_div_const h2K_pos
    exact tendsto_nat_floor_atTop.comp h1
  -- Threshold to get Yx ≥ max(Y₀, 1).
  have h_Yx_ge_Y0 : ∀ᶠ x : ℕ in atTop, Y₀ ≤ Yx x := hYx_tendsto.eventually_ge_atTop Y₀
  have h_Yx_ge_1 : ∀ᶠ x : ℕ in atTop, 1 ≤ Yx x := hYx_tendsto.eventually_ge_atTop 1
  -- Compute the basic inequalities relating x and Yx.
  -- Key: for x ≥ 1 with log x ≥ 0, Yx x ≤ log x / (2K), hence 2K · Yx ≤ log x,
  -- so exp(K · Yx) ≤ exp(log x / 2) = √x ≤ x for x ≥ 1.
  have h_exp_K_Yx_le_x : ∀ᶠ x : ℕ in atTop, Real.exp (K * Yx x) ≤ (x : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx1
    have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hxR_pos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogx_nn : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg hxR
    have h_floor_le : (Yx x : ℝ) ≤ Real.log (x : ℝ) / (2 * K) := by
      simpa [Yx] using Nat.floor_le (a := Real.log (x : ℝ) / (2 * K)) (by positivity)
    have h_2K_Yx : (2 * K) * (Yx x : ℝ) ≤ Real.log (x : ℝ) := by
      have := mul_le_mul_of_nonneg_left h_floor_le h2K_pos.le
      have hsimp : (2 * K) * (Real.log (x : ℝ) / (2 * K)) = Real.log (x : ℝ) := by
        field_simp
      linarith [hsimp ▸ this]
    have hK_Yx_le_half : K * (Yx x : ℝ) ≤ Real.log (x : ℝ) / 2 := by
      have h2 : 2 * (K * (Yx x : ℝ)) ≤ Real.log (x : ℝ) := by linarith
      linarith
    have h_exp_le : Real.exp (K * (Yx x : ℝ)) ≤ Real.exp (Real.log (x : ℝ) / 2) :=
      Real.exp_le_exp.mpr hK_Yx_le_half
    have h_sqrt_le : Real.exp (Real.log (x : ℝ) / 2) ≤ (x : ℝ) := by
      -- exp(log x / 2) = sqrt x ≤ x for x ≥ 1.
      have hexp_eq : Real.exp (Real.log (x : ℝ) / 2) =
          Real.exp (Real.log (x : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.exp_mul]
        ring_nf
      rw [hexp_eq, Real.exp_log hxR_pos]
      -- x^(1/2) ≤ x for x ≥ 1: x^(1/2) = x^(1/2) and x = x^1, so use Real.rpow_le_rpow_left.
      have h_rpow_le : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hxR
        norm_num
      rw [Real.rpow_one] at h_rpow_le
      exact h_rpow_le
    calc Real.exp (K * (Yx x : ℝ)) ≤ Real.exp (Real.log (x : ℝ) / 2) := h_exp_le
      _ ≤ (x : ℝ) := h_sqrt_le
  -- Step B: For x large enough, log (Yx x) ≥ (1 - ε/(2*(e^γ - ε/2))) * log log x −
  -- (something involving log(2K)). We prove eventually:
  --   (e^γ - ε/2) * log (Yx x) ≥ (e^γ - ε) * log log x.
  -- Strategy: log (Yx x) ≥ log (log x / (2K) - 1) = log log x - log(2K) + o(1)
  -- (eventually), so the LHS is (e^γ - ε/2)(log log x - log(2K) - small).
  -- Difference RHS-LHS = (ε/2) log log x - (e^γ - ε/2)(log(2K) + small).
  -- Eventually positive for log log x → ∞.
  have h_loglog_tendsto : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp h1
  have hlogYx_tendsto : Tendsto (fun x : ℕ => Real.log (Yx x : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun x : ℕ => (Yx x : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hYx_tendsto
    exact Real.tendsto_log_atTop.comp h1
  -- Need: eventually `(e^γ - ε/2) log (Yx x) ≥ (e^γ - ε) log log x`.
  -- Use: Yx x ≥ log x / (2K) - 1, so log (Yx x) ≥ log (log x / (2K) - 1).
  -- For x large enough (log x ≥ 4K), log x / (2K) - 1 ≥ log x / (4K), so
  -- log (Yx x) ≥ log (log x / (4K)) = log log x - log (4K).
  -- Then (e^γ - ε/2)(log log x - log(4K)) ≥ (e^γ - ε) log log x ⇔
  -- (ε/2) log log x ≥ (e^γ - ε/2) log(4K), eventually true.
  have h_ratio_eventually : ∀ᶠ x : ℕ in atTop,
      (γc - ε / 2) * Real.log (Yx x : ℝ) ≥ (γc - ε) * Real.log (Real.log (x : ℝ)) := by
    -- Strategy:
    -- log (Yx x) ≥ log log x - log (4K)  (eventually, when log x ≥ 8K).
    -- Also log (Yx x) ≤ log log x      (eventually, when Yx x ≤ log x).
    -- We split on the sign of (γc - ε/2):
    --  • If γc - ε/2 ≥ 0: LHS ≥ (γc - ε/2)(log log x - log 4K) ≥ (γc - ε) log log x
    --                     ⇔ (ε/2) log log x ≥ (γc - ε/2) log(4K), true eventually.
    --  • If γc - ε/2 < 0: γc - ε < γc - ε/2 < 0. Use log Yx ≤ log log x:
    --                     LHS = (γc - ε/2) log Yx ≥ (γc - ε/2) log log x ≥ (γc - ε) log log x
    --                     (first ≥ since coefficient is negative; second since γc-ε/2 ≥ γc-ε).
    have h4K_pos : (0 : ℝ) < 4 * K := by linarith
    -- Magnitude bound for the threshold: |γc - ε/2| · |log(4K)| + 1 + γc·γc.
    -- We make log log x larger than (|γc - ε/2| · |log(4K)| + 1) · 2 / ε to ensure the
    -- needed inequality.
    set MUB : ℝ := (|γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) + 1) * 2 / ε + 1
      with hMUB_def
    have h_loglog_ge : ∀ᶠ x : ℕ in atTop, Real.log (Real.log (x : ℝ)) ≥ MUB :=
      h_loglog_tendsto.eventually_ge_atTop _
    have h_logx_ge_8K : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≥ 8 * K := by
      have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact h1.eventually_ge_atTop _
    have h_logx_ge_e : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≥ Real.exp 1 := by
      have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact h1.eventually_ge_atTop _
    -- For Yx x ≤ log x (eventually): Yx x = ⌊log x / (2K)⌋ ≤ log x / (2K). For 2K ≥ 1, Yx ≤ log x
    -- automatically; for 2K < 1, need log x / (2K) ≤ log x which holds only if 2K ≥ 1. So use
    -- the stronger threshold: pick x large enough that log x / (2K) ≤ log x is moot — we just
    -- want log(Yx x) ≤ log log x. Since Yx x ≤ log x / (2K), have log Yx ≤ log(log x / (2K)) =
    -- log log x - log(2K). If log(2K) ≥ 0 (i.e., 2K ≥ 1), log Yx ≤ log log x. If log(2K) < 0
    -- (i.e., 2K < 1), log Yx ≤ log log x + |log(2K)|.
    -- Cleaner: log (Yx x) ≤ log log x + |log(2K)| (eventually). We use this generic bound.
    have h_logx_ge_2K : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≥ 2 * K := by
      have h1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact h1.eventually_ge_atTop _
    filter_upwards [h_loglog_ge, h_logx_ge_8K, h_logx_ge_e, h_logx_ge_2K, h_Yx_ge_1]
      with x hx_loglog hx_logx hx_logx_e hx_logx_2K hx_Yx1
    -- Compute Yx x ≥ log x / (4K) and Yx x ≤ log x / (2K).
    have h_logx_pos : (0 : ℝ) < Real.log (x : ℝ) := by
      have : Real.exp 1 > 0 := Real.exp_pos _
      linarith
    have h_Yx_pos_R : (0 : ℝ) < (Yx x : ℝ) := by exact_mod_cast hx_Yx1
    have h_floor_lb : (Real.log (x : ℝ) / (2 * K) - 1 : ℝ) ≤ (Yx x : ℝ) := by
      have h := Nat.sub_one_lt_floor (a := Real.log (x : ℝ) / (2 * K))
      simp only [Yx]
      linarith
    have h_floor_ub : ((Yx x : ℝ)) ≤ Real.log (x : ℝ) / (2 * K) := by
      simpa [Yx] using Nat.floor_le (a := Real.log (x : ℝ) / (2 * K)) (by positivity)
    -- log x / (2K) ≥ 4, so log x / (2K) - 1 ≥ log x / (4K) ≥ 2.
    have h_logx_div_2K_ge4 : Real.log (x : ℝ) / (2 * K) ≥ 4 := by
      rw [ge_iff_le, le_div_iff₀ h2K_pos]
      linarith
    have h_logx_div_4K_pos : (0 : ℝ) < Real.log (x : ℝ) / (4 * K) := by
      positivity
    have h_subtraction_id : Real.log (x : ℝ) / (2 * K) - Real.log (x : ℝ) / (4 * K) =
        Real.log (x : ℝ) / (4 * K) := by
      field_simp
      ring
    have h_logx_div_4K_ge2 : Real.log (x : ℝ) / (4 * K) ≥ 2 := by
      have : Real.log (x : ℝ) / (4 * K) = (Real.log (x : ℝ) / (2 * K)) / 2 := by
        field_simp
        ring
      rw [this]
      linarith
    have h_lower_lb : (Real.log (x : ℝ) / (4 * K)) ≤ Real.log (x : ℝ) / (2 * K) - 1 := by
      linarith
    have h_Yx_ge_4K : (Yx x : ℝ) ≥ Real.log (x : ℝ) / (4 * K) := by linarith
    -- log (Yx x) ≥ log (log x / (4K)) = log log x - log (4K).
    have h_log_Yx_ge : Real.log (Yx x : ℝ) ≥ Real.log (Real.log (x : ℝ) / (4 * K)) :=
      Real.log_le_log h_logx_div_4K_pos h_Yx_ge_4K
    have h_4K_pos' : (0 : ℝ) < 4 * K := by linarith
    have h_log_div_4K : Real.log (Real.log (x : ℝ) / (4 * K)) =
        Real.log (Real.log (x : ℝ)) - Real.log (4 * K) := by
      rw [Real.log_div h_logx_pos.ne' h_4K_pos'.ne']
    have h_log_Yx_lb : Real.log (Yx x : ℝ) ≥
        Real.log (Real.log (x : ℝ)) - Real.log (4 * K) := by
      rw [← h_log_div_4K]
      exact h_log_Yx_ge
    -- log (Yx x) ≤ log (log x / (2K)) = log log x - log(2K).
    have h_logx_div_2K_pos : (0 : ℝ) < Real.log (x : ℝ) / (2 * K) := by positivity
    have h_log_Yx_ub : Real.log (Yx x : ℝ) ≤ Real.log (Real.log (x : ℝ) / (2 * K)) :=
      Real.log_le_log h_Yx_pos_R h_floor_ub
    have h_log_div_2K_id : Real.log (Real.log (x : ℝ) / (2 * K)) =
        Real.log (Real.log (x : ℝ)) - Real.log (2 * K) := by
      rw [Real.log_div h_logx_pos.ne' h2K_pos.ne']
    have h_log_Yx_ub2 : Real.log (Yx x : ℝ) ≤
        Real.log (Real.log (x : ℝ)) - Real.log (2 * K) := by
      rw [← h_log_div_2K_id]
      exact h_log_Yx_ub
    -- Set abbreviations.
    set M : ℝ := Real.log (Real.log (x : ℝ)) with hM_def
    set N : ℝ := Real.log (Yx x : ℝ) with hN_def
    -- We have N ≥ M - log(4K) and N ≤ M - log(2K).
    -- Want: (γc - ε/2) N ≥ (γc - ε) M.
    -- Use: N ≥ M - log(4K). Then (γc - ε/2) N ≥ (γc - ε/2)(M - log(4K)) when γc-ε/2 ≥ 0,
    -- i.e., (γc - ε/2) M - (γc - ε/2) log(4K). Want this ≥ (γc - ε) M ⇔
    --   (ε/2) M ≥ (γc - ε/2) log(4K). Holds when M ≥ 2(γc - ε/2) log(4K) / ε, i.e., M ≥ MUB
    --   (chosen large enough).
    -- For γc - ε/2 < 0: use N ≤ M - log(2K) ≤ M + |log(2K)|, so
    -- (γc-ε/2) N ≥ (γc-ε/2)(M + |log(2K)|).
    -- Goal: (γc - ε/2) N ≥ (γc - ε) M.
    have h_abs_le : |γc - ε / 2| * |Real.log (4 * K)| ≤
        (|γc - ε / 2| * |Real.log (4 * K)| + 1) := by linarith
    have hMUB_M : M ≥ MUB := hx_loglog
    have h_M_pos : 0 < M := by
      rw [hM_def]
      exact Real.log_pos (by linarith [Real.exp_one_gt_d9])
    -- nlinarith handles the bound with the right hints.
    -- Common bookkeeping for both cases:
    -- (γc - ε/2) · log(4K) ≤ |γc - ε/2| · (|log(4K)| + |log(2K)|).
    -- (γc - ε/2) · log(2K) ≤ |γc - ε/2| · (|log(4K)| + |log(2K)|) (for case 2; using
    -- |γc-ε/2|·|log(2K)| ≤ same RHS).
    have h_abs_nn : 0 ≤ |γc - ε / 2| := abs_nonneg _
    have h_abs_log4K : 0 ≤ |Real.log (4 * K)| := abs_nonneg _
    have h_abs_log2K : 0 ≤ |Real.log (2 * K)| := abs_nonneg _
    have h_bd_4K : (γc - ε / 2) * Real.log (4 * K) ≤
        |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) := by
      calc (γc - ε / 2) * Real.log (4 * K)
          ≤ |(γc - ε / 2) * Real.log (4 * K)| := le_abs_self _
        _ = |γc - ε / 2| * |Real.log (4 * K)| := abs_mul _ _
        _ ≤ |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) := by
            apply mul_le_mul_of_nonneg_left _ h_abs_nn
            linarith
    have h_bd_2K : (γc - ε / 2) * Real.log (2 * K) ≤
        |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) := by
      calc (γc - ε / 2) * Real.log (2 * K)
          ≤ |(γc - ε / 2) * Real.log (2 * K)| := le_abs_self _
        _ = |γc - ε / 2| * |Real.log (2 * K)| := abs_mul _ _
        _ ≤ |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|) := by
            apply mul_le_mul_of_nonneg_left _ h_abs_nn
            linarith
    -- ε/2 · M ≥ |γc-ε/2| · (|log(4K)| + |log(2K)|) + 1 + ε/2.
    set BoundLog : ℝ := |γc - ε / 2| * (|Real.log (4 * K)| + |Real.log (2 * K)|)
      with hBoundLog_def
    have h_BoundLog_nn : 0 ≤ BoundLog := mul_nonneg h_abs_nn (by linarith)
    have h_bd_4K' : (γc - ε / 2) * Real.log (4 * K) ≤ BoundLog := h_bd_4K
    have h_bd_2K' : (γc - ε / 2) * Real.log (2 * K) ≤ BoundLog := h_bd_2K
    have h_eps_M_explicit : ε / 2 * M ≥ BoundLog + 1 + ε / 2 := by
      -- M ≥ MUB = (BoundLog + 1) * 2 / ε + 1.
      -- ⟹ ε/2 · M ≥ ε/2 · ((BoundLog + 1) * 2 / ε + 1) = (BoundLog + 1) + ε/2.
      have h_eps_pos : 0 < ε := hε
      have h_M_lb : M ≥ (BoundLog + 1) * 2 / ε + 1 := hMUB_M
      have hε_M : ε / 2 * M ≥ ε / 2 * ((BoundLog + 1) * 2 / ε + 1) :=
        mul_le_mul_of_nonneg_left h_M_lb (by linarith)
      have h_simp : ε / 2 * ((BoundLog + 1) * 2 / ε + 1) = (BoundLog + 1) + ε / 2 := by
        field_simp
      linarith [h_simp ▸ hε_M]
    by_cases hcoeff : 0 ≤ γc - ε / 2
    · -- Case 1: γc - ε/2 ≥ 0.
      have h_LHS_lb : (γc - ε / 2) * N ≥ (γc - ε / 2) * (M - Real.log (4 * K)) :=
        mul_le_mul_of_nonneg_left h_log_Yx_lb hcoeff
      -- (γc - ε/2)(M - log(4K)) - (γc - ε) M = (ε/2) M - (γc - ε/2) log(4K) ≥ 0.
      have h_arith : (γc - ε / 2) * (M - Real.log (4 * K)) ≥ (γc - ε) * M := by
        have hexpand : (γc - ε / 2) * (M - Real.log (4 * K)) - (γc - ε) * M =
            ε / 2 * M - (γc - ε / 2) * Real.log (4 * K) := by ring
        linarith [hexpand]
      linarith
    · -- Case 2: γc - ε/2 < 0. Use N ≤ M - log(2K), coefficient negative.
      push Not at hcoeff
      have hcoeff_le : γc - ε / 2 ≤ 0 := le_of_lt hcoeff
      -- (γc - ε/2) N - (γc - ε/2)(M - log(2K)) = (γc - ε/2)(N - M + log(2K))
      -- N ≤ M - log(2K) ⟹ N - M + log(2K) ≤ 0. Multiply by negative: ≥ 0.
      have h_LHS_lb : (γc - ε / 2) * N ≥ (γc - ε / 2) * (M - Real.log (2 * K)) := by
        -- mul_le_mul_of_nonpos_left : c ≤ 0 → a ≤ b → c * b ≤ c * a.
        exact mul_le_mul_of_nonpos_left h_log_Yx_ub2 hcoeff_le
      -- (γc - ε/2)(M - log(2K)) - (γc - ε) M = ε/2 M - (γc - ε/2) log(2K) ≥ 0.
      have h_arith : (γc - ε / 2) * (M - Real.log (2 * K)) ≥ (γc - ε) * M := by
        have hexpand : (γc - ε / 2) * (M - Real.log (2 * K)) - (γc - ε) * M =
            ε / 2 * M - (γc - ε / 2) * Real.log (2 * K) := by ring
        linarith [hexpand]
      linarith
  -- Now combine: the main per-x consequence.
  -- We need: ∃ a b n, [props] ∧ n ≤ x ∧ b/a ≥ (e^γ - ε) log log x.
  filter_upwards [h_Yx_ge_Y0, h_Yx_ge_1, h_exp_K_Yx_le_x, h_ratio_eventually,
    Filter.eventually_ge_atTop 1] with x hxY0 hxYx1 hx_exp hx_ratio _hx1
  obtain ⟨a, b, n, ha, hb, hn, hφa, hφb, hba_height, hn_size⟩ := hY_main (Yx x) hxY0
  refine ⟨a, b, n, ha, hb, hn, ?_, hφa, hφb, ?_⟩
  · -- n ≤ x.
    have hn_le_R : (n : ℝ) ≤ Real.exp (K * Yx x) := hn_size
    have h_le_x_R : (n : ℝ) ≤ (x : ℝ) := le_trans hn_le_R hx_exp
    exact_mod_cast h_le_x_R
  · -- b/a ≥ (γc - ε) log log x.
    calc (b : ℝ) / a ≥ (γc - ε / 2) * Real.log (Yx x : ℝ) := hba_height
      _ ≥ (γc - ε) * Real.log (Real.log (x : ℝ)) := hx_ratio

private lemma R_ge_of_totient_collision {x a b n : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : 1 ≤ n) (hnx : n ≤ x)
    (hφa : Nat.totient a = n) (hφb : Nat.totient b = n) :
    (b : ℝ) / a ≤ R x := by
  -- We show R x ≥ b/a by exhibiting n in the supremum index set.
  -- mmax := sSup {m | φ m = n} ≥ b (since b is in the set and the set is bounded)
  -- mmin := sInf {m | φ m = n} ≤ a (since a is in the set)
  -- so mmax/mmin ≥ b/a.
  set A : Set ℕ := {m | Nat.totient m = n} with hA_def
  have hb_in : b ∈ A := hφb
  have ha_in : a ∈ A := hφa
  have hA_ne : A.Nonempty := ⟨b, hb_in⟩
  -- A is bounded above by 2 n^2 (totient_preimage_bound).
  have hA_bdd : BddAbove A := by
    refine ⟨2 * n ^ 2, ?_⟩
    intro m hm
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · have hm' : Nat.totient m = n := hm
        rw [h0, Nat.totient_zero] at hm'
        omega
      · exact hpos
    exact totient_preimage_bound hm_pos hm
  set mmax : ℕ := sSup A with hmmax_def
  set mmin : ℕ := sInf A with hmmin_def
  have hmmax_in : mmax ∈ A := Nat.sSup_mem hA_ne hA_bdd
  have hmmin_in : mmin ∈ A := Nat.sInf_mem hA_ne
  -- b ≤ mmax (since b ∈ A, mmax = sSup A).
  have hb_le_mmax : b ≤ mmax := le_csSup hA_bdd hb_in
  -- mmin ≤ a (since a ∈ A, mmin = sInf A).
  have hmmin_le_a : mmin ≤ a := Nat.sInf_le ha_in
  -- mmin ≥ 1.
  have hmmin_pos : 1 ≤ mmin := by
    rcases Nat.eq_zero_or_pos mmin with h0 | hpos
    · have : Nat.totient mmin = n := hmmin_in
      rw [h0, Nat.totient_zero] at this
      omega
    · exact hpos
  have hmmax_pos : 1 ≤ mmax := le_trans hb hb_le_mmax
  -- (mmax : ℝ)/mmin ≥ b/a.
  have ha_pos_R : (0 : ℝ) < a := by exact_mod_cast ha
  have hmmin_pos_R : (0 : ℝ) < mmin := by exact_mod_cast hmmin_pos
  have hb_le_mmax_R : (b : ℝ) ≤ mmax := by exact_mod_cast hb_le_mmax
  have hmmin_le_a_R : (mmin : ℝ) ≤ a := by exact_mod_cast hmmin_le_a
  have hratio_ge : (b : ℝ) / a ≤ (mmax : ℝ) / mmin := by
    -- b/a ≤ mmax/a ≤ mmax/mmin
    have h1 : (b : ℝ) / a ≤ (mmax : ℝ) / a :=
      div_le_div_of_nonneg_right hb_le_mmax_R (le_of_lt ha_pos_R)
    have hmmax_nn : (0 : ℝ) ≤ mmax := by exact_mod_cast Nat.zero_le _
    have h2 : (mmax : ℝ) / a ≤ (mmax : ℝ) / mmin :=
      div_le_div_of_nonneg_left hmmax_nn hmmin_pos_R hmmin_le_a_R
    linarith
  -- Now show R x ≥ mmax/mmin by inclusion in the supremum.
  -- n ∈ {n | n ∈ Icc 1 x ∧ ∃ m, φ m = n}
  have hn_in_idx : n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n} := by
    refine ⟨⟨hn, hnx⟩, b, hφb⟩
  -- Boundedness for the outer sup.
  -- The outer family ⨆ (n : ℕ), ⨆ (_ : n ∈ idx_set), (mmax_n : ℝ) / mmin_n is bounded
  -- by 2 * x^2 (since mmax ≤ 2 n² ≤ 2 x², and mmin ≥ 1).
  have hbdd_outer :
      BddAbove (Set.range (fun (n' : ℕ) =>
        ⨆ (_ : n' ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}),
          let mmax' := sSup {m | Nat.totient m = n'}
          let mmin' := sInf {m | Nat.totient m = n'}
          (mmax' : ℝ) / mmin')) := by
    refine ⟨((2 * x ^ 2 : ℕ) : ℝ), ?_⟩
    rintro _ ⟨n', rfl⟩
    simp only
    by_cases hn'mem : n' ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}
    · rw [ciSup_pos hn'mem]
      obtain ⟨⟨hn'_pos, hn'_le_x⟩, m_w, hφm_w⟩ := hn'mem
      have hm_w_pos : 1 ≤ m_w := by
        rcases Nat.eq_zero_or_pos m_w with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφm_w
          omega
        · exact hpos
      set A' : Set ℕ := {m | Nat.totient m = n'} with hA'_def
      have hA'_ne : A'.Nonempty := ⟨m_w, hφm_w⟩
      have hA'_bdd : BddAbove A' := by
        refine ⟨2 * n' ^ 2, ?_⟩
        intro m hm
        have hm_pos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · have : Nat.totient m = n' := hm
            rw [h0, Nat.totient_zero] at this
            omega
          · exact hpos
        exact totient_preimage_bound hm_pos hm
      set mmax' : ℕ := sSup A' with hmmax'_def
      set mmin' : ℕ := sInf A' with hmmin'_def
      have hmmax'_in : mmax' ∈ A' := Nat.sSup_mem hA'_ne hA'_bdd
      have hmmin'_in : mmin' ∈ A' := Nat.sInf_mem hA'_ne
      have hφmmax' : Nat.totient mmax' = n' := hmmax'_in
      have hφmmin' : Nat.totient mmin' = n' := hmmin'_in
      have hmmax'_pos : 1 ≤ mmax' := by
        rcases Nat.eq_zero_or_pos mmax' with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmax'
          omega
        · exact hpos
      have hmmin'_pos : 1 ≤ mmin' := by
        rcases Nat.eq_zero_or_pos mmin' with h0 | hpos
        · rw [h0, Nat.totient_zero] at hφmmin'
          omega
        · exact hpos
      have hmmax'_le : mmax' ≤ 2 * n' ^ 2 := totient_preimage_bound hmmax'_pos hφmmax'
      have hmmax'_le_2xsq : mmax' ≤ 2 * x ^ 2 := by
        have : 2 * n' ^ 2 ≤ 2 * x ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn'_le_x 2)
        omega
      -- (mmax' : ℝ) / mmin' ≤ mmax' (since mmin' ≥ 1)
      have hmmin'_pos_R : (0 : ℝ) < mmin' := by exact_mod_cast hmmin'_pos
      have hmmax'_nn_R : (0 : ℝ) ≤ mmax' := by exact_mod_cast Nat.zero_le _
      have h1' : (mmax' : ℝ) / mmin' ≤ mmax' := by
        rw [div_le_iff₀ hmmin'_pos_R]
        have : (1 : ℝ) ≤ (mmin' : ℝ) := by exact_mod_cast hmmin'_pos
        nlinarith
      have h2' : (mmax' : ℝ) ≤ ((2 * x ^ 2 : ℕ) : ℝ) := by exact_mod_cast hmmax'_le_2xsq
      linarith
    · rw [ciSup_neg hn'mem]
      simp only [Real.sSup_empty]
      exact_mod_cast Nat.zero_le _
  -- R x ≥ inner term at n.
  have hR_ge : (mmax : ℝ) / mmin ≤ R x := by
    unfold R
    have h_inner_eq :
        (⨆ (_ : n ∈ {n : ℕ | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n}),
            let mmax' := sSup {m | Nat.totient m = n}
            let mmin' := sInf {m | Nat.totient m = n}
            (mmax' : ℝ) / mmin') = (mmax : ℝ) / mmin :=
      ciSup_pos hn_in_idx
    rw [← h_inner_eq]
    exact le_ciSup hbdd_outer n
  exact le_trans hratio_ge hR_ge

theorem R_lower_bound :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      R x ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  intro ε hε
  filter_upwards [totient_collision_construction ε hε, Filter.eventually_ge_atTop 1]
    with x hx hx1
  obtain ⟨a, b, n, ha, hb, hn, hnx, hφa, hφb, hba⟩ := hx
  have hR_ge : (b : ℝ) / a ≤ R x :=
    R_ge_of_totient_collision ha hb hn hnx hφa hφb
  linarith

/-- **Theorem 2.1.** Combined upper and lower bounds give the asymptotic.

Squeeze argument: given `R_upper_bound` and `R_lower_bound` (both `∀ ε > 0, ∀ᶠ x, …`),
choose `ε = δ · e^γ / 2` for target `δ > 0`. Eventually
`(R x - e^γ log log x) / log log x ∈ [-ε, ε]`, so `R x / (e^γ log log x) - 1 ∈
[-δ/2, δ/2]`, giving `dist < δ`. -/
theorem totient_fibre_extremes :
    Tendsto
      (fun x : ℕ => R x / (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  set ε : ℝ := δ * γc / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have hev := (R_upper_bound ε hε_pos).and
    ((R_lower_bound ε hε_pos).and (Filter.eventually_ge_atTop 3))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun x hxN => ?_⟩
  obtain ⟨hxu, hxl, hx3⟩ := hN x hxN
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hlogx_gt_one : 1 < Real.log x := by
    have hle : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3R
    have hexp_lt_three : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have hlog3 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos _) hexp_lt_three
      simpa [Real.log_exp] using h
    linarith
  have hllogx_pos : 0 < Real.log (Real.log x) := Real.log_pos hlogx_gt_one
  set L : ℝ := Real.log (Real.log x) with hL_def
  have hdenom_pos : 0 < γc * L := mul_pos hγc_pos hllogx_pos
  rw [Real.dist_eq]
  have key : R x / (γc * L) - 1 = (R x - γc * L) / (γc * L) := by
    field_simp
  rw [key, abs_div, abs_of_pos hdenom_pos]
  have hub : R x - γc * L ≤ ε * L := by
    have h1 : (γc + ε) * L = γc * L + ε * L := by ring
    linarith
  have hlb : -(ε * L) ≤ R x - γc * L := by
    have h1 : (γc - ε) * L = γc * L - ε * L := by ring
    linarith
  have habs : |R x - γc * L| ≤ ε * L := abs_le.mpr ⟨hlb, hub⟩
  have hratio : |R x - γc * L| / (γc * L) ≤ ε * L / (γc * L) :=
    div_le_div_of_nonneg_right habs (le_of_lt hdenom_pos)
  have hsimp : ε * L / (γc * L) = ε / γc := by
    field_simp
  rw [hsimp] at hratio
  have hε_over_γc : ε / γc = δ / 2 := by
    rw [hε_def]
    field_simp
  rw [hε_over_γc] at hratio
  have hδ2_lt : δ / 2 < δ := by linarith
  exact lt_of_le_of_lt hratio hδ2_lt

/- ## Section 3 — Permanence observation

This section is **fully proved** — no sorries, no extra trusted inputs beyond Mathlib.
-/

/-- **Proposition 3.1 (Permanence).** If `φ(a) = φ(b) = n` with `a > b ≥ 1`, then
for every prime `r` coprime to `a*b`, the totient value `N_r := (r - 1) · n` has
both `r·a` and `r·b` as preimages, with ratio `r·a / (r·b) = a/b`.

In particular, since there are infinitely many primes coprime to any given `a*b`,
infinitely many distinct totient values achieve at least the ratio `a/b`. -/
theorem permanence_step (a b r : ℕ)
    (hab : Nat.totient a = Nat.totient b) (hr : Nat.Prime r) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b) :
    Nat.totient (r * a) = Nat.totient (r * b) := by
  have hcop_a : Nat.Coprime r a := (Nat.Prime.coprime_iff_not_dvd hr).mpr hra
  have hcop_b : Nat.Coprime r b := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrb
  rw [Nat.totient_mul hcop_a, Nat.totient_mul hcop_b, hab]

/-- **Proposition 3.1 (corollary, faithful to the PDF).**
If `1 ≤ b < a` and `φ(a) = φ(b)`, then there are infinitely many distinct
totient values `N` admitting a pair of preimages `(x, y)` with `y < x` and
`b · x ≥ a · y` (equivalently, `x / y ≥ a / b` in `ℚ` — and hence
`f_max(N) / f_min(N) ≥ a / b` since `f_max(N) ≥ x` and `f_min(N) ≤ y`).

This is the strict form of PDF Proposition 3.1: any nontrivial totient
collision propagates to infinitely many collisions of at least the same ratio. -/
theorem infinitely_many_collisions (a b : ℕ) (hb : 1 ≤ b) (hgt : b < a)
    (hab : Nat.totient a = Nat.totient b) :
    {N : ℕ | ∃ x y, Nat.totient x = N ∧ Nat.totient y = N ∧ y < x ∧ b * x ≥ a * y}.Infinite := by
  have ha : 1 ≤ a := lt_of_le_of_lt hb hgt |>.le
  -- Strategy: f r := (r - 1) * φ(a) is injective on primes ≥ 2, and for primes r
  -- coprime to a*b, the witnesses x = r*a, y = r*b satisfy (since r ≥ 2 and a > b)
  -- y = r*b < r*a = x and b*x = a*y. {primes not dividing a*b} is infinite.
  set S : Set ℕ := {N | ∃ x y, Nat.totient x = N ∧ Nat.totient y = N ∧ y < x ∧ b * x ≥ a * y}
  -- The set of primes coprime to a*b is infinite (primes infinite, divisors finite).
  have h_inf_good : {r : ℕ | r.Prime ∧ ¬ r ∣ (a * b)}.Infinite := by
    apply Set.Infinite.mono (s := {r | r.Prime} \ {r | r ∣ (a * b)})
    · intro r hr
      exact ⟨hr.1, hr.2⟩
    · refine Set.Infinite.diff Nat.infinite_setOf_prime ?_
      exact Set.Finite.subset (Set.finite_Icc 0 (a * b)) (fun r hr =>
        Set.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_of_dvd (Nat.mul_pos ha hb) hr⟩)
  -- Each such prime maps into S.
  have hmap : ∀ r ∈ {r : ℕ | r.Prime ∧ ¬ r ∣ (a * b)}, (r - 1) * Nat.totient a ∈ S := by
    rintro r ⟨hpr, hndvd⟩
    have hra : ¬ r ∣ a := fun h => hndvd (h.mul_right b)
    have hrb : ¬ r ∣ b := fun h => hndvd (Dvd.dvd.mul_left h a)
    have hcop_a : Nat.Coprime r a := (Nat.Prime.coprime_iff_not_dvd hpr).mpr hra
    have hcop_b : Nat.Coprime r b := (Nat.Prime.coprime_iff_not_dvd hpr).mpr hrb
    have hr2 : 2 ≤ r := hpr.two_le
    have hr_pos : 0 < r := by omega
    refine ⟨r * a, r * b, ?_, ?_, ?_, ?_⟩
    · rw [Nat.totient_mul hcop_a, Nat.totient_prime hpr]
    · rw [Nat.totient_mul hcop_b, Nat.totient_prime hpr, hab]
    · -- y = r*b < r*a = x because b < a and r > 0
      exact (Nat.mul_lt_mul_left hr_pos).mpr hgt
    · -- b * (r * a) = a * (r * b) — exact equality, hence ≥.
      ring_nf
      exact le_refl _
  -- f is injective on primes (since primes ≥ 2 and φ(a) > 0).
  have hφ_pos : 0 < Nat.totient a := Nat.totient_pos.mpr ha
  have hinj : Set.InjOn (fun r : ℕ => (r - 1) * Nat.totient a)
      {r : ℕ | r.Prime ∧ ¬ r ∣ (a * b)} := by
    rintro r ⟨hpr, _⟩ s ⟨hps, _⟩ heq
    simp only at heq
    have h2r : 2 ≤ r := hpr.two_le
    have h2s : 2 ≤ s := hps.two_le
    have : r - 1 = s - 1 := Nat.eq_of_mul_eq_mul_right hφ_pos heq
    omega
  exact (h_inf_good.image hinj).mono (Set.image_subset_iff.mpr hmap)

/-- **Asymptotic companion theorem (Section 4).**

PDF Theorem 2.1 in the natural `Tendsto` shape an asymptotic result requires.

Trust boundary: `mertens_product` + `linnik_dvd` plus
Mathlib core. There are no `sorry`s in this file. -/
theorem erdos_694_asymptotic :
    Tendsto
      (fun x : ℕ => R x /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) :=
  totient_fibre_extremes

end Erdos694

/-! ## Trust boundary audit

`#print axioms` is an info-level command: it logs the closed set of axioms
each named declaration depends on, without affecting compilation.
Expected results, where `core` denotes Mathlib's
`{propext, Classical.choice, Quot.sound}`:

* `totient_sq_ge_half`, `permanence_step`,
  `LowerConstruction.totient_a_eq_totient_b`,
  `infinitely_many_collisions` — `core` only.
* `landau_max_ratio`, `R_upper_bound`, `collision_at_height` —
  `core + mertens_product` (Linnik enters as a hypothesis, not as a global axiom).
* `totient_collision_construction`, `R_lower_bound`,
  `totient_fibre_extremes`, `erdos_694_asymptotic` —
  `core + mertens_product + linnik_dvd`.
-/
#print axioms Erdos694.totient_sq_ge_half
-- 'Erdos694.totient_sq_ge_half' depends on axioms: [propext,
-- Classical.choice, Quot.sound]
#print axioms Erdos694.permanence_step
-- 'Erdos694.permanence_step' depends on axioms: [propext,
-- Classical.choice, Quot.sound]
#print axioms Erdos694.infinitely_many_collisions
-- 'Erdos694.infinitely_many_collisions' depends on axioms: [propext,
-- Classical.choice, Quot.sound]
#print axioms Erdos694.LowerConstruction.totient_a_eq_totient_b
-- 'Erdos694.LowerConstruction.totient_a_eq_totient_b' depends on axioms: [propext,
-- Classical.choice, Quot.sound]
#print axioms Erdos694.landau_max_ratio
-- 'Erdos694.landau_max_ratio' depends on axioms: [mertens_product, propext,
-- Classical.choice, Quot.sound]
#print axioms Erdos694.R_upper_bound
-- 'Erdos694.R_upper_bound' depends on axioms: [mertens_product, propext, Classical.choice,
-- Quot.sound]
#print axioms Erdos694.collision_at_height
-- 'Erdos694.collision_at_height' depends on axioms: [mertens_product, propext,
-- Classical.choice, Quot.sound]
#print axioms Erdos694.totient_collision_construction
-- 'Erdos694.totient_collision_construction' depends on axioms: [linnik_dvd,
-- mertens_product, propext, Classical.choice, Quot.sound]
#print axioms Erdos694.R_lower_bound
-- 'Erdos694.R_lower_bound' depends on axioms: [linnik_dvd, mertens_product, propext,
-- Classical.choice, Quot.sound]
#print axioms Erdos694.totient_fibre_extremes
-- 'Erdos694.totient_fibre_extremes' depends on axioms: [linnik_dvd,
-- mertens_product, propext, Classical.choice, Quot.sound]
#print axioms Erdos694.erdos_694_asymptotic
-- 'Erdos694.erdos_694_asymptotic' depends on axioms: [linnik_dvd, mertens_product, propext,
-- Classical.choice, Quot.sound]
