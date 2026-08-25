/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
# Totient ratios and the arithmetic core of Erdős 694

The original proof's provenance is recorded in `ErdosProblems.Erdos694`.
This module proves the upper bound and elementary collision identities using
only standard Lean axioms and the proved Mertens product theorem.
-/

import Mathlib
import Util.MertensProduct

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

/-! ### Analytic prerequisites

The Mertens product asymptotic is supplied by `Util.MertensProduct`.
The elementary size estimates use `A_Y ≤ P_Y ≤ 4^Y`.
-/

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
      simpa [Function.comp_def, Real.log_one] using this
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

/-! ## Elementary lower-bound construction

The original prime construction has `U = (ℓ-1)/A_Y`,
`Q = ∏_{q ∣ U, Y < q} q`, `a = ℓ*Q`, and `b = P_Y*U*Q`.
Its ratio is `(P_Y/A_Y)*((ℓ-1)/ℓ)`. All identities below are elementary.
`PrimeProducts` generalizes them to a composite integer coprime to its totient;
`Height` and `Unconditional` supply the new lower-bound argument.
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


end Erdos694
