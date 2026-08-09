/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1138.
https://www.erdosproblems.com/forum/thread/1138

Formalization status:
- Partial

Informal authors:
- Hrishi Sunder
- Sourish Kumrawat
- Kireet Cheri

Formal authors:
- Aristotle
- Lorenzo Luccioli

URLs:
- https://www.erdosproblems.com/forum/thread/1138#post-6243
- https://gist.githubusercontent.com/LorenzoLuccioli/c7fbdd9809a616974b5587ee526c163b/raw
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

namespace Erdos1138


/-!
# Erdős Problem #1138

This file contains a formalization of the disproof of Erdős Problem #1138, following the paper
"An Elementary Obstruction to a Uniform Prime-Gap Asymptotic"
by Hrishi Sunder, Sourish Kumrawat, and Kireet Cheri (April 2026).

## Main Definitions

* `nthPrime` — the n-th prime (0-indexed)
* `primeGap` — the gap between consecutive primes
* `realPi` — the prime counting function on ℝ
* `maxPrimeGap` — the maximal prime gap function d(x)
* `IsStrictRecordGap` — predicate for strict record prime gaps
* `AsymptoticA` — the uniform prime-gap asymptotic assertion A(C)

## Main Results

* `erdos1138_theorem` — **Theorem 1.2**: For 1 < C₁ < C₂ with C₂ - C₁ < 1/2,
  A(C₁) and A(C₂) cannot both hold.
* `erdos1138_corollary` — **Corollary 3.1**: A(C) cannot hold for every C > 1.
  This gives a negative answer to Erdős Problem #1138.
-/

open Nat Set Filter

-- ============================================================================
-- Section 0: Definitions
-- ============================================================================

/-- The n-th prime number (0-indexed): p₀ = 2, p₁ = 3, p₂ = 5, … -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The prime gap at index n: gₙ = p_{n+1} - pₙ. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- The real-valued prime counting function: π(t) = #{p ≤ ⌊t⌋₊ : p prime}. -/
noncomputable def realPi (t : ℝ) : ℕ := Nat.primeCounting ⌊t⌋₊

/-- The maximal prime gap function d(x) = max{gₙ : pₙ < x}.

For real x, the primes pₙ < x correspond to indices n < primeCounting'(⌈x⌉₊),
so d(x) is the sup of `primeGap` over `Finset.range (primeCounting' ⌈x⌉₊)`. -/
noncomputable def maxPrimeGap (x : ℝ) : ℕ :=
  Finset.sup (Finset.range (Nat.primeCounting' ⌈x⌉₊)) primeGap

/-- A strict record gap at index n: gₙ is strictly larger than all previous gaps. -/
def IsStrictRecordGap (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → primeGap m < primeGap n

/-- The assertion A(C): the prime counting function satisfies
  π(y + C·d(x)) - π(y) ~ C·d(x)/log(y)
uniformly for all y ∈ (x/2, x) as x → ∞.

Formally: for all ε > 0, there exists X such that for all x ≥ X and all y ∈ (x/2, x),
  |(π(y + Cd) - π(y)) · log(y) / (Cd) - 1| < ε
where d = maxPrimeGap(x). -/
def AsymptoticA (C : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ X : ℝ, ∀ x ≥ X, ∀ y : ℝ, x / 2 < y → y < x →
    |((realPi (y + C * (maxPrimeGap x : ℝ)) : ℝ) - (realPi y : ℝ)) *
      Real.log y / (C * (maxPrimeGap x : ℝ)) - 1| < ε

-- ============================================================================
-- Section 1: Basic prime number facts
-- ============================================================================

lemma primes_infinite : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime

lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite primes_infinite n

lemma nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono primes_infinite

lemma nthPrime_mono : Monotone nthPrime := nthPrime_strictMono.monotone

/-- Every prime is at least 2, so every nthPrime value is at least 2. -/
lemma nthPrime_ge_two (n : ℕ) : 2 ≤ nthPrime n :=
  Nat.Prime.two_le (nthPrime_prime n)

/-- The prime gap at any index is positive. -/
lemma primeGap_pos (n : ℕ) : 0 < primeGap n :=
  Nat.sub_pos_of_lt (nthPrime_strictMono n.lt_succ_self)

/-- nthPrime (n+1) = nthPrime n + primeGap n. -/
lemma nthPrime_succ_eq (n : ℕ) : nthPrime (n + 1) = nthPrime n + primeGap n :=
  Eq.symm (Nat.add_sub_of_le (nthPrime_strictMono.monotone (Nat.le_succ _)))

/-- No natural number strictly between consecutive primes is prime. -/
lemma not_prime_between_consecutive (n : ℕ) (k : ℕ)
    (hlo : nthPrime n < k) (hhi : k < nthPrime (n + 1)) : ¬Nat.Prime k := by
  have h_prime_nth :
      ∀ m, Nat.nth Nat.Prime n < m → m < Nat.nth Nat.Prime (n + 1) →
        ¬Nat.Prime m := by
    intros m hm₁ hm₂
    contrapose! hm₂
    rw [Nat.nth_eq_sInf]
    exact Nat.sInf_le ⟨hm₂, fun k hk => lt_of_le_of_lt
      (Nat.nth_monotone Nat.infinite_setOf_prime (by linarith)) hm₁⟩
  exact h_prime_nth k hlo hhi

-- ============================================================================
-- Section 2: Counting primes in gaps
-- ============================================================================

/-- `primeCounting' m = n + 1` when m is strictly between nthPrime n and nthPrime (n+1). -/
lemma primeCounting'_eq_succ_of_between {n : ℕ} {m : ℕ}
    (hlo : nthPrime n < m) (hhi : m ≤ nthPrime (n + 1)) :
    Nat.primeCounting' m = n + 1 := by
  apply le_antisymm
  · contrapose! hhi
    exact Nat.nth_lt_of_lt_count hhi
  · rw [Nat.primeCounting', Nat.count_eq_card_filter_range]
    refine le_trans ?_ (Finset.card_mono <| show Finset.image (fun k => Nat.nth Nat.Prime k)
      (Finset.range (n + 1)) ⊆ Finset.filter Nat.Prime (Finset.range m) from ?_)
    · rw [Finset.card_image_of_injective _ fun a b h =>
        Nat.nth_injective Nat.infinite_setOf_prime h]
      norm_num
    · exact Finset.image_subset_iff.mpr fun k hk => Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr <| lt_of_le_of_lt
          (Nat.nth_monotone Nat.infinite_setOf_prime <| Finset.mem_range_succ_iff.mp hk) hlo,
         Nat.prime_nth_prime k⟩

-- This generated proof compares prime-counting filters between consecutive primes.
/-- `realPi` is constant between consecutive primes. -/
lemma realPi_eq_of_in_gap {n : ℕ} {s t : ℝ}
    (hlos : (nthPrime n : ℝ) ≤ s) (hhis : s < (nthPrime (n + 1) : ℝ))
    (hlot : (nthPrime n : ℝ) ≤ t) (hhit : t < (nthPrime (n + 1) : ℝ)) :
    realPi s = realPi t := by
  have h_floor_s : (Nat.floor s : ℕ) ∈ Finset.Ico (nthPrime n) (nthPrime (n + 1)) :=
    Finset.mem_Ico.mpr ⟨Nat.le_floor hlos, Nat.floor_lt (by linarith) |>.2 hhis⟩
  have h_floor_t : (Nat.floor t : ℕ) ∈ Finset.Ico (nthPrime n) (nthPrime (n + 1)) :=
    Finset.mem_Ico.mpr ⟨Nat.le_floor hlot, Nat.floor_lt (by linarith) |>.mpr hhit⟩
  have h_primeCounting_eq : ∀ k : ℕ, nthPrime n ≤ k → k < nthPrime (n + 1) →
      Nat.primeCounting k = Nat.primeCounting (nthPrime n) := by
    intros k hk₁ hk₂
    rw [Nat.primeCounting, Nat.primeCounting,
        Nat.primeCounting', Nat.count_eq_card_filter_range,
        Nat.count_eq_card_filter_range]
    congr 1 with x
    simp_all +decide only [Finset.mem_filter, Finset.mem_range, Order.lt_add_one_iff,
      and_congr_left_iff]
    exact fun hx => ⟨fun hx' => le_of_not_gt fun hx'' => by
      have := not_prime_between_consecutive n x hx'' (by linarith)
      contradiction, fun hx' => le_trans hx' hk₁⟩
  unfold realPi
  simp_all only [Finset.mem_Ico, Std.le_refl]

-- ============================================================================
-- Section 3: maxPrimeGap at record gaps
-- ============================================================================

/-- The supremum of primeGap over a range ending at a strict record is the record value. -/
lemma finset_sup_range_record {n : ℕ} (hrec : IsStrictRecordGap n) :
    Finset.sup (Finset.range (n + 1)) primeGap = primeGap n :=
  le_antisymm
    (Finset.sup_le fun x hx => if h : x = n then h.symm ▸ le_rfl
      else le_of_lt (hrec x (Nat.lt_of_le_of_ne (Finset.mem_range_succ_iff.mp hx) h)))
    (Finset.le_sup (f := primeGap) (Finset.mem_range.mpr (Nat.lt_succ_self n)))

/-- `maxPrimeGap x = primeGap n` when x lies in the gap (nthPrime n, nthPrime (n+1))
and n is a strict record gap index. -/
lemma maxPrimeGap_eq_at_record {n : ℕ} (hrec : IsStrictRecordGap n)
    {x : ℝ} (hlo : (nthPrime n : ℝ) < x) (hhi : x < (nthPrime (n + 1) : ℝ)) :
    maxPrimeGap x = primeGap n := by
  convert finset_sup_range_record hrec using 1
  refine congr (congr rfl ?_) rfl
  refine congr_arg _ (primeCounting'_eq_succ_of_between ?_ ?_)
  · exact Nat.lt_ceil.mpr hlo
  · exact Nat.ceil_le.mpr hhi.le

-- ============================================================================
-- Section 4: Unbounded prime gaps and record gap existence
-- ============================================================================

-- The factorial construction uses generated simplification of primality divisors.
/-- Prime gaps are unbounded: for any M, there exists a gap of size ≥ M.
Proof uses the factorial argument: (M+1)!+2, ..., (M+1)!+M+1 are all composite. -/
lemma primeGap_unbounded (M : ℕ) : ∃ n : ℕ, M ≤ primeGap n := by
  have h_small_prime :
      (Finset.filter Nat.Prime (Finset.Iic ((M + 1)! + 1))).Nonempty := by
    refine ⟨2, ?_⟩
    norm_num
    linarith [Nat.self_le_factorial (M + 1)]
  obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p ≤ (M + 1)! + 1 ∧
      ∀ q, Nat.Prime q → q ≤ (M + 1)! + 1 → q ≤ p :=
    ⟨Finset.max' (Finset.filter Nat.Prime (Finset.Iic ((M + 1)! + 1)))
      h_small_prime,
     Finset.mem_filter.mp (Finset.max'_mem (Finset.filter Nat.Prime (Finset.Iic ((M + 1)! + 1)))
      h_small_prime) |>.2,
     Finset.mem_Iic.mp (Finset.mem_filter.mp (Finset.max'_mem
      (Finset.filter Nat.Prime (Finset.Iic ((M + 1)! + 1)))
      h_small_prime) |>.1),
     fun q hq hq' => Finset.le_max' _ _ <| by
       simp_all only [Finset.mem_filter, Finset.mem_Iic, and_self]⟩
  obtain ⟨n, hn⟩ : ∃ n, nthPrime n = p :=
    ⟨Nat.count Nat.Prime p, Nat.nth_count hp.1⟩
  have h_next_prime : ∀ q, Nat.Prime q → q > p → q ≥ (M + 1)! + (M + 2) := by
    intros q hq hq_gt_p
    by_contra h_contra
    obtain ⟨k, hk⟩ : ∃ k, 2 ≤ k ∧ k ≤ M + 1 ∧ q = (M + 1)! + k := by
      use q - (M + 1)!
      grind
    simp_all +decide only [prime_def_lt', and_imp, gt_iff_lt, ge_iff_le, add_le_add_iff_left,
      not_le]
    exact hq.2 k hk.1 (by linarith [Nat.self_le_factorial (M + 1)])
      (Nat.dvd_add (Nat.dvd_factorial (by linarith) (by linarith)) (dvd_refl k))
  have h_gap : nthPrime (n + 1) ≥ (M + 1)! + (M + 2) := by
    apply h_next_prime
    · exact Nat.prime_nth_prime _
    · exact hn ▸ Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self _)
  exact ⟨n, Nat.le_sub_of_add_le <| by linarith!⟩

/-- There exist infinitely many strict record prime gaps. -/
lemma exists_record_gap_ge (N : ℕ) : ∃ n ≥ N, IsStrictRecordGap n := by
  obtain ⟨n, hn1, hn2⟩ : ∃ n ≥ N, primeGap n > Finset.sup (Finset.range N) primeGap := by
    have := primeGap_unbounded (Finset.sup (Finset.range N) primeGap + 1)
    exact ⟨this.choose, le_of_not_gt fun h =>
      not_lt_of_ge (Finset.le_sup (f := primeGap) (Finset.mem_range.mpr h)) this.choose_spec,
      this.choose_spec⟩
  obtain ⟨n, hn1, hn2⟩ : ∃ n ≥ N, primeGap n > Finset.sup (Finset.range N) primeGap ∧
      ∀ m ≥ N, m < n → primeGap m ≤ Finset.sup (Finset.range N) primeGap :=
    ⟨Nat.find (⟨n, hn1, hn2⟩ : ∃ n ≥ N, primeGap n > Finset.sup (Finset.range N) primeGap),
     Nat.find_spec (⟨n, hn1, hn2⟩ : ∃ n ≥ N,
       primeGap n > Finset.sup (Finset.range N) primeGap) |>.1,
     Nat.find_spec (⟨n, hn1, hn2⟩ : ∃ n ≥ N,
       primeGap n > Finset.sup (Finset.range N) primeGap) |>.2,
     by
       intro m a a_1
       simp_all only [ge_iff_le, gt_iff_lt, lt_find_iff, not_and, not_lt, Std.le_refl]⟩
  exact ⟨n, hn1, fun m mn => lt_of_le_of_lt
    (if hm : m < N then Finset.le_sup (f := primeGap) (Finset.mem_range.mpr hm)
     else hn2.2 m (le_of_not_gt hm) mn)
    hn2.1⟩

/-- For any bound B, there exists a strict record gap with nthPrime n ≥ B. -/
lemma record_gap_arbitrarily_large (B : ℕ) :
    ∃ n, IsStrictRecordGap n ∧ 0 < n ∧ B ≤ nthPrime n := by
  obtain ⟨n, hn_ge_max, hn_rec⟩ : ∃ n ≥ Nat.max B 1, IsStrictRecordGap n :=
    exists_record_gap_ge (max B 1)
  have hn_ge_B : B ≤ n := le_trans (Nat.le_max_left B 1) hn_ge_max
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (Nat.le_max_right B 1) hn_ge_max)
  refine ⟨n, hn_rec, hn_pos, ?_⟩
  refine le_trans hn_ge_B ?_
  exact Nat.recOn n (by norm_num [nthPrime]) fun n ihn => by
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ihn
      (Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self _)))

-- ============================================================================
-- Section 5: Algebraic helpers
-- ============================================================================

/-- If 0 < C₁ < C₂ then C₁/C₂ < (1 - ε)/(1 + ε) where ε = (C₂ - C₁)/(2(C₂ + C₁)). -/
private lemma rho_lt_bound {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hlt : C₁ < C₂) :
    let ε := (C₂ - C₁) / (2 * (C₂ + C₁))
    C₁ / C₂ < (1 - ε) / (1 + ε) := by
  rw [div_lt_div_iff₀]
  · nlinarith [mul_div_cancel₀ (C₂ - C₁) (by linarith : (2 * (C₂ + C₁)) ≠ 0)]
  · grind
  · rw [add_div', lt_div_iff₀] <;> linarith

/-- Core ratio contradiction: if 0 < 1-ε < a, 0 < b < 1+ε, then (1-ε)/(1+ε) < a/b. -/
private lemma ratio_bound {a b ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (ha : 1 - ε < a) (hb : b < 1 + ε) (hb_pos : 0 < b) :
    (1 - ε) / (1 + ε) < a / b := by
  rw [div_lt_div_iff₀] <;> nlinarith

-- ============================================================================
-- Section 6: Construction helpers
-- ============================================================================

/-- The constructed z < x when η < 1/2. -/
private lemma construct_z_lt_x {P D η : ℝ} (hD : 0 < D) (hη' : η < 1 / 2) :
    P + (1/2 + η) * D < P + ((3 + 2 * η) / 4) * D := by
  nlinarith

/-- The constructed x < Q = P + D when α < 1. -/
private lemma construct_x_lt_Q {P D η : ℝ} (hD : 0 < D) (hη' : η < 1 / 2) :
    P + ((3 + 2 * η) / 4) * D < P + D := by
  nlinarith

-- ============================================================================
-- Section 7: Main theorem
-- ============================================================================

-- The final contradiction proof uses generated simplifications over many local definitions.
/-- **Theorem 1.2** (Sunder–Kumrawat–Cheri, 2026).
Let 1 < C₁ < C₂ with C₂ - C₁ < 1/2. Then A(C₁) and A(C₂) cannot both hold.

The proof constructs counterexample points from strict record prime gaps. For a record gap
at index n with pₙ = P, pₙ₊₁ = Q, D = Q - P, and η = C₂ - C₁, set:
  x = P + ((3+2η)/4) · D,   y = P + D/2,   z = P + (1/2+η) · D

Then x/2 < y < z < x, d(x) = D, π(y) = π(z), and y + C₂D = z + C₁D (same endpoint).
The asymptotic A(C₂) at y and A(C₁) at z give the same count N satisfying two different
bounds, leading to (C₁/C₂)·(log y/log z) both > and < (1-ε)/(1+ε). -/
theorem erdos1138_theorem (C₁ C₂ : ℝ) (hC₁_pos : 1 < C₁) (hlt : C₁ < C₂)
    (hη : C₂ - C₁ < 1 / 2) : ¬(AsymptoticA C₁ ∧ AsymptoticA C₂) := by
  norm_num +zetaDelta at *
  intro h₁ h₂
  obtain ⟨ε, hε_pos, hε_lt⟩ : ∃ ε > 0, ε < 1 ∧ C₁ / C₂ < (1 - ε) / (1 + ε) :=
    ⟨(C₂ - C₁) / (2 * (C₂ + C₁)), div_pos (by linarith) (by linarith),
     by rw [div_lt_iff₀] <;> linarith, rho_lt_bound (by linarith) (by linarith)⟩
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, ∀ x ≥ X₁, ∀ y : ℝ, x / 2 < y → y < x →
      |((realPi (y + C₂ * (maxPrimeGap x : ℝ)) : ℝ) - (realPi y : ℝ)) *
        Real.log y / (C₂ * (maxPrimeGap x : ℝ)) - 1| < ε :=
    h₂ ε hε_pos
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : ℝ, ∀ x ≥ X₂, ∀ y : ℝ, x / 2 < y → y < x →
      |((realPi (y + C₁ * (maxPrimeGap x : ℝ)) : ℝ) - (realPi y : ℝ)) *
        Real.log y / (C₁ * (maxPrimeGap x : ℝ)) - 1| < ε :=
    h₁ ε hε_pos
  obtain ⟨n, hn_rec, hn_pos, hn_B⟩ : ∃ n, IsStrictRecordGap n ∧ 0 < n ∧
      max (Nat.ceil (max X₁ X₂)) 3 ≤ nthPrime n :=
    record_gap_arbitrarily_large _
  set P := (nthPrime n : ℝ)
  set Q := (nthPrime (n + 1) : ℝ)
  set D := (primeGap n : ℝ)
  set η := C₂ - C₁
  set x := P + ((3 + 2 * η) / 4) * D
  set y := P + (1 / 2) * D
  set z := P + (1 / 2 + η) * D
  have hx_ge_X₁ : x ≥ X₁ := by
    norm_num +zetaDelta at *
    exact le_add_of_le_of_nonneg hn_B.1.1 (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have hx_ge_X₂ : x ≥ X₂ := by
    norm_num +zetaDelta at *
    exact le_add_of_le_of_nonneg hn_B.1.2 (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have hy_lt_z : y < z := by
    simpa [y, z, η, D] using
      add_lt_add_left
        (mul_lt_mul_of_pos_right (by linarith) (Nat.cast_pos.mpr (primeGap_pos n))) P
  have hz_lt_x : z < x :=
    construct_z_lt_x (Nat.cast_pos.mpr (primeGap_pos n)) hη
  have hx_lt_Q : x < Q := by
    have hQ_eq_P_plus_D : Q = P + D := by
      simp +zetaDelta only [ge_iff_le] at *
      exact_mod_cast nthPrime_succ_eq n
    exact hQ_eq_P_plus_D.symm ▸ construct_x_lt_Q (Nat.cast_pos.mpr (primeGap_pos n)) hη
  have hy_gt_1 : 1 < y :=
    lt_add_of_le_of_pos (Nat.one_le_cast.mpr (Nat.Prime.pos (nthPrime_prime n)))
      (mul_pos (by norm_num) (Nat.cast_pos.mpr (primeGap_pos n)))
  have hz_gt_1 : 1 < z :=
    lt_of_lt_of_le hy_gt_1 (le_of_lt hy_lt_z)
  have hmaxPrimeGap_x : maxPrimeGap x = primeGap n := by
    apply maxPrimeGap_eq_at_record hn_rec
    · exact lt_add_of_pos_right _
        (mul_pos (by linarith) (Nat.cast_pos.mpr (primeGap_pos n)))
    · exact hx_lt_Q
  have hrealPi_y_eq_realPi_z : realPi y = realPi z := by
    apply realPi_eq_of_in_gap
    any_goals exact n
    · exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    · grind
    · exact le_add_of_nonneg_right (mul_nonneg (by linarith) (Nat.cast_nonneg _))
    · linarith
  have hy_plus_C₂D_eq_z_plus_C₁D : y + C₂ * D = z + C₁ * D := by ring
  have h_ineq1 : |((realPi (y + C₂ * D) : ℝ) - (realPi y : ℝ)) *
      Real.log y / (C₂ * D) - 1| < ε := by
    convert hX₁ x hx_ge_X₁ y ?_ ?_ using 1 <;> norm_num [hmaxPrimeGap_x]
    · congr!
    · grind
    · linarith
  have h_ineq2 : |((realPi (z + C₁ * D) : ℝ) - (realPi z : ℝ)) *
      Real.log z / (C₁ * D) - 1| < ε := by
    grind +splitImp
  set N := (realPi (y + C₂ * D) : ℝ) - (realPi y : ℝ)
  have h_ineq1_simplified : N * Real.log y / (C₂ * D) > 1 - ε := by
    linarith [abs_lt.mp h_ineq1]
  have h_ineq2_simplified : N * Real.log z / (C₁ * D) < 1 + ε := by
    rw [abs_lt] at h_ineq2
    grind
  have h_ratio : (1 - ε) / (1 + ε) < (N * Real.log y / (C₂ * D)) /
      (N * Real.log z / (C₁ * D)) := by
    apply ratio_bound hε_pos hε_lt.left h_ineq1_simplified h_ineq2_simplified
    refine div_pos (mul_pos ?_ (Real.log_pos hz_gt_1))
      (mul_pos (by linarith) (Nat.cast_pos.mpr (primeGap_pos n)))
    contrapose! h_ineq1_simplified
    exact le_trans (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg h_ineq1_simplified (Real.log_nonneg (by linarith)))
      (mul_nonneg (by linarith) (Nat.cast_nonneg _))) (by linarith)
  have h_simplify : (N * Real.log y / (C₂ * D)) / (N * Real.log z / (C₁ * D)) =
      (C₁ / C₂) * (Real.log y / Real.log z) := by
    field_simp
    convert mul_div_mul_left _ _ (show N ≠ 0 from ?_) using 1
    · convert mul_div_mul_right _ _ (show D ≠ 0 from ?_) using 1
      · ring
      · exact ne_of_gt <| Nat.cast_pos.mpr <| primeGap_pos n
    · grind +locals
  have h_log_ratio : Real.log y / Real.log z < 1 := by
    rw [div_lt_one (Real.log_pos hz_gt_1)]
    exact Real.log_lt_log (by positivity) hy_lt_z
  nlinarith [show 0 < C₁ / C₂ by exact div_pos (by linarith) (by linarith)]

/-- **Corollary 3.1**. The assertion A(C) cannot hold for every fixed C > 1.
This gives a negative answer to Erdős Problem #1138. -/
theorem erdos1138_corollary : ¬(∀ C : ℝ, 1 < C → AsymptoticA C) := by
  intro h
  exact erdos1138_theorem 2 (9/4) (by norm_num) (by norm_num) (by norm_num)
    ⟨h 2 (by norm_num), h (9/4) (by norm_num)⟩

#print axioms erdos1138_corollary
-- 'Erdos1138.erdos1138_corollary' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1138
