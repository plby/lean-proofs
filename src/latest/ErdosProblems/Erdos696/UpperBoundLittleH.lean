/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import ErdosProblems.Erdos696.UpperBoundH

namespace Erdos696

open scoped BigOperators Topology
open Real MeasureTheory

-- === Inlined from Erdos696/UpperBoundLittleH.lean ===
/-
# Upper bound for `h(n)`

Mirrors §4 of `erdos_696_paper.tex`.

**Theorem.** For all but `o(x)` integers `n ≤ x`,
`h(n) ≤ (1/2 + o(1)) log_* x`.

**Proof structure (paper §4).**
1. *Bad-prime-pair density* (Lemma 4.2): the set of `n ≤ x` admitting some
   `h`-bad prime pair `(p, q)` with `p ≥ Y` is `o(x)`.  Uses Brun–Titchmarsh.
2. *`U`-tower lemma for `h`* (Lemma 4.4): `f(U_m) ≤ U_{m-2}` for `m ≥ m₀*`.
3. *Tower descent for `h`* (Lemma 4.6): if `(p_i, p_{i+1})` is not bad with
   `p_i ≥ Y`, then `Urank p_i ≤ Urank p_{i+1} - 2`.
4. Assembly: each chain step descends two `U`-tower levels on average,
   plus `Y = O(L^{1/2})` small terms, giving `h(n) ≤ L/2 + O(L^{1/2})`.

NOTE: filename uses `LittleH` to avoid case-collision with
`UpperBoundH.lean` on case-insensitive (macOS default) filesystems.
-/



open Real

/-- The function `Q(p) := exp(exp(p / (log p)^2))` of equation (4.3). -/
noncomputable def Qfn (p : ℝ) : ℝ :=
  Real.exp (Real.exp (p / (Real.log p) ^ 2))

/-- **Bad prime pair** (Definition 4.1 of paper). -/
def IsHBadPrimePair (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ q % p = 1 ∧ (q : ℝ) < Qfn (p : ℝ)

/-- If a bad prime pair divides a positive integer, then the product divides it. -/
private lemma IsHBadPrimePair.mul_dvd_of_dvd {p q n : ℕ}
    (hpq : IsHBadPrimePair p q) (hpdvd : p ∣ n) (hqdvd : q ∣ n) :
    p * q ∣ n := by
  rcases hpq with ⟨hp, hq, hpq_lt, _hmod, _hq_lt⟩
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 (Nat.ne_of_lt hpq_lt)
  exact hcop.mul_dvd_of_dvd_of_dvd hpdvd hqdvd

/-- Finset version of `IsHBadPrimePair.card_multiples_le`. -/
private lemma IsHBadPrimePair.finset_card_multiples_le {p q N : ℕ}
    (hpq : IsHBadPrimePair p q) :
    ({n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n}.card) ≤ N / (p * q) := by
  classical
  rw [← Nat.Ioc_filter_dvd_card_eq_div N (p * q)]
  exact Finset.card_le_card (by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hpq.mul_dvd_of_dvd hn.2.1 hn.2.2⟩)

/-- The possible larger entries in an `h`-bad prime pair with fixed smaller
prime, truncated at `N`. -/
private noncomputable def hBadPrimeQs (p N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (p + 1) N).filter (fun q => IsHBadPrimePair p q)

/-- Majorant for the `∑ log n / n^2` part of the bad-prime-pair tail. -/
private noncomputable def logOverSq (n : ℕ) : ℝ :=
  if 1 ≤ n then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0

/-- Majorant for the `∑ 1/(n (log n)^2)` part of the bad-prime-pair tail. -/
private noncomputable def invNatLogSq (n : ℕ) : ℝ :=
  if 2 ≤ n then (1 : ℝ) / ((n : ℝ) * (Real.log n) ^ 2) else 0

private noncomputable def badPrimePairMajorant (n : ℕ) : ℝ :=
  logOverSq n + invNatLogSq n

private lemma logOverSq_nonneg (n : ℕ) : 0 ≤ logOverSq n := by
  dsimp [logOverSq]
  split_ifs with hn
  · have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  · positivity

private lemma inv_nat_mul_log_sq_antitone {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    (1 : ℝ) / ((n : ℝ) * (Real.log n) ^ 2) ≤
      1 / ((m : ℝ) * (Real.log m) ^ 2) := by
  have hmpos_nat : 0 < m := lt_of_lt_of_le (by norm_num : 0 < 2) hm
  have hnpos_nat : 0 < n := lt_of_lt_of_le hmpos_nat hmn
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hmpos_nat
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnpos_nat
  have hmone : (1 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos hmone
  have hlog_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hmpos (by exact_mod_cast hmn)
  have hsq_le : (Real.log (m : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hlogm_pos.le hlog_le 2
  have hden_pos : 0 < (m : ℝ) * (Real.log (m : ℝ)) ^ 2 := by positivity
  have hden_le :
      (m : ℝ) * (Real.log (m : ℝ)) ^ 2 ≤
        (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    exact mul_le_mul (by exact_mod_cast hmn) hsq_le (sq_nonneg _) hnpos.le
  exact one_div_le_one_div_of_le hden_pos hden_le

private lemma summable_logOverSq : Summable logOverSq := by
  apply Summable.of_nonneg_of_le
    (g := logOverSq)
    (f := fun n : ℕ => 2 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2)))
  · exact logOverSq_nonneg
  · intro n
    dsimp [logOverSq]
    split_ifs with hn
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hlog_le :
          Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) :=
        Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))
      have hlog_le' : Real.log (n : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        norm_num at hlog_le ⊢
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog_le
      calc
        Real.log (n : ℝ) / (n : ℝ) ^ 2 ≤
            (2 * (n : ℝ) ^ ((1 : ℝ) / 2)) / (n : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right hlog_le' (by positivity)
        _ = 2 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2)) := by
          rw [div_eq_mul_inv, mul_assoc]
          congr 1
          rw [← Real.rpow_natCast]
          calc
            (n : ℝ) ^ ((1 : ℝ) / 2) * ((n : ℝ) ^ (2 : ℝ))⁻¹
                = (n : ℝ) ^ ((1 : ℝ) / 2 - 2) := by
                  rw [← Real.rpow_neg hnpos.le, ← Real.rpow_add hnpos]
                  ring_nf
            _ = ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
                  rw [← Real.rpow_neg hnpos.le]
                  ring_nf
          simp [one_div]
    · positivity
  · exact (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < (3 : ℝ) / 2)).mul_left 2

private lemma summable_invNatLogSq : Summable invNatLogSq := by
  rw [← summable_condensed_iff_of_eventually_nonneg]
  · have hbase :
        Summable fun k : ℕ => (1 / (Real.log 2) ^ 2) * (1 / (k : ℝ) ^ (2 : ℝ)) := by
      exact (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < (2 : ℝ))).mul_left _
    refine (summable_congr_atTop ?_).mp hbase
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkpos : 0 < k := by omega
    have h2k : 2 ≤ 2 ^ k := by
      cases k with
      | zero => omega
      | succ k =>
          have hpos : 0 < 2 ^ k := Nat.pow_pos (by norm_num : 0 < 2)
          simpa [pow_succ] using Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hpos)
    have hpow_pos : (0 : ℝ) < (2 : ℕ) ^ k := by
      exact_mod_cast (Nat.pow_pos (by norm_num : 0 < 2) : 0 < 2 ^ k)
    have hkposR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hlogpow : Real.log (((2 ^ k : ℕ) : ℝ)) = (k : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    rw [invNatLogSq, if_pos h2k, hlogpow]
    have hlog2_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hpow_pos.ne', hkposR.ne', hlog2_ne]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    norm_num [Real.rpow_natCast]
    ring_nf
  · exact (Filter.eventually_ge_atTop 2).mono (by
      intro n hn
      dsimp [invNatLogSq]
      split_ifs with h2n
      · positivity
      · omega)
  · exact (Filter.eventually_ge_atTop 2).mono (by
      intro n hn
      dsimp [invNatLogSq]
      have hn2 : 2 ≤ n := hn
      have h2succ : 2 ≤ n + 1 := by omega
      have h := inv_nat_mul_log_sq_antitone hn2 (Nat.le_succ n)
      simpa [hn2, h2succ, Nat.cast_add, Nat.cast_one, one_div, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc] using h)

private lemma summable_badPrimePairMajorant : Summable badPrimePairMajorant := by
  exact summable_logOverSq.add summable_invNatLogSq

private lemma badPrimePairMajorant_eq_of_two_le {p : ℕ} (hp : 2 ≤ p) :
    badPrimePairMajorant p =
      Real.log (p : ℝ) / (p : ℝ) ^ 2 +
        1 / ((p : ℝ) * (Real.log p) ^ 2) := by
  have hp1 : 1 ≤ p := hp.trans' (by norm_num)
  simp [badPrimePairMajorant, logOverSq, invNatLogSq, hp1, hp]

/-- **Lemma 4.2 (bad-prime-pair density for `h`).**

The number of integers `n ≤ x` such that some `h`-bad prime pair `(p, q)`
with `p ≥ Y` divides `n` is `o(x)` as `Y → ∞`.

Sketch: Brun–Titchmarsh gives `S(p) ≪ (log p)/p + 1/(log p)^2`; summing
`S(p)/p` over `p ≥ Y` gives a convergent series.

Uses `brun_titchmarsh` (Lemma 2.2). -/
lemma bad_prime_pair_density_h :
    ∀ ε : ℝ, 0 < ε →
      ∃ Y₀ : ℝ, 0 < Y₀ ∧
        ∀ x : ℝ, 1 ≤ x →
          ∀ Y : ℝ, Y₀ ≤ Y →
            (Nat.card
                {n : ℕ | 0 < n ∧ n ≤ ⌊x⌋₊ ∧
                   ∃ p q : ℕ, IsHBadPrimePair p q ∧ (p : ℝ) ≥ Y ∧
                     p ∣ n ∧ q ∣ n} : ℝ) ≤ ε * x := by
  classical
  intro ε hε
  rcases bt_reciprocal_AP_tail with ⟨C, hCpos, hBT⟩
  have hmaj_sum : Summable fun n : ℕ => C * badPrimePairMajorant n :=
    summable_badPrimePairMajorant.mul_left C
  have htail := hmaj_sum.nat_tsum_vanishing
    (Iio_mem_nhds hε : Set.Iio ε ∈ nhds (0 : ℝ))
  rcases htail with ⟨K, hK⟩
  refine ⟨max 2 (K : ℝ), by positivity, ?_⟩
  intro x hx Y hY
  let N : ℕ := ⌊x⌋₊
  let D : ℕ := ⌈Y⌉₊
  let P : Finset ℕ := (Finset.Icc D N).filter Nat.Prime
  let S : Finset ℕ := {n ∈ Finset.Ioc 0 N |
    ∃ p q : ℕ, IsHBadPrimePair p q ∧ (p : ℝ) ≥ Y ∧ p ∣ n ∧ q ∣ n}
  let U : Finset ℕ := P.biUnion fun p =>
    (hBadPrimeQs p N).biUnion fun q => {n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n}
  have hx_nonneg : 0 ≤ x := le_trans (by norm_num) hx
  have hN_le_x : (N : ℝ) ≤ x := by
    simpa [N] using (Nat.floor_le hx_nonneg)
  have hY_ge_K : (K : ℝ) ≤ Y := by
    exact (le_max_right (2 : ℝ) (K : ℝ)).trans (hY.trans_eq (by rfl))
  have hS_subset : S ⊆ U := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Ioc] at hn
    rcases hn with ⟨hnIoc, p, q, hbad, hpY, hpn, hqn⟩
    rcases hbad with ⟨hpprime, hqprime, hpq_lt, hmod, hq_lt⟩
    have hnpos : 0 < n := hnIoc.1
    have hnle : n ≤ N := hnIoc.2
    have hp_le_n : p ≤ n := Nat.le_of_dvd hnpos hpn
    have hq_le_n : q ≤ n := Nat.le_of_dvd hnpos hqn
    have hD_le_p : D ≤ p := (Nat.ceil_le).2 hpY
    have hp_le_N : p ≤ N := hp_le_n.trans hnle
    have hq_le_N : q ≤ N := hq_le_n.trans hnle
    have hq_mem : q ∈ hBadPrimeQs p N := by
      dsimp [hBadPrimeQs]
      exact Finset.mem_filter.2
        ⟨by simp [Nat.succ_le_of_lt hpq_lt, hq_le_N],
          ⟨hpprime, hqprime, hpq_lt, hmod, hq_lt⟩⟩
    simp only [U, Finset.mem_biUnion]
    refine ⟨p, ?_, q, hq_mem, ?_⟩
    · simp [P, hpprime, hD_le_p, hp_le_N]
    · simp [hnIoc, hpn, hqn]
  have hcard_nat : S.card ≤
      ∑ p ∈ P, ∑ q ∈ hBadPrimeQs p N,
        ({n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n}.card) := by
    calc
      S.card ≤ U.card := Finset.card_le_card hS_subset
      _ ≤ ∑ p ∈ P,
            ((hBadPrimeQs p N).biUnion fun q =>
              {n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n}).card := by
          exact Finset.card_biUnion_le
      _ ≤ ∑ p ∈ P, ∑ q ∈ hBadPrimeQs p N,
            ({n ∈ Finset.Ioc 0 N | p ∣ n ∧ q ∣ n}.card) := by
          apply Finset.sum_le_sum
          intro p _hp
          exact Finset.card_biUnion_le
  have hcard_nat_div : S.card ≤
      ∑ p ∈ P, ∑ q ∈ hBadPrimeQs p N, N / (p * q) := by
    exact hcard_nat.trans (by
      apply Finset.sum_le_sum
      intro p _hp
      apply Finset.sum_le_sum
      intro q hq
      have hbad : IsHBadPrimePair p q := by
        dsimp [hBadPrimeQs] at hq
        exact (Finset.mem_filter.mp hq).2
      exact hbad.finset_card_multiples_le)
  have hcard_real : (S.card : ℝ) ≤
      ∑ p ∈ P, ∑ q ∈ hBadPrimeQs p N, ((N / (p * q) : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat_div
  have hdiv_to_real :
      (∑ p ∈ P, ∑ q ∈ hBadPrimeQs p N, ((N / (p * q) : ℕ) : ℝ)) ≤
        ∑ p ∈ P, ∑ q ∈ hBadPrimeQs p N, x / ((p : ℝ) * (q : ℝ)) := by
    apply Finset.sum_le_sum
    intro p _hp
    apply Finset.sum_le_sum
    intro q hq
    have hbad : IsHBadPrimePair p q := by
      dsimp [hBadPrimeQs] at hq
      exact (Finset.mem_filter.mp hq).2
    have hppos_nat : 0 < p := hbad.1.pos
    have hqpos_nat : 0 < q := hbad.2.1.pos
    have hdenpos : 0 < ((p * q : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hppos_nat hqpos_nat
    calc
      ((N / (p * q) : ℕ) : ℝ) ≤ (N : ℝ) / ((p * q : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ x / ((p * q : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right hN_le_x hdenpos.le
      _ = x / ((p : ℝ) * (q : ℝ)) := by norm_num
  have hinner :
      (∑ p ∈ P, ∑ q ∈ hBadPrimeQs p N, x / ((p : ℝ) * (q : ℝ))) ≤
        ∑ p ∈ P, x * (C * badPrimePairMajorant p) := by
    apply Finset.sum_le_sum
    intro p hpP
    have hpprime : p.Prime := by
      simpa [P] using (Finset.mem_filter.mp hpP).2
    have hp2 : 2 ≤ p := hpprime.two_le
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hq_sum_le :
        (∑ q ∈ hBadPrimeQs p N, (1 : ℝ) / (q : ℝ)) ≤
          C * (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2) := by
      have hsubset :
          hBadPrimeQs p N ⊆
            Finset.filter
              (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧
                (q : ℝ) ≤ Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2)))
              (Finset.Iic ⌊Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2))⌋₊) := by
        intro q hq
        dsimp [hBadPrimeQs] at hq
        rcases Finset.mem_filter.mp hq with ⟨_hqIcc, hbad⟩
        rcases hbad with ⟨_hp, hqprime, hpq_lt, hmod, hq_lt⟩
        have hq_le_Q :
            (q : ℝ) ≤ Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2)) := by
          simpa [Qfn] using hq_lt.le
        have hq_floor :
            q ≤ ⌊Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2))⌋₊ := by
          apply Nat.le_floor
          exact hq_le_Q
        simp [hq_floor, hqprime, hpq_lt, hmod, hq_le_Q]
      have hsum_subset :
          (∑ q ∈ hBadPrimeQs p N, (1 : ℝ) / (q : ℝ)) ≤
            ∑ q ∈ Finset.filter
              (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧
                (q : ℝ) ≤ Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2)))
              (Finset.Iic ⌊Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2))⌋₊),
              (1 : ℝ) / (q : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro q _hq _hnot
          positivity)
      exact hsum_subset.trans (hBT p hpprime hp2)
    calc
      (∑ q ∈ hBadPrimeQs p N, x / ((p : ℝ) * (q : ℝ)))
          = (x / (p : ℝ)) * (∑ q ∈ hBadPrimeQs p N, (1 : ℝ) / (q : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _hq
        field_simp [hppos.ne']
      _ ≤ (x / (p : ℝ)) *
            (C * (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2)) := by
        have hcoef_nonneg : 0 ≤ x / (p : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hq_sum_le hcoef_nonneg
      _ = x * (C * badPrimePairMajorant p) := by
        rw [badPrimePairMajorant_eq_of_two_le hp2]
        field_simp [hppos.ne']
  have htailP_lt : (∑ p ∈ P, C * badPrimePairMajorant p) < ε := by
    have hsubset_tail : (↑P : Set ℕ) ⊆ {n | K ≤ n} := by
      intro p hpP
      have hp_mem : p ∈ P := hpP
      have hD_le_p : D ≤ p := by
        simpa [P] using (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_mem).1).1
      have hY_le_D : Y ≤ (D : ℝ) := by simpa [D] using Nat.le_ceil Y
      have hK_le_p_real : (K : ℝ) ≤ (p : ℝ) :=
        hY_ge_K.trans (hY_le_D.trans (by exact_mod_cast hD_le_p))
      exact_mod_cast hK_le_p_real
    have htsum_lt : (∑' p : (↑P : Set ℕ), C * badPrimePairMajorant (p : ℕ)) < ε := by
      simpa [Set.mem_Iio] using hK (↑P : Set ℕ) hsubset_tail
    change (∑' p : {p // p ∈ P}, C * badPrimePairMajorant (p : ℕ)) < ε at htsum_lt
    have htsum_eq :
        (∑' p : {p // p ∈ P}, C * badPrimePairMajorant (p : ℕ)) =
          ∑ p ∈ P, C * badPrimePairMajorant p := by
      simpa using (Finset.tsum_subtype P (fun p => C * badPrimePairMajorant p))
    rwa [htsum_eq] at htsum_lt
  have htailP_le : (∑ p ∈ P, C * badPrimePairMajorant p) ≤ ε := le_of_lt htailP_lt
  have hS_bound : (S.card : ℝ) ≤ ε * x := by
    calc
      (S.card : ℝ)
          ≤ ∑ p ∈ P, ∑ q ∈ hBadPrimeQs p N, ((N / (p * q) : ℕ) : ℝ) :=
            hcard_real
      _ ≤ ∑ p ∈ P, ∑ q ∈ hBadPrimeQs p N, x / ((p : ℝ) * (q : ℝ)) := hdiv_to_real
      _ ≤ ∑ p ∈ P, x * (C * badPrimePairMajorant p) := hinner
      _ = x * (∑ p ∈ P, C * badPrimePairMajorant p) := by rw [Finset.mul_sum]
      _ ≤ x * ε := mul_le_mul_of_nonneg_left htailP_le hx_nonneg
      _ = ε * x := by ring
  change (Nat.card {n : ℕ | 0 < n ∧ n ≤ N ∧
    ∃ p q : ℕ, IsHBadPrimePair p q ∧ (p : ℝ) ≥ Y ∧ p ∣ n ∧ q ∣ n} : ℝ) ≤
      ε * x
  rw [Nat.subtype_card S]
  · exact hS_bound
  · intro n
    simp [S, and_assoc]

private lemma log_log_Um_eq (m : ℕ) (hm : 2 ≤ m) :
    Real.log (Real.log (Um m)) = tower (m - 2) + Real.log 3 := by
  rw [show m = (m - 1) + 1 by omega, log_Um_succ]
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (tower_pos (m - 1)).ne']
  rw [show m - 1 = (m - 2) + 1 by omega, log_tower_succ]
  rw [show m - 2 + 1 + 1 - 2 = m - 2 by omega]
  ring

private lemma log_div_sq_le_of_Qfn_le_Um {p m : ℕ} (hQ : Qfn (p : ℝ) ≤ Um m)
    (hm : 2 ≤ m) :
    (p : ℝ) / (Real.log p) ^ 2 ≤ tower (m - 2) + Real.log 3 := by
  let A : ℝ := (p : ℝ) / (Real.log p) ^ 2
  have hQ_pos : 0 < Qfn (p : ℝ) := by
    unfold Qfn
    positivity
  have hlogQ_le : Real.log (Qfn (p : ℝ)) ≤ Real.log (Um m) :=
    Real.log_le_log hQ_pos hQ
  have hlogQ_eq : Real.log (Qfn (p : ℝ)) = Real.exp A := by
    simp [Qfn, A]
  have h_expA_le : Real.exp A ≤ Real.log (Um m) := by
    simpa [hlogQ_eq] using hlogQ_le
  have hA_le : A ≤ Real.log (Real.log (Um m)) := by
    calc
      A = Real.log (Real.exp A) := by rw [Real.log_exp]
      _ ≤ Real.log (Real.log (Um m)) := Real.log_le_log (Real.exp_pos A) h_expA_le
  simpa [A, log_log_Um_eq m hm] using hA_le

private lemma real_le_cube_of_log_div_sq_le {P y : ℝ} (hP100 : 100 ≤ P)
    (hy1024 : 1024 ≤ y) (hlog3_le : Real.log 3 ≤ y)
    (hineq : P / (Real.log P) ^ 2 ≤ y + Real.log 3) : P ≤ y ^ 3 := by
  by_contra hnot
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hP0 : 0 < P := by linarith
  have hP_nonneg : 0 ≤ P := hP0.le
  have hlog_pos : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog_sq_pos : 0 < (Real.log P) ^ 2 := sq_pos_of_pos hlog_pos
  have hlog_nonneg : 0 ≤ Real.log P := hlog_pos.le
  have hlog_sq_le : (Real.log P) ^ 2 ≤ 16 * Real.sqrt P := by
    have hlog_le : Real.log P ≤ 4 * P ^ ((1 : ℝ) / 4) := by
      have h := Real.log_le_rpow_div (x := P) (ε := (1 : ℝ) / 4) hP_nonneg
        (by norm_num)
      norm_num at h ⊢
      linarith
    calc
      (Real.log P) ^ 2 ≤ (4 * P ^ ((1 : ℝ) / 4)) ^ 2 := by
        exact pow_le_pow_left₀ hlog_nonneg hlog_le 2
      _ = 16 * Real.sqrt P := by
        rw [mul_pow]
        have hroot : (P ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) = Real.sqrt P := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hP_nonneg]
          norm_num [Real.sqrt_eq_rpow]
        rw [hroot]
        norm_num
  have hcube_lt : y ^ 3 < P := lt_of_not_ge hnot
  have hsum_le : y + Real.log 3 ≤ 2 * y := by linarith
  have hsq_le_cube : (16 * (y + Real.log 3)) ^ 2 ≤ y ^ 3 := by
    calc
      (16 * (y + Real.log 3)) ^ 2 ≤ (16 * (2 * y)) ^ 2 := by
        have hleft_nonneg : 0 ≤ 16 * (y + Real.log 3) := by positivity
        have hmul : 16 * (y + Real.log 3) ≤ 16 * (2 * y) := by nlinarith
        exact pow_le_pow_left₀ hleft_nonneg hmul 2
      _ = 1024 * y ^ 2 := by ring
      _ ≤ y ^ 3 := by nlinarith
  have hsum_lt_sqrt : y + Real.log 3 < Real.sqrt P / 16 := by
    have hsq_lt : (16 * (y + Real.log 3)) ^ 2 < P := lt_of_le_of_lt hsq_le_cube hcube_lt
    have hmul_lt : 16 * (y + Real.log 3) < Real.sqrt P :=
      (Real.lt_sqrt (by positivity)).2 hsq_lt
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt P := Real.sqrt_pos.2 hP0
  have hlower : Real.sqrt P / 16 ≤ P / (Real.log P) ^ 2 := by
    calc
      Real.sqrt P / 16 = P / (16 * Real.sqrt P) := by
        field_simp [hsqrt_pos.ne']
        rw [Real.sq_sqrt hP_nonneg]
      _ ≤ P / (Real.log P) ^ 2 := by
        exact div_le_div_of_nonneg_left hP_nonneg hlog_sq_pos hlog_sq_le
  nlinarith

private lemma tower_four_ge_1024 : (1024 : ℝ) ≤ tower 4 := by
  have h_exp9_gt_512 : (512 : ℝ) < Real.exp 9 := by
    calc
      (512 : ℝ) = (2 : ℝ) ^ 9 := by norm_num
      _ < (Real.exp 1) ^ 9 := by
        exact pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
      _ = Real.exp 9 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have ht3_gt_512 : (512 : ℝ) < tower 3 := by
    calc
      (512 : ℝ) < Real.exp 9 := h_exp9_gt_512
      _ < Real.exp (tower 2) := Real.exp_lt_exp.mpr tower_two_gt_nine
      _ = tower 3 := by norm_num [tower]
  have ht4_gt_1024 : (1024 : ℝ) < tower 4 := by
    calc
      (1024 : ℝ) < Real.exp 1 * (512 : ℝ) := by
        nlinarith [Real.exp_one_gt_two]
      _ ≤ Real.exp 1 * tower 3 := by
        exact mul_le_mul_of_nonneg_left ht3_gt_512.le (by positivity)
      _ ≤ Real.exp (tower 3) := Real.exp_one_mul_le_exp
      _ = tower 4 := by norm_num [tower]
  exact ht4_gt_1024.le

private lemma le_Um_sub_two_of_Qfn_le_Um {p m : ℕ} (hp : 100 ≤ p) (hm : 6 ≤ m)
    (hQ : Qfn (p : ℝ) ≤ Um m) : (p : ℝ) ≤ Um (m - 2) := by
  have hineq := log_div_sq_le_of_Qfn_le_Um (p := p) (m := m) hQ (by omega)
  have hP100 : (100 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hmono : Monotone tower := (strictMono_nat_of_lt_succ tower_lt_succ).monotone
  have hy1024 : (1024 : ℝ) ≤ tower (m - 2) :=
    tower_four_ge_1024.trans (hmono (by omega))
  have hlog3_le : Real.log 3 ≤ tower (m - 2) := by
    have hlog3_le_1024 : Real.log 3 ≤ (1024 : ℝ) := by
      have h : Real.log (3 : ℝ) ≤ (3 : ℝ) := Real.log_le_self (by norm_num)
      linarith
    exact hlog3_le_1024.trans hy1024
  have hp_le_tower_cube : (p : ℝ) ≤ tower (m - 2) ^ 3 :=
    real_le_cube_of_log_div_sq_le hP100 hy1024 hlog3_le hineq
  simpa [Um] using hp_le_tower_cube

/-- **Lemma 4.6 (tower descent for `h`).**

If `(p_i, p_{i+1})` is not `h`-bad with `p_i ≥ Y ≥ 100` and
`Urank p_{i+1} ≥ m₀*`, then `Urank p_i ≤ Urank p_{i+1} - 2`.

Combines `U_tower_h` from `Tower.lean` with `p_bound_from_Q` and the
definition of `Urank`.

Refactored 2026-04-28: af-017 found that hypothesis `m₀ ≤ Urank pnext`
was insufficient (no link to U_tower_h's existential threshold). Now
takes `Cf > 0` and uses `(U_tower_h Cf hCf).choose` so the proof can
extract the threshold and apply U_tower_h's universal property. -/
lemma tower_descent_h (pi pnext : ℕ) (hpi : 100 ≤ pi)
    (h_pi_prime : pi.Prime) (h_pnext_prime : pnext.Prime)
    (h_no_bad : ¬ IsHBadPrimePair pi pnext)
    (h_chain : pi < pnext ∧ pnext % pi = 1)
    (Cf : ℝ) (hCf : 0 < Cf)
    (h_rank : (U_tower_h Cf hCf).choose ≤ Urank pnext) :
    Urank pi ≤ Urank pnext - 2 := by
  let m := Urank pnext
  have hm_rank : (U_tower_h Cf hCf).choose ≤ m := by simpa [m] using h_rank
  obtain ⟨hm0_ge_6, _hthresh⟩ := (U_tower_h Cf hCf).choose_spec
  have hm6 : 6 ≤ m := le_trans hm0_ge_6 hm_rank
  have hpnext_le_Um : (pnext : ℝ) ≤ Um m := by simpa [m] using Urank_spec pnext
  have hnot_lt : ¬ (pnext : ℝ) < Qfn (pi : ℝ) := by
    intro hlt
    exact h_no_bad ⟨h_pi_prime, h_pnext_prime, h_chain.1, h_chain.2, hlt⟩
  have hQ_le_Um : Qfn (pi : ℝ) ≤ Um m := (le_of_not_gt hnot_lt).trans hpnext_le_Um
  have hpi_le : (pi : ℝ) ≤ Um (m - 2) := le_Um_sub_two_of_Qfn_le_Um hpi hm6 hQ_le_Um
  have hres : Urank pi ≤ m - 2 := Urank_le_of_le_Um hpi_le
  simpa [m] using hres

/-- The tail of a nontrivial prime chain is again a prime chain. -/
private lemma IsPrimeChain.tail_cons {n p q : ℕ} {rest : List ℕ}
    (hps : IsPrimeChain n (p :: q :: rest)) : IsPrimeChain n (q :: rest) := by
  rcases hps with ⟨hprime, hpair, hmod⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact hprime a (by simp [ha])
  · exact hpair.tail
  · intro i hi
    let j : Fin (p :: q :: rest).length := ⟨i.val + 1, by simp at hi ⊢; omega⟩
    have hj : j.val + 1 < (p :: q :: rest).length := by
      dsimp [j]
      simp at hi ⊢
      omega
    have := hmod j hj
    simpa [j] using this

/-- The first two entries of a nontrivial prime chain satisfy the chain relation. -/
private lemma IsPrimeChain.head_rel {n p q : ℕ} {rest : List ℕ}
    (hps : IsPrimeChain n (p :: q :: rest)) : p < q ∧ q % p = 1 := by
  rcases hps with ⟨_hprime, hpair, hmod⟩
  constructor
  · exact hpair.rel_head_tail (by simp)
  · have := hmod ⟨0, by simp⟩ (by simp)
    simpa using this

/-- A prime appearing in a positive prime chain has `U`-rank at most that of `n`. -/
private lemma Urank_le_of_mem_primeChain {n p : ℕ} {ps : List ℕ} (hn : 0 < n)
    (hps : IsPrimeChain n ps) (hpmem : p ∈ ps) : Urank p ≤ Urank n := by
  exact Urank_mono (Nat.le_of_dvd hn ((hps.1 p hpmem).2))

/-- If an integer is above a `U`-threshold, its `U`-rank is at least that threshold. -/
private lemma threshold_le_Urank_of_Um_lt {M d : ℕ} (h : Um M < (d : ℝ)) :
    M ≤ Urank d := by
  by_contra hM
  have hr : Urank d < M := Nat.lt_of_not_ge hM
  have hle : (d : ℝ) ≤ Um M := (Urank_spec d).trans (Um_mono hr.le)
  exact (not_lt_of_ge hle) h

/-- Recursive doubled budget for a prime chain with no bad large adjacent pair. -/
private lemma prime_chain_two_length_aux {n T : ℕ} (Cf : ℝ) (hCf : 0 < Cf)
    (hT100 : 100 ≤ T) (hTU : Um ((U_tower_h Cf hCf).choose) < (T : ℝ))
    (hn : 0 < n)
    (hnoT : ∀ p q : ℕ, T ≤ p → p ∣ n → q ∣ n → ¬ IsHBadPrimePair p q) :
    ∀ (p : ℕ) (rest : List ℕ), IsPrimeChain n (p :: rest) →
      (p < T → 2 * (p :: rest).length ≤ 2 * (T - p) + Urank n + 2) ∧
      (T ≤ p → 2 * (p :: rest).length ≤ Urank n - Urank p + 2) := by
  intro p rest
  induction rest generalizing p with
  | nil =>
      intro hps
      constructor
      · intro _hpT
        change 2 ≤ 2 * (T - p) + Urank n + 2
        omega
      · intro _hTp
        have hrp : Urank p ≤ Urank n := Urank_le_of_mem_primeChain hn hps (by simp)
        change 2 ≤ Urank n - Urank p + 2
        omega
  | cons q rest ih =>
      intro hps
      have htail : IsPrimeChain n (q :: rest) := hps.tail_cons
      have hrel : p < q ∧ q % p = 1 := hps.head_rel
      have hp_prime : p.Prime := (hps.1 p (by simp)).1
      have hq_prime : q.Prime := (hps.1 q (by simp)).1
      have hpdvd : p ∣ n := (hps.1 p (by simp)).2
      have hqdvd : q ∣ n := (hps.1 q (by simp)).2
      have hrq : Urank q ≤ Urank n := Urank_le_of_mem_primeChain hn htail (by simp)
      constructor
      · intro hpT
        by_cases hqT : q < T
        · have htail_bound := (ih q htail).1 hqT
          change 2 * ((q :: rest).length + 1) ≤ 2 * (T - p) + Urank n + 2
          omega
        · have hTq : T ≤ q := le_of_not_gt hqT
          have htail_bound := (ih q htail).2 hTq
          change 2 * ((q :: rest).length + 1) ≤ 2 * (T - p) + Urank n + 2
          omega
      · intro hTp
        have hno_bad : ¬ IsHBadPrimePair p q := hnoT p q hTp hpdvd hqdvd
        have hT_q_real : (T : ℝ) ≤ (q : ℝ) := by exact_mod_cast (hTp.trans hrel.1.le)
        have hrank_q : (U_tower_h Cf hCf).choose ≤ Urank q :=
          threshold_le_Urank_of_Um_lt (hTU.trans_le hT_q_real)
        have hq_rank_ge2 : 2 ≤ Urank q := by
          have hchoose_ge6 : 6 ≤ (U_tower_h Cf hCf).choose :=
            (U_tower_h Cf hCf).choose_spec.1
          omega
        have hdesc : Urank p ≤ Urank q - 2 :=
          tower_descent_h p q (hT100.trans hTp) hp_prime hq_prime hno_bad hrel Cf hCf
            hrank_q
        have htail_bound := (ih q htail).2 (hTp.trans hrel.1.le)
        change 2 * ((q :: rest).length + 1) ≤ Urank n - Urank p + 2
        omega

/-- A prime chain is bounded by half the rank of `n`, plus the number of small entries. -/
private lemma prime_chain_length_le_half_rank_add {n T : ℕ} (Cf : ℝ) (hCf : 0 < Cf)
    (hT100 : 100 ≤ T) (hTU : Um ((U_tower_h Cf hCf).choose) < (T : ℝ))
    (hn : 0 < n)
    (hnoT : ∀ p q : ℕ, T ≤ p → p ∣ n → q ∣ n → ¬ IsHBadPrimePair p q)
    {ps : List ℕ} (hps : IsPrimeChain n ps) : ps.length ≤ T + Urank n / 2 + 1 := by
  cases ps with
  | nil => simp
  | cons p rest =>
      have htwo :=
        prime_chain_two_length_aux Cf hCf hT100 hTU hn hnoT p rest hps
      have htwo_bound : 2 * (p :: rest).length ≤ 2 * T + Urank n + 2 := by
        by_cases hpT : p < T
        · exact (htwo.1 hpT).trans (by omega)
        · exact (htwo.2 (le_of_not_gt hpT)).trans (by omega)
      omega

/-- If `n` has no bad prime pair with smaller entry at least `T`, then `hChain n`
is bounded by half the `U`-rank of `n`, up to the small-prime cutoff. -/
private lemma hChain_le_half_rank_add_of_no_bad {n T : ℕ} (Cf : ℝ) (hCf : 0 < Cf)
    (hT100 : 100 ≤ T) (hTU : Um ((U_tower_h Cf hCf).choose) < (T : ℝ))
    (hn : 0 < n)
    (hnoT : ∀ p q : ℕ, T ≤ p → p ∣ n → q ∣ n → ¬ IsHBadPrimePair p q) :
    hChain n ≤ T + Urank n / 2 + 1 := by
  classical
  have hne : ({ℓ | ∃ ps : List ℕ, IsPrimeChain n ps ∧ ps.length = ℓ} : Set ℕ).Nonempty :=
    ⟨0, ⟨[], by simp [IsPrimeChain]⟩⟩
  dsimp [hChain]
  exact csSup_le hne (by
    intro ℓ hℓ
    rcases hℓ with ⟨ps, hps, rfl⟩
    exact prime_chain_length_le_half_rank_add Cf hCf hT100 hTU hn hnoT hps)

/-- Deterministic part of the upper-bound proof for `h`: away from large bad prime
pairs, all sufficiently large `n` satisfy the desired bound. -/
private lemma eventually_good_upper_bound_h (ε : ℝ) (hε : 0 < ε) (T : ℕ)
    (Cf : ℝ) (hCf : 0 < Cf) (hT100 : 100 ≤ T)
    (hTU : Um ((U_tower_h Cf hCf).choose) < (T : ℝ)) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (¬ ∃ p q : ℕ, IsHBadPrimePair p q ∧ (T : ℝ) ≤ p ∧ p ∣ n ∧ q ∣ n) →
          (hChain n : ℝ) ≤ (1 / 2 + ε) * (logStar (n : ℝ) : ℝ) := by
  let L₀ : ℕ := max 1 ⌈((T + 1 : ℝ) / ε)⌉₊
  have hT_le_eps_L₀ : (T + 1 : ℝ) ≤ ε * (L₀ : ℝ) := by
    have hceil0 : ((T + 1 : ℝ) / ε) ≤ (⌈((T + 1 : ℝ) / ε)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hceil : ((T + 1 : ℝ) / ε) ≤ (L₀ : ℝ) := by
      exact hceil0.trans (by simp [L₀])
    have hmul := mul_le_mul_of_nonneg_left hceil hε.le
    field_simp [hε.ne'] at hmul
    simpa [mul_comm] using hmul
  rcases eventually_logStar_ge L₀ with ⟨N₀, hN₀⟩
  refine ⟨max 1 N₀, le_max_left _ _, ?_⟩
  intro n hn hno
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hn)
  have hN₀n : N₀ ≤ n := (le_max_right _ _).trans hn
  have hlog_ge : L₀ ≤ logStar (n : ℝ) := hN₀ n hN₀n
  have hnoT : ∀ p q : ℕ, T ≤ p → p ∣ n → q ∣ n → ¬ IsHBadPrimePair p q := by
    intro p q hTp hpvd hqvd hbad
    exact hno ⟨p, q, hbad, by exact_mod_cast hTp, hpvd, hqvd⟩
  have hh_nat : hChain n ≤ T + Urank n / 2 + 1 :=
    hChain_le_half_rank_add_of_no_bad Cf hCf hT100 hTU hn_pos hnoT
  have hU : Urank n ≤ logStar (n : ℝ) := Urank_le_logStar n
  have hT_eps_log : (T + 1 : ℝ) ≤ ε * (logStar (n : ℝ) : ℝ) := by
    exact hT_le_eps_L₀.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hlog_ge) hε.le)
  have hU_half : ((Urank n / 2 : ℕ) : ℝ) ≤ (logStar (n : ℝ) : ℝ) / 2 := by
    have htwonat : 2 * (Urank n / 2) ≤ Urank n := by omega
    have htworeal : ((2 * (Urank n / 2) : ℕ) : ℝ) ≤ (Urank n : ℝ) := by
      exact_mod_cast htwonat
    have hUreal : (Urank n : ℝ) ≤ (logStar (n : ℝ) : ℝ) := by exact_mod_cast hU
    norm_num at htworeal
    nlinarith
  have hmain : ((T + Urank n / 2 + 1 : ℕ) : ℝ) ≤
      (1 / 2 + ε) * (logStar (n : ℝ) : ℝ) := by
    norm_num
    nlinarith [hT_eps_log, hU_half]
  have hh_real : (hChain n : ℝ) ≤ (T + Urank n / 2 + 1 : ℕ) := by
    exact_mod_cast hh_nat
  exact hh_real.trans (by simpa using hmain)

/-- **Theorem 4.1 (upper bound for `h`).**

For all but `o(x)` integers `n ≤ x`, `h(n) ≤ (1/2 + o(1)) log_* x`.

Encoded ε-style: for every `ε > 0`, the density of `n ≤ x` with
`hChain n > (1/2 + ε) logStar x` tends to `0`. -/
theorem upper_bound_h :
    ∀ ε : ℝ, 0 < ε →
      almostAll (fun n => (hChain n : ℝ) ≤ (1/2 + ε) * (logStar n : ℝ)) := by
  intro ε hε
  classical
  unfold almostAll
  rw [Metric.tendsto_atTop]
  intro η hη
  have hη2 : 0 < η / 2 := by positivity
  have hη3 : 0 < η / 3 := by positivity
  rcases bad_prime_pair_density_h (η / 3) hη3 with ⟨Y₀, _hY₀pos, hbad_bound⟩
  let Cf : ℝ := 1
  have hCf : 0 < Cf := by norm_num [Cf]
  let M : ℕ := (U_tower_h Cf hCf).choose
  let T : ℕ := max 100 ⌈max Y₀ (Um M + 1)⌉₊
  have hT100 : 100 ≤ T := by simp [T]
  have hT_ge_Y₀ : Y₀ ≤ (T : ℝ) := by
    have hceil : max Y₀ (Um M + 1) ≤ (⌈max Y₀ (Um M + 1)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hceil_T : (⌈max Y₀ (Um M + 1)⌉₊ : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast le_max_right 100 ⌈max Y₀ (Um M + 1)⌉₊
    exact (le_max_left _ _).trans (hceil.trans hceil_T)
  have hTU : Um M < (T : ℝ) := by
    have hceil : max Y₀ (Um M + 1) ≤ (⌈max Y₀ (Um M + 1)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hceil_T : (⌈max Y₀ (Um M + 1)⌉₊ : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast le_max_right 100 ⌈max Y₀ (Um M + 1)⌉₊
    have hplus : Um M + 1 ≤ (T : ℝ) :=
      (le_max_right _ _).trans (hceil.trans hceil_T)
    linarith
  have hTU' : Um ((U_tower_h Cf hCf).choose) < (T : ℝ) := by simpa [M] using hTU
  rcases eventually_good_upper_bound_h ε hε T Cf hCf hT100 hTU' with ⟨N, hN1, hgood⟩
  let X : ℝ := max 1 (2 * (N : ℝ) / η)
  refine ⟨X, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx1
  let E : Set ℕ :=
    {n : ℕ | n ≤ ⌊x⌋₊ ∧
      ¬ (hChain n : ℝ) ≤ (1 / 2 + ε) * (logStar (n : ℝ) : ℝ)}
  let S : Set ℕ := {n : ℕ | n < N}
  let B : Set ℕ :=
    {n : ℕ | 0 < n ∧ n ≤ ⌊x⌋₊ ∧
      ∃ p q : ℕ, IsHBadPrimePair p q ∧ (T : ℝ) ≤ p ∧ p ∣ n ∧ q ∣ n}
  have hsub : E ⊆ S ∪ B := by
    intro n hn
    by_cases hnN : n < N
    · exact Or.inl hnN
    · right
      have hNn : N ≤ n := le_of_not_gt hnN
      have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) (hN1.trans hNn)
      have hbad : ∃ p q : ℕ, IsHBadPrimePair p q ∧ (T : ℝ) ≤ p ∧ p ∣ n ∧ q ∣ n := by
        by_contra hno
        exact hn.2 (hgood n hNn hno)
      exact ⟨hnpos, hn.1, hbad⟩
  have hS_finite : S.Finite := by
    change (Set.Iio N : Set ℕ).Finite
    exact Set.finite_Iio N
  have hB_finite : B.Finite := by
    exact (Set.finite_Iic ⌊x⌋₊).subset (by
      intro n hn
      exact hn.2.1)
  have hS_card : Nat.card S = N := by
    change Nat.card (Set.Iio N : Set ℕ) = N
    simp
  have hcardE_nat : Nat.card E ≤ N + Nat.card B := by
    have hmono : Nat.card E ≤ Nat.card (↥(S ∪ B)) :=
      Nat.card_mono (hS_finite.union hB_finite) hsub
    have hunion : Nat.card (↥(S ∪ B)) ≤ Nat.card S + Nat.card B :=
      Set.card_union_le S B
    exact hmono.trans (by simpa [hS_card] using hunion)
  have hB_bound : (Nat.card B : ℝ) ≤ (η / 3) * x := by
    simpa [B, ge_iff_le] using hbad_bound x hx1 (T : ℝ) hT_ge_Y₀
  have hcardE_real : (Nat.card E : ℝ) ≤ (N : ℝ) + (Nat.card B : ℝ) := by
    exact_mod_cast hcardE_nat
  have hratio_E :
      (Nat.card E : ℝ) / x ≤ (N : ℝ) / x + (Nat.card B : ℝ) / x := by
    calc
      (Nat.card E : ℝ) / x ≤ ((N : ℝ) + (Nat.card B : ℝ)) / x :=
        div_le_div_of_nonneg_right hcardE_real hxpos.le
      _ = (N : ℝ) / x + (Nat.card B : ℝ) / x := by ring
  have hB_ratio : (Nat.card B : ℝ) / x ≤ η / 3 := by
    have htmp := div_le_div_of_nonneg_right hB_bound hxpos.le
    have hsimp : ((η / 3) * x) / x = η / 3 := by field_simp [hxpos.ne']
    exact htmp.trans_eq hsimp
  have hXbig : 2 * (N : ℝ) / η ≤ x := (le_max_right _ _).trans hx
  have hsmall_ratio : (N : ℝ) / x ≤ η / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hXbig (show 0 ≤ η / 2 by positivity)
    have hNx : (N : ℝ) ≤ η / 2 * x := by
      field_simp [hη.ne'] at hmul
      nlinarith
    exact (div_le_iff₀ hxpos).2 (by simpa [mul_comm] using hNx)
  have hratio_lt : (Nat.card E : ℝ) / x < η := by
    calc
      (Nat.card E : ℝ) / x ≤ (N : ℝ) / x + (Nat.card B : ℝ) / x := hratio_E
      _ ≤ η / 2 + η / 3 := add_le_add hsmall_ratio hB_ratio
      _ < η := by nlinarith
  have hratio_nonneg : 0 ≤ (Nat.card E : ℝ) / x := by positivity
  change dist ((Nat.card E : ℝ) / x) 0 < η
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hratio_nonneg]
  exact hratio_lt

end Erdos696
