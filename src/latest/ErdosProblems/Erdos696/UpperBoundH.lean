/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import ErdosProblems.Erdos696.Tower

namespace Erdos696

open scoped BigOperators Topology
open Real MeasureTheory

-- === Inlined from Erdos696/UpperBoundH.lean ===
/-
# Upper bound for `H(n)`

Mirrors §3 of `erdos_696_paper.tex`.

**Theorem.** For all but `o(x)` integers `n ≤ x`,
`H(n) ≤ (1 + o(1)) log_* x`.

**Proof structure (paper §3).**
1. *Bad-pair density* (Lemma 3.2): the set of `n ≤ x` admitting some
   `H`-bad pair `(d, e)` with `d ≥ Y` (`Y → ∞`) has size `O(x · Y^{-1/2})`.
2. *`U`-tower lemma* (Lemma 3.3): `G(U_m) ≤ U_{m-1}` for `m ≥ 5`,
   where `G(t) = (log t)^2`.
3. *Tower descent* (Lemma 3.4): if `(d_i, d_{i+1})` is good with `d_i ≥ Y`,
   then `ρ(d_i) ≤ ρ(d_{i+1}) - 1`.
4. Assembly: each chain step descends one `U`-tower level on average,
   plus `Y = O(L^{1/2})` small terms, giving `H(n) ≤ L + O(L^{1/2})`.
-/



open Real

/-- **Bad pair, divisor version** (Definition 3.1 in the paper). -/
def IsHBadPair (d e : ℕ) : Prop :=
  d < e ∧ e % d = 1 ∧ (e : ℝ) < Real.exp (Real.sqrt d)

/-- The congruence condition in an `H`-bad pair makes the two divisors coprime. -/
lemma IsHBadPair.coprime {d e : ℕ} (h : IsHBadPair d e) : Nat.Coprime d e := by
  have hmod : e ≡ 1 [MOD d] := by
    simpa [h.2.1] using (Nat.mod_modEq e d).symm
  have hcop : Nat.Coprime e d := by
    exact Nat.coprime_of_mul_modEq_one 1 (by simpa using hmod)
  exact hcop.symm

/-- If an `H`-bad pair divides `n`, then the product of the two divisors divides `n`. -/
lemma IsHBadPair.mul_dvd {d e n : ℕ} (h : IsHBadPair d e) (hd : d ∣ n)
    (he : e ∣ n) : d * e ∣ n := by
  rcases he with ⟨k, rfl⟩
  have hdk : d ∣ k := by
    exact (h.coprime.dvd_mul_left).mp (by simpa [mul_comm, mul_left_comm, mul_assoc] using hd)
  rcases hdk with ⟨l, rfl⟩
  refine ⟨l, by ring⟩

/-- The smaller entry in an `H`-bad pair is at least `2`. -/
lemma IsHBadPair.two_le_left {d e : ℕ} (h : IsHBadPair d e) : 2 ≤ d := by
  by_contra hd
  have hdle : d ≤ 1 := by omega
  interval_cases d
  · have heq : e = 1 := by simpa using h.2.1
    have hlt : (1 : ℝ) < 1 := by
      simpa [heq] using h.2.2
    norm_num at hlt
  · have hzero : e % 1 = 0 := Nat.mod_one e
    have hbad : (0 : ℕ) = 1 := by
      rw [← hzero]
      exact h.2.1
    omega

/-- The congruence condition may be parameterized as `e = k * d + 1`. -/
lemma IsHBadPair.exists_mul_add_one {d e : ℕ} (h : IsHBadPair d e) :
    ∃ k : ℕ, 1 ≤ k ∧ e = k * d + 1 := by
  refine ⟨e / d, ?_, ?_⟩
  · have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) h.two_le_left
    exact Nat.succ_le_of_lt (Nat.div_pos h.1.le hdpos)
  · calc
      e = d * (e / d) + e % d := (Nat.div_add_mod e d).symm
      _ = e / d * d + e % d := by rw [mul_comm d]
      _ = e / d * d + 1 := by rw [h.2.1]

/-- A telescoping bound for the `d^{-3/2}` tail, written using square roots. -/
lemma inv_mul_sqrt_le_tel (d : ℕ) (hd : 1 ≤ d) :
    (1 : ℝ) / ((d : ℝ) * Real.sqrt d) ≤
      4 * (1 / Real.sqrt d - 1 / Real.sqrt (d + 1 : ℝ)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
  have hsd1 : 0 < Real.sqrt (d + 1 : ℝ) := by positivity
  field_simp [hdpos.ne', hsd.ne', hsd1.ne']
  set a : ℝ := Real.sqrt (d : ℝ)
  set b : ℝ := Real.sqrt (d + 1 : ℝ)
  have ha_nonneg : 0 ≤ a := by simp [a]
  have hb_nonneg : 0 ≤ b := by simp [b]
  have ha_le_b : a ≤ b := by
    simp [a, b]
    exact Real.sqrt_le_sqrt (by norm_num : (d : ℝ) ≤ d + 1)
  have ha_sq : a ^ 2 = (d : ℝ) := by simp [a, Real.sq_sqrt (le_of_lt hdpos)]
  have hb_sq : b ^ 2 = (d : ℝ) + 1 := by
    simp [b, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d + 1)]
  have hmul : (b - a) * (b + a) = 1 := by nlinarith
  have hb_sum : b * (b + a) ≤ 4 * (d : ℝ) := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  calc
    b = (b * (b + a)) * (b - a) := by nlinarith [hmul]
    _ ≤ (4 * (d : ℝ)) * (b - a) := by
      gcongr
    _ = (d : ℝ) * 4 * (b - a) := by ring

/-- A finite form of `∑_{d ≥ D} d^{-3/2} ≤ 4 / √D`. -/
lemma sum_Icc_inv_mul_sqrt_le (D N : ℕ) (hD : 1 ≤ D) :
    (∑ d ∈ Finset.Icc D N, (1 : ℝ) / ((d : ℝ) * Real.sqrt d)) ≤
      4 / Real.sqrt D := by
  by_cases hDN : D ≤ N
  · have hterm : ∀ d ∈ Finset.Icc D N,
        (1 : ℝ) / ((d : ℝ) * Real.sqrt d) ≤
          4 * (1 / Real.sqrt d - 1 / Real.sqrt (d + 1 : ℝ)) := by
      intro d hdmem
      exact inv_mul_sqrt_le_tel d (hD.trans (Finset.mem_Icc.mp hdmem).1)
    calc
      (∑ d ∈ Finset.Icc D N, (1 : ℝ) / ((d : ℝ) * Real.sqrt d))
          ≤ ∑ d ∈ Finset.Icc D N,
              4 * (1 / Real.sqrt d - 1 / Real.sqrt (d + 1 : ℝ)) := by
            exact Finset.sum_le_sum hterm
      _ = 4 * (∑ d ∈ Finset.Icc D N,
              (1 / Real.sqrt d - 1 / Real.sqrt (d + 1 : ℝ))) := by
            rw [Finset.mul_sum]
      _ = 4 * (1 / Real.sqrt D - 1 / Real.sqrt (N + 1 : ℝ)) := by
            congr 1
            have htel := Finset.sum_Ico_sub (f := fun i : ℕ => -(1 / Real.sqrt (i : ℝ)))
              (m := D) (n := N + 1) (hDN.trans (Nat.le_succ N))
            simpa [Finset.Ico_add_one_right_eq_Icc, sub_eq_add_neg, add_comm, add_left_comm,
              add_assoc] using htel
      _ ≤ 4 / Real.sqrt D := by
            have hnonneg : 0 ≤ 1 / Real.sqrt (N + 1 : ℝ) := by positivity
            have hle : 4 * (1 / Real.sqrt D - 1 / Real.sqrt (N + 1 : ℝ)) ≤
                4 * (1 / Real.sqrt D) := by nlinarith
            simp [div_eq_mul_inv] at hle ⊢
  · have hempty : Finset.Icc D N = ∅ := Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hDN)
    simp [hempty]
    positivity

/-- The possible larger entries in an `H`-bad pair with fixed smaller entry `d`,
truncated at `N`. -/
noncomputable def hBadEs (d N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (d + 1) N).filter (fun e => IsHBadPair d e)

/-- Finset version of `IsHBadPair.card_multiples_le`. -/
lemma IsHBadPair.finset_card_multiples_le {d e N : ℕ} (h : IsHBadPair d e) :
    ({n ∈ Finset.Ioc 0 N | d ∣ n ∧ e ∣ n}.card) ≤ N / (d * e) := by
  classical
  rw [← Nat.Ioc_filter_dvd_card_eq_div N (d * e)]
  exact Finset.card_le_card (by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, h.mul_dvd hn.2.1 hn.2.2⟩)

/-- A reciprocal-sum bound for the arithmetic progression `e ≡ 1 (mod d)` inside
the `H`-bad range.  The proof uses `e = k d + 1`, injects the possible `e` into
`k ≤ exp (√d)`, and bounds the resulting harmonic sum by `1 + log`. -/
lemma sum_hBadEs_inv_le (d N : ℕ) (hd : 1 ≤ d) :
    (∑ e ∈ hBadEs d N, (1 : ℝ) / (e : ℝ)) ≤ 2 / Real.sqrt d := by
  classical
  let s := hBadEs d N
  let M := ⌊Real.exp (Real.sqrt (d : ℝ))⌋₊
  have hs_def : s = (Finset.Icc (d + 1) N).filter (fun e => IsHBadPair d e) := rfl
  have hdpos_nat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdpos_nat
  have hM_nonneg : 0 ≤ Real.exp (Real.sqrt (d : ℝ)) := (Real.exp_pos _).le
  have hM_le_exp : (M : ℝ) ≤ Real.exp (Real.sqrt (d : ℝ)) := Nat.floor_le hM_nonneg
  have hM_pos : 0 < (M : ℝ) := by
    have h1 : (1 : ℕ) ≤ M := by
      apply Nat.le_floor
      norm_num
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1)
  have hlogM : Real.log (M : ℝ) ≤ Real.sqrt (d : ℝ) := by
    calc
      Real.log (M : ℝ) ≤ Real.log (Real.exp (Real.sqrt (d : ℝ))) :=
        Real.log_le_log hM_pos hM_le_exp
      _ = Real.sqrt (d : ℝ) := Real.log_exp _
  have hbad_of_mem : ∀ {e : ℕ}, e ∈ s → IsHBadPair d e := by
    intro e he
    rw [hs_def] at he
    exact (Finset.mem_filter.mp he).2
  have hinj : Set.InjOn (fun e : ℕ => e / d) (↑s : Set ℕ) := by
    intro e he e' he' hq
    change e ∈ s at he
    change e' ∈ s at he'
    change e / d = e' / d at hq
    have hbad : IsHBadPair d e := hbad_of_mem he
    have hbad' : IsHBadPair d e' := hbad_of_mem he'
    calc
      e = d * (e / d) + e % d := (Nat.div_add_mod e d).symm
      _ = d * (e' / d) + e' % d := by rw [hq, hbad.2.1, hbad'.2.1]
      _ = e' := Nat.div_add_mod e' d
  have hmaps : ∀ e ∈ s, e / d ∈ Finset.Icc 1 M := by
    intro e he
    have hbad : IsHBadPair d e := hbad_of_mem he
    rcases hbad.exists_mul_add_one with ⟨k, hk, heq⟩
    have hkdiv : e / d = k := by
      rw [heq]
      have hdgt : 1 < d := lt_of_lt_of_le (by norm_num : 1 < 2) hbad.two_le_left
      rw [Nat.add_comm, Nat.add_mul_div_right 1 k hdpos_nat, Nat.div_eq_of_lt hdgt,
        zero_add]
    rw [hkdiv]
    have hk_le_M : k ≤ M := by
      apply Nat.le_floor
      have hk_le_e : k ≤ e := by
        calc
          k = k * 1 := by rw [mul_one]
          _ ≤ k * d := Nat.mul_le_mul_left k hd
          _ ≤ k * d + 1 := Nat.le_succ _
          _ = e := heq.symm
      exact (show (k : ℝ) ≤ (e : ℝ) from by exact_mod_cast hk_le_e).trans hbad.2.2.le
    simpa [Finset.mem_Icc] using And.intro hk hk_le_M
  have hpoint : ∀ e ∈ s, (1 : ℝ) / (e : ℝ) ≤
      1 / (((e / d : ℕ) : ℝ) * (d : ℝ)) := by
    intro e he
    have hbad : IsHBadPair d e := hbad_of_mem he
    rcases hbad.exists_mul_add_one with ⟨k, _hk, heq⟩
    have hkdiv : e / d = k := by
      rw [heq]
      have hdgt : 1 < d := lt_of_lt_of_le (by norm_num : 1 < 2) hbad.two_le_left
      rw [Nat.add_comm, Nat.add_mul_div_right 1 k hdpos_nat, Nat.div_eq_of_lt hdgt,
        zero_add]
    have hprod_pos : 0 < (((e / d : ℕ) : ℝ) * (d : ℝ)) := by
      rw [hkdiv]
      positivity
    have hprod_le : (((e / d : ℕ) : ℝ) * (d : ℝ)) ≤ (e : ℝ) := by
      exact_mod_cast (Nat.div_mul_le_self e d)
    exact one_div_le_one_div_of_le hprod_pos hprod_le
  calc
    (∑ e ∈ hBadEs d N, (1 : ℝ) / (e : ℝ))
        = ∑ e ∈ s, (1 : ℝ) / (e : ℝ) := rfl
    _ ≤ ∑ e ∈ s, 1 / (((e / d : ℕ) : ℝ) * (d : ℝ)) := Finset.sum_le_sum hpoint
    _ = ∑ k ∈ Finset.image (fun e : ℕ => e / d) s, 1 / ((k : ℝ) * (d : ℝ)) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ k ∈ Finset.Icc 1 M, 1 / ((k : ℝ) * (d : ℝ)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by
        intro k hk
        rw [Finset.mem_image] at hk
        rcases hk with ⟨e, he, rfl⟩
        exact hmaps e he) (by
        intro k _hk _hk'
        positivity)
    _ = (1 / (d : ℝ)) * (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkpos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hkpos_nat
      field_simp [hkpos.ne', hdpos.ne']
    _ = (1 / (d : ℝ)) * (harmonic M : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp [one_div]
    _ ≤ (1 / (d : ℝ)) * (1 + Real.log (M : ℝ)) := by
      gcongr
      exact harmonic_le_one_add_log M
    _ ≤ (1 / (d : ℝ)) * (1 + Real.sqrt (d : ℝ)) := by
      gcongr
    _ ≤ 2 / Real.sqrt (d : ℝ) := by
      have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
      have hsd_ge_one : 1 ≤ Real.sqrt (d : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
      have hsdsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos.le
      field_simp [hdpos.ne', hsd.ne']
      nlinarith [hsdsq, hsd_ge_one]

/-- **Lemma 3.2 (bad-pair density for `H`).**

The number of integers `n ≤ x` such that some `H`-bad pair `(d, e)` with
`d ≥ Y` divides `n` is `O(x · Y^{-1/2})`.

Sketch: the inner sum `∑_{d < e < exp√d, e ≡ 1 mod d} 1/e ≤ d^{-1/2}`,
giving `∑_{d ≥ Y} x/d · d^{-1/2} ≪ x · Y^{-1/2}`.

Elementary but multi-step. -/
lemma bad_pair_density_H :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 1 ≤ x →
        ∀ Y : ℝ, 1 ≤ Y →
          (Nat.card
              {n : ℕ | 0 < n ∧ n ≤ ⌊x⌋₊ ∧
                 ∃ d e : ℕ, IsHBadPair d e ∧ (d : ℝ) ≥ Y ∧
                   d ∣ n ∧ e ∣ n} : ℝ) ≤ C * x / Real.sqrt Y := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro x hx Y hY
  let N : ℕ := ⌊x⌋₊
  let D : ℕ := ⌈Y⌉₊
  have hx_nonneg : 0 ≤ x := le_trans (by norm_num) hx
  have hN_le_x : (N : ℝ) ≤ x := by
    simpa [N] using (Nat.floor_le hx_nonneg)
  have hD_one : 1 ≤ D := by
    have hDreal : (1 : ℝ) ≤ (D : ℝ) := hY.trans (Nat.le_ceil Y)
    exact_mod_cast hDreal
  have hDreal_geY : Y ≤ (D : ℝ) := Nat.le_ceil Y
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD_one)
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  let S : Finset ℕ := {n ∈ Finset.Ioc 0 N |
    ∃ d e : ℕ, IsHBadPair d e ∧ (d : ℝ) ≥ Y ∧ d ∣ n ∧ e ∣ n}
  let U : Finset ℕ := (Finset.Icc D N).biUnion fun d =>
    (hBadEs d N).biUnion fun e => {n ∈ Finset.Ioc 0 N | d ∣ n ∧ e ∣ n}
  have hS_subset : S ⊆ U := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Ioc] at hn
    rcases hn with ⟨hnIoc, d, e, hbad, hdY, hdn, hen⟩
    have hnpos : 0 < n := hnIoc.1
    have hnle : n ≤ N := hnIoc.2
    have hd_le_n : d ≤ n := Nat.le_of_dvd hnpos hdn
    have he_le_n : e ≤ n := Nat.le_of_dvd hnpos hen
    have hD_le_d : D ≤ d := (Nat.ceil_le).2 hdY
    have hd_le_N : d ≤ N := hd_le_n.trans hnle
    have he_le_N : e ≤ N := he_le_n.trans hnle
    have he_mem : e ∈ hBadEs d N := by
      dsimp [hBadEs]
      simp [hbad, hbad.1, he_le_N]
    simp only [U, Finset.mem_biUnion]
    refine ⟨d, ?_, e, he_mem, ?_⟩
    · simpa [Finset.mem_Icc] using And.intro hD_le_d hd_le_N
    · simp [hnIoc, hdn, hen]
  have hcard_nat : S.card ≤
      ∑ d ∈ Finset.Icc D N, ∑ e ∈ hBadEs d N,
        ({n ∈ Finset.Ioc 0 N | d ∣ n ∧ e ∣ n}.card) := by
    calc
      S.card ≤ U.card := Finset.card_le_card hS_subset
      _ ≤ ∑ d ∈ Finset.Icc D N,
            ((hBadEs d N).biUnion fun e =>
              {n ∈ Finset.Ioc 0 N | d ∣ n ∧ e ∣ n}).card := by
          exact Finset.card_biUnion_le
      _ ≤ ∑ d ∈ Finset.Icc D N, ∑ e ∈ hBadEs d N,
            ({n ∈ Finset.Ioc 0 N | d ∣ n ∧ e ∣ n}.card) := by
          apply Finset.sum_le_sum
          intro d _hd
          exact Finset.card_biUnion_le
  have hcard_nat_div : S.card ≤
      ∑ d ∈ Finset.Icc D N, ∑ e ∈ hBadEs d N, N / (d * e) := by
    exact hcard_nat.trans (by
      apply Finset.sum_le_sum
      intro d _hd
      apply Finset.sum_le_sum
      intro e he
      have hbad : IsHBadPair d e := by
        dsimp [hBadEs] at he
        exact (Finset.mem_filter.mp he).2
      exact hbad.finset_card_multiples_le)
  have hcard_real : (S.card : ℝ) ≤
      ∑ d ∈ Finset.Icc D N, ∑ e ∈ hBadEs d N, ((N / (d * e) : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat_div
  have hdiv_to_real :
      (∑ d ∈ Finset.Icc D N, ∑ e ∈ hBadEs d N, ((N / (d * e) : ℕ) : ℝ)) ≤
        ∑ d ∈ Finset.Icc D N, ∑ e ∈ hBadEs d N,
          x / ((d : ℝ) * (e : ℝ)) := by
    apply Finset.sum_le_sum
    intro d _hdmem
    apply Finset.sum_le_sum
    intro e he
    have hbad : IsHBadPair d e := by
      dsimp [hBadEs] at he
      exact (Finset.mem_filter.mp he).2
    have hdpos_nat : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hbad.two_le_left
    have hepos_nat : 0 < e := lt_trans hdpos_nat hbad.1
    have hdenpos : 0 < ((d * e : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hdpos_nat hepos_nat
    calc
      ((N / (d * e) : ℕ) : ℝ) ≤ (N : ℝ) / ((d * e : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ x / ((d * e : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right hN_le_x hdenpos.le
      _ = x / ((d : ℝ) * (e : ℝ)) := by norm_num
  have hinner :
      (∑ d ∈ Finset.Icc D N, ∑ e ∈ hBadEs d N, x / ((d : ℝ) * (e : ℝ))) ≤
        ∑ d ∈ Finset.Icc D N, (x / (d : ℝ)) * (2 / Real.sqrt d) := by
    calc
      (∑ d ∈ Finset.Icc D N, ∑ e ∈ hBadEs d N, x / ((d : ℝ) * (e : ℝ)))
          = ∑ d ∈ Finset.Icc D N,
              (x / (d : ℝ)) * (∑ e ∈ hBadEs d N, (1 : ℝ) / (e : ℝ)) := by
            apply Finset.sum_congr rfl
            intro d hdmem
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _he
            have hdpos_nat : 0 < d :=
              lt_of_lt_of_le Nat.zero_lt_one (hD_one.trans (Finset.mem_Icc.mp hdmem).1)
            have hdpos : (0 : ℝ) < d := by exact_mod_cast hdpos_nat
            field_simp [hdpos.ne']
      _ ≤ ∑ d ∈ Finset.Icc D N, (x / (d : ℝ)) * (2 / Real.sqrt d) := by
            apply Finset.sum_le_sum
            intro d hdmem
            have hd1 : 1 ≤ d := hD_one.trans (Finset.mem_Icc.mp hdmem).1
            have hcoef_nonneg : 0 ≤ x / (d : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_left (sum_hBadEs_inv_le d N hd1) hcoef_nonneg
  have htail :
      (∑ d ∈ Finset.Icc D N, (x / (d : ℝ)) * (2 / Real.sqrt d)) ≤
        8 * x / Real.sqrt Y := by
    calc
      (∑ d ∈ Finset.Icc D N, (x / (d : ℝ)) * (2 / Real.sqrt d))
          = 2 * x *
              (∑ d ∈ Finset.Icc D N, (1 : ℝ) / ((d : ℝ) * Real.sqrt d)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hdmem
            have hd1 : 1 ≤ d := hD_one.trans (Finset.mem_Icc.mp hdmem).1
            have hdpos : (0 : ℝ) < d := by
              exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
            have hsqrtd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
            field_simp [hdpos.ne', hsqrtd.ne']
      _ ≤ 2 * x * (4 / Real.sqrt D) := by
            have hcoef_nonneg : 0 ≤ 2 * x := by nlinarith [hx]
            exact mul_le_mul_of_nonneg_left (sum_Icc_inv_mul_sqrt_le D N hD_one)
              hcoef_nonneg
      _ = 8 * x / Real.sqrt D := by ring
      _ ≤ 8 * x / Real.sqrt Y := by
            have hcoef_nonneg : 0 ≤ 8 * x := by nlinarith [hx]
            have hsqrtY : 0 < Real.sqrt Y := Real.sqrt_pos.2 hYpos
            have hsqrtD : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 hDpos
            have hsqrt_le : Real.sqrt Y ≤ Real.sqrt (D : ℝ) :=
              Real.sqrt_le_sqrt hDreal_geY
            have hrec : 1 / Real.sqrt (D : ℝ) ≤ 1 / Real.sqrt Y :=
              one_div_le_one_div_of_le hsqrtY hsqrt_le
            have := mul_le_mul_of_nonneg_left hrec hcoef_nonneg
            simpa [div_eq_mul_inv, mul_assoc] using this
  have hS_bound : (S.card : ℝ) ≤ 8 * x / Real.sqrt Y := by
    exact hcard_real.trans (hdiv_to_real.trans (hinner.trans htail))
  change (Nat.card {n : ℕ | 0 < n ∧ n ≤ N ∧
    ∃ d e : ℕ, IsHBadPair d e ∧ (d : ℝ) ≥ Y ∧ d ∣ n ∧ e ∣ n} : ℝ) ≤
      8 * x / Real.sqrt Y
  rw [Nat.subtype_card S]
  · exact hS_bound
  · intro n
    simp [S, and_assoc]

/-- Every natural number lies below some `U_m`. -/
lemma Urank_exists (d : ℕ) : ∃ m : ℕ, (d : ℝ) ≤ Um m := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (tower_tendsto_atTop.eventually_ge_atTop (d : ℝ))
  refine ⟨N, ?_⟩
  have htd : (d : ℝ) ≤ tower N := hN N le_rfl
  unfold Um
  have ht1 : (1 : ℝ) ≤ tower N := one_le_tower N
  have ht0 : (0 : ℝ) ≤ tower N := le_trans (by norm_num) ht1
  nlinarith [htd, ht1, sq_nonneg (tower N), mul_nonneg ht0 (sq_nonneg (tower N))]

/-- The `U`-rank of `d`: the smallest `m ≥ 0` with `d ≤ U_m`. -/
noncomputable def Urank (d : ℕ) : ℕ := by
  classical
  letI : DecidablePred (fun m : ℕ => (d : ℝ) ≤ Um m) := Classical.decPred _
  exact Nat.find (Urank_exists d)

/-- The defining upper bound at the minimal `U`-rank. -/
lemma Urank_spec (d : ℕ) : (d : ℝ) ≤ Um (Urank d) := by
  classical
  unfold Urank
  exact Nat.find_spec (Urank_exists d)

/-- If `d ≤ U_m`, then the `U`-rank of `d` is at most `m`. -/
lemma Urank_le_of_le_Um {d m : ℕ} (h : (d : ℝ) ≤ Um m) : Urank d ≤ m := by
  classical
  unfold Urank
  exact Nat.find_min' (Urank_exists d) h

/-- The auxiliary tower scale `U_m` is monotone in `m`. -/
lemma Um_mono : Monotone Um := by
  intro a b hab
  unfold Um
  have ht : tower a ≤ tower b := (strictMono_nat_of_lt_succ tower_lt_succ).monotone hab
  exact pow_le_pow_left₀ (le_of_lt (tower_pos a)) ht 3

/-- The `U`-rank is monotone in its argument. -/
lemma Urank_mono {a b : ℕ} (h : a ≤ b) : Urank a ≤ Urank b := by
  apply Urank_le_of_le_Um
  have hab : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
  exact hab.trans (Urank_spec b)

/-- The original tower is bounded by the auxiliary scale `U_m = T_m^3`. -/
lemma tower_le_Um (m : ℕ) : tower m ≤ Um m := by
  unfold Um
  have ht : 1 ≤ tower m := one_le_tower m
  have ht0 : 0 ≤ tower m := le_trans (by norm_num) ht
  nlinarith [sq_nonneg (tower m), mul_nonneg ht0 (sq_nonneg (tower m))]

/-- Anything above `U_5` has `U`-rank at least `6`. -/
lemma six_le_Urank_of_Um_five_lt {d : ℕ} (h : Um 5 < (d : ℝ)) : 6 ≤ Urank d := by
  by_contra h6
  have hr : Urank d ≤ 5 := by omega
  have hle : (d : ℝ) ≤ Um 5 := (Urank_spec d).trans (Um_mono hr)
  exact (not_lt_of_ge hle) h

/-- If an iterated logarithm lands below a tower level, then the original
number lies below the correspondingly higher tower level. -/
lemma le_tower_add_of_iteratedLog_le (k m : ℕ) {x : ℝ}
    (h : iteratedLog k x ≤ tower m) : x ≤ tower (m + k) := by
  induction k generalizing m with
  | zero =>
      simpa [iteratedLog] using h
  | succ k ih =>
      change Real.log (iteratedLog k x) ≤ tower m at h
      by_cases hy : iteratedLog k x ≤ 0
      · have h0 : iteratedLog k x ≤ tower 0 := le_trans hy (tower_pos 0).le
        have hx0 : x ≤ tower (0 + k) := ih 0 h0
        have hmono : Monotone tower := (strictMono_nat_of_lt_succ tower_lt_succ).monotone
        exact hx0.trans (hmono (by omega))
      · have hypos : 0 < iteratedLog k x := lt_of_not_ge hy
        have hyle : iteratedLog k x ≤ Real.exp (tower m) :=
          (Real.log_le_iff_le_exp hypos).mp h
        have hx : x ≤ tower ((m + 1) + k) := by
          apply ih (m + 1)
          simpa [tower] using hyle
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx

/-- Moving one logarithm from the argument into the iteration count. -/
lemma iteratedLog_log (k : ℕ) (x : ℝ) :
    iteratedLog k (Real.log x) = iteratedLog (k + 1) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [iteratedLog, ih]

/-- Any number below a tower eventually has an iterated logarithm at most `e`. -/
lemma exists_iteratedLog_le_exp_one_of_le_tower (K : ℕ) {x : ℝ}
    (hx : x ≤ tower K) : ∃ k : ℕ, iteratedLog k x ≤ Real.exp 1 := by
  induction K generalizing x with
  | zero =>
      exact ⟨0, by simpa only [iteratedLog, tower] using hx⟩
  | succ K ih =>
      by_cases hx0 : x ≤ Real.exp 1
      · exact ⟨0, by simpa [iteratedLog] using hx0⟩
      · have hxpos : 0 < x := lt_trans (Real.exp_pos 1) (lt_of_not_ge hx0)
        have hlog_le : Real.log x ≤ tower K := by
          have hx_le_exp : x ≤ Real.exp (tower K) := by simpa [tower] using hx
          exact (Real.log_le_iff_le_exp hxpos).2 hx_le_exp
        rcases ih hlog_le with ⟨k, hk⟩
        exact ⟨k + 1, by simpa [iteratedLog_log] using hk⟩

/-- Every real number has some iterated logarithm at most `e`. -/
lemma exists_iteratedLog_le_exp_one (x : ℝ) :
    ∃ k : ℕ, iteratedLog k x ≤ Real.exp 1 := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (tower_tendsto_atTop.eventually_ge_atTop x)
  exact exists_iteratedLog_le_exp_one_of_le_tower N (hN N le_rfl)

/-- The defining property of `logStar`. -/
lemma logStar_spec (x : ℝ) : iteratedLog (logStar x) x ≤ Real.exp 1 := by
  classical
  unfold logStar
  let h : ∃ k : ℕ, iteratedLog k x ≤ Real.exp 1 := exists_iteratedLog_le_exp_one x
  rw [dif_pos h]
  exact Nat.find_spec h

/-- A number is bounded by the tower at its `logStar` level. -/
lemma self_le_tower_logStar (x : ℝ) : x ≤ tower (logStar x) := by
  simpa using le_tower_add_of_iteratedLog_le (logStar x) 0
    (by simpa only [tower] using logStar_spec x)

/-- The `U`-rank of a natural number is at most its `logStar`. -/
lemma Urank_le_logStar (n : ℕ) : Urank n ≤ logStar (n : ℝ) := by
  apply Urank_le_of_le_Um
  exact (self_le_tower_logStar (n : ℝ)).trans (tower_le_Um _)

/-- `logStar n` is eventually at least any prescribed natural level. -/
lemma eventually_logStar_ge (L₀ : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → L₀ ≤ logStar (n : ℝ) := by
  classical
  by_cases hL₀ : L₀ = 0
  · subst L₀
    exact ⟨0, by intro n hn; omega⟩
  · let N : ℕ := ⌊tower L₀⌋₊ + 1
    refine ⟨N, ?_⟩
    intro n hn
    by_contra hnot
    have hlt : logStar (n : ℝ) < L₀ := Nat.lt_of_not_ge hnot
    have hn_le : (n : ℝ) ≤ tower (logStar (n : ℝ)) := self_le_tower_logStar (n : ℝ)
    have htower_lt : tower (logStar (n : ℝ)) < tower L₀ :=
      strictMono_nat_of_lt_succ tower_lt_succ hlt
    have htowerL₀_lt_N : tower L₀ < (N : ℝ) := by
      have hnonneg : 0 ≤ tower L₀ := (tower_pos L₀).le
      exact (Nat.floor_lt hnonneg).mp (Nat.lt_succ_self _)
    have hn_real_ge : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith

/-- A property that holds above a fixed natural threshold holds for almost all integers. -/
lemma almostAll_of_forall_ge {P : ℕ → Prop} (N : ℕ) (hN : ∀ n : ℕ, N ≤ n → P n) :
    almostAll P := by
  classical
  unfold almostAll
  have hbound : ∀ x : ℝ,
      (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} : ℝ) ≤ (N : ℝ) := by
    intro x
    have hsub : {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} ⊆ Set.Iio N := by
      intro n hn
      by_contra hnN
      exact hn.2 (hN n (le_of_not_gt hnN))
    have hcard : Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} ≤
        Nat.card (Set.Iio N : Set ℕ) := by
      exact Nat.card_mono (Set.finite_Iio N) hsub
    have hcardIio : Nat.card (Set.Iio N : Set ℕ) = N := by
      simp
    exact_mod_cast (by simpa [hcardIio] using hcard)
  have hnonneg : ∀ᶠ x : ℝ in Filter.atTop,
      0 ≤ (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} : ℝ) / x := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  have hupper : Filter.Tendsto (fun x : ℝ => (N : ℝ) / x) Filter.atTop (nhds 0) := by
    exact Filter.Tendsto.const_div_atTop Filter.tendsto_id (N : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hnonneg ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  exact div_le_div_of_nonneg_right (hbound x) hx.le

/-- **Lemma 3.4 (tower descent for `H`).**

If `d_i ≥ Y` (for some `Y` chosen later) and the pair `(d_i, d_{i+1})` is
*not* `H`-bad, then `Urank d_i ≤ Urank d_{i+1} - 1`, provided
`Urank d_{i+1} ≥ 6`.

Combines `U_tower_H` from `Tower.lean` with the definition of `Urank`
and the inequality `d_i ≤ G(d_{i+1})` from the not-bad condition. -/
lemma tower_descent_H (di dnext : ℕ) (hdi : 100 ≤ di)
    (h_no_bad : ¬ IsHBadPair di dnext)
    (h_chain : di < dnext ∧ dnext % di = 1)
    (h_rank : 6 ≤ Urank dnext) :
    Urank di ≤ Urank dnext - 1 := by
  let m := Urank dnext
  have hm6 : 6 ≤ m := by simpa [m] using h_rank
  have hm5 : 5 ≤ m := le_trans (by norm_num) hm6
  have hnotlt : ¬ (dnext : ℝ) < Real.exp (Real.sqrt di) := by
    intro hlt
    exact h_no_bad ⟨h_chain.1, h_chain.2, hlt⟩
  have hexp_le_dnext : Real.exp (Real.sqrt di) ≤ (dnext : ℝ) := le_of_not_gt hnotlt
  have hdnext_le_Um : (dnext : ℝ) ≤ Um m := by
    simpa [m] using Urank_spec dnext
  have hexp_le_Um : Real.exp (Real.sqrt di) ≤ Um m := le_trans hexp_le_dnext hdnext_le_Um
  have hsqrt_le_log : Real.sqrt (di : ℝ) ≤ Real.log (Um m) := by
    calc
      Real.sqrt (di : ℝ) = Real.log (Real.exp (Real.sqrt (di : ℝ))) := by
        rw [Real.log_exp]
      _ ≤ Real.log (Um m) := Real.log_le_log (Real.exp_pos _) hexp_le_Um
  have hdi_nonneg : 0 ≤ (di : ℝ) := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (di : ℝ) := Real.sqrt_nonneg _
  have hlog_nonneg : 0 ≤ Real.log (Um m) := le_trans hsqrt_nonneg hsqrt_le_log
  have hdi_le_G : (di : ℝ) ≤ G (Um m) := by
    unfold G
    rw [← Real.sq_sqrt hdi_nonneg]
    nlinarith [hsqrt_le_log, hsqrt_nonneg, hlog_nonneg]
  have hdi_le_Uprev : (di : ℝ) ≤ Um (m - 1) := le_trans hdi_le_G (U_tower_H m hm5)
  have hres : Urank di ≤ m - 1 := Urank_le_of_le_Um hdi_le_Uprev
  simpa [m] using hres

/-- The tail of a nontrivial divisor chain is again a divisor chain. -/
private lemma IsDivisorChain.tail_cons {n d e : ℕ} {rest : List ℕ}
    (hds : IsDivisorChain n (d :: e :: rest)) : IsDivisorChain n (e :: rest) := by
  rcases hds with ⟨hdiv, hpair, hmod⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact hdiv a (by simp [ha])
  · exact hpair.tail
  · intro i hi
    let j : Fin (d :: e :: rest).length := ⟨i.val + 1, by simp at hi ⊢; omega⟩
    have hj : j.val + 1 < (d :: e :: rest).length := by
      dsimp [j]
      simp at hi ⊢
      omega
    have := hmod j hj
    simpa [j] using this

/-- The first two entries of a nontrivial divisor chain satisfy the chain relation.
The mod condition is the paper-faithful `e ≡ 1 (mod d)`, which is vacuous for `d = 1`. -/
private lemma IsDivisorChain.head_rel {n d e : ℕ} {rest : List ℕ}
    (hds : IsDivisorChain n (d :: e :: rest)) : d < e ∧ Nat.ModEq d e 1 := by
  rcases hds with ⟨_hdiv, hpair, hmod⟩
  constructor
  · exact hpair.rel_head_tail (by simp)
  · have := hmod ⟨0, by simp⟩ (by simp)
    simpa using this

/-- A divisor appearing in a positive divisor chain has `U`-rank at most that of `n`. -/
private lemma Urank_le_of_mem_divisorChain {n d : ℕ} {ds : List ℕ} (hn : 0 < n)
    (hds : IsDivisorChain n ds) (hdmem : d ∈ ds) : Urank d ≤ Urank n := by
  exact Urank_mono (Nat.le_of_dvd hn ((hds.1 d hdmem).2))

/-- Recursive budget for a divisor chain with no bad large adjacent pair. -/
private lemma divisor_chain_length_aux {n T : ℕ}
    (hT100 : 100 ≤ T) (hTU : Um 5 < (T : ℝ)) (hn : 0 < n)
    (hnoT : ∀ d e : ℕ, T ≤ d → d ∣ n → e ∣ n → ¬ IsHBadPair d e) :
    ∀ (d : ℕ) (rest : List ℕ), IsDivisorChain n (d :: rest) →
      (d < T → (d :: rest).length ≤ T - d + Urank n + 1) ∧
      (T ≤ d → (d :: rest).length ≤ Urank n - Urank d + 1) := by
  intro d rest
  induction rest generalizing d with
  | nil =>
      intro hds
      constructor
      · intro _hdT
        change 1 ≤ T - d + Urank n + 1
        omega
      · intro _hTd
        have hrd : Urank d ≤ Urank n := Urank_le_of_mem_divisorChain hn hds (by simp)
        change 1 ≤ Urank n - Urank d + 1
        omega
  | cons e rest ih =>
      intro hds
      have htail : IsDivisorChain n (e :: rest) := hds.tail_cons
      have hrel_modeq : d < e ∧ Nat.ModEq d e 1 := hds.head_rel
      have hdvd : d ∣ n := (hds.1 d (by simp)).2
      have hedvd : e ∣ n := (hds.1 e (by simp)).2
      have hre : Urank e ≤ Urank n := Urank_le_of_mem_divisorChain hn htail (by simp)
      constructor
      · intro hdT
        by_cases heT : e < T
        · have htail_bound := (ih e htail).1 heT
          have hbudget : T - e + Urank n + 1 + 1 ≤ T - d + Urank n + 1 := by
            omega
          exact (Nat.succ_le_succ htail_bound).trans hbudget
        · have hTe : T ≤ e := le_of_not_gt heT
          have htail_bound := (ih e htail).2 hTe
          have hbudget : Urank n - Urank e + 1 + 1 ≤ T - d + Urank n + 1 := by
            omega
          exact (Nat.succ_le_succ htail_bound).trans hbudget
      · intro hTd
        -- In this branch T ≤ d and 100 ≤ T, so d ≥ 100 ≥ 2.
        -- Hence Nat.ModEq d e 1 is equivalent to e % d = 1 (since 1 % d = 1 for d ≥ 2).
        have hd_ge_2 : 2 ≤ d := by linarith [hT100, hTd]
        have hmod_old : e % d = 1 := by
          have h := hrel_modeq.2
          show e % d = 1
          have : e % d = 1 % d := h
          rwa [Nat.mod_eq_of_lt (by linarith : 1 < d)] at this
        have hrel : d < e ∧ e % d = 1 := ⟨hrel_modeq.1, hmod_old⟩
        have hno_bad : ¬ IsHBadPair d e := hnoT d e hTd hdvd hedvd
        have hT_e_real : (T : ℝ) ≤ (e : ℝ) := by exact_mod_cast (hTd.trans hrel.1.le)
        have hrank_e : 6 ≤ Urank e := six_le_Urank_of_Um_five_lt (hTU.trans_le hT_e_real)
        have hdesc : Urank d ≤ Urank e - 1 :=
          tower_descent_H d e (hT100.trans hTd) hno_bad hrel hrank_e
        have hrd_lt_re : Urank d < Urank e := by omega
        have htail_bound := (ih e htail).2 (hTd.trans hrel.1.le)
        have hbudget : Urank n - Urank e + 1 + 1 ≤ Urank n - Urank d + 1 := by
          omega
        exact (Nat.succ_le_succ htail_bound).trans hbudget

/-- A divisor chain is bounded by the rank of `n`, plus the number of small entries. -/
private lemma divisor_chain_length_le_rank_add {n T : ℕ}
    (hT100 : 100 ≤ T) (hTU : Um 5 < (T : ℝ)) (hn : 0 < n)
    (hnoT : ∀ d e : ℕ, T ≤ d → d ∣ n → e ∣ n → ¬ IsHBadPair d e)
    {ds : List ℕ} (hds : IsDivisorChain n ds) : ds.length ≤ T + Urank n + 1 := by
  cases ds with
  | nil => simp
  | cons d rest =>
      by_cases hdT : d < T
      · have h := (divisor_chain_length_aux hT100 hTU hn hnoT d rest hds).1 hdT
        calc
          (d :: rest).length ≤ T - d + Urank n + 1 := h
          _ ≤ T + Urank n + 1 := by omega
      · have hTd : T ≤ d := le_of_not_gt hdT
        have h := (divisor_chain_length_aux hT100 hTU hn hnoT d rest hds).2 hTd
        calc
          (d :: rest).length ≤ Urank n - Urank d + 1 := h
          _ ≤ T + Urank n + 1 := by omega

/-- If `n` has no bad pair with smaller entry at least `T`, then `HChain n` is
bounded by `Urank n + T + 1`. -/
private lemma HChain_le_rank_add_of_no_bad {n T : ℕ}
    (hT100 : 100 ≤ T) (hTU : Um 5 < (T : ℝ)) (hn : 0 < n)
    (hnoT : ∀ d e : ℕ, T ≤ d → d ∣ n → e ∣ n → ¬ IsHBadPair d e) :
    HChain n ≤ T + Urank n + 1 := by
  classical
  by_cases hn1 : n = 1
  · subst hn1; simp [HChain]
  have hne : ({u | ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = u} : Set ℕ).Nonempty :=
    ⟨0, ⟨[], by simp [IsDivisorChain]⟩⟩
  show HChain n ≤ T + Urank n + 1
  rw [HChain, if_neg hn1]
  exact csSup_le hne (by
    intro u hu
    rcases hu with ⟨ds, hds, rfl⟩
    exact divisor_chain_length_le_rank_add hT100 hTU hn hnoT hds)

/-- Deterministic part of the upper-bound proof: away from large bad pairs,
all sufficiently large `n` satisfy the desired `H` bound. -/
private lemma eventually_good_upper_bound (ε : ℝ) (hε : 0 < ε) (T : ℕ)
    (hT100 : 100 ≤ T) (hTU : Um 5 < (T : ℝ)) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (¬ ∃ d e : ℕ, IsHBadPair d e ∧ (T : ℝ) ≤ d ∧ d ∣ n ∧ e ∣ n) →
          (HChain n : ℝ) ≤ (1 + ε) * (logStar (n : ℝ) : ℝ) := by
  let L₀ : ℕ := max 1 ⌈((T + 1 : ℝ) / ε)⌉₊
  have hL₀_pos : 1 ≤ L₀ := by simp [L₀]
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
  have hnoT : ∀ d e : ℕ, T ≤ d → d ∣ n → e ∣ n → ¬ IsHBadPair d e := by
    intro d e hTd hdvd hedvd hbad
    exact hno ⟨d, e, hbad, by exact_mod_cast hTd, hdvd, hedvd⟩
  have hH_nat : HChain n ≤ T + Urank n + 1 :=
    HChain_le_rank_add_of_no_bad hT100 hTU hn_pos hnoT
  have hU : Urank n ≤ logStar (n : ℝ) := Urank_le_logStar n
  have hT_eps_log : (T + 1 : ℝ) ≤ ε * (logStar (n : ℝ) : ℝ) := by
    exact hT_le_eps_L₀.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hlog_ge) hε.le)
  have hmain : (T + Urank n + 1 : ℝ) ≤
      (1 + ε) * (logStar (n : ℝ) : ℝ) := by
    have hUreal : (Urank n : ℝ) ≤ (logStar (n : ℝ) : ℝ) := by exact_mod_cast hU
    nlinarith
  have hH_real : (HChain n : ℝ) ≤ (T + Urank n + 1 : ℕ) := by
    exact_mod_cast hH_nat
  exact hH_real.trans (by simpa using hmain)

/-- **Theorem 3.1 (upper bound for `H`).**

For all but `o(x)` integers `n ≤ x`, `H(n) ≤ (1 + o(1)) log_* x`.

This is the formalized statement.  The asymptotic `(1 + o(1))` is encoded
as: for every `ε > 0`, the density of `n ≤ x` with
`HChain n > (1 + ε) logStar x` tends to `0` as `x → ∞`.

Proof sketch (§3.3 of paper): combine `bad_pair_density_H` with
`tower_descent_H` and the fact `ρ(d_u) ≤ L`.
-/
theorem upper_bound_H :
    ∀ ε : ℝ, 0 < ε →
      almostAll (fun n => (HChain n : ℝ) ≤ (1 + ε) * (logStar n : ℝ)) := by
  intro ε hε
  classical
  rcases bad_pair_density_H with ⟨C, hCpos, hbad_bound⟩
  unfold almostAll
  rw [Metric.tendsto_atTop]
  intro η hη
  have hη2 : 0 < η / 2 := by positivity
  have hcoef_tendsto :
      Filter.Tendsto (fun Y : ℝ => C / Real.sqrt Y) Filter.atTop (nhds 0) := by
    have hdiv : Filter.Tendsto (fun y : ℝ => C / y) Filter.atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop Filter.tendsto_id C
    exact hdiv.comp Real.tendsto_sqrt_atTop
  rw [Metric.tendsto_atTop] at hcoef_tendsto
  rcases hcoef_tendsto (η / 2) hη2 with ⟨Y₀, hY₀⟩
  let T : ℕ := max 100 ⌈max Y₀ (Um 5 + 1)⌉₊
  have hT100 : 100 ≤ T := by simp [T]
  have hT1_nat : 1 ≤ T := le_trans (by norm_num) hT100
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT1_nat
  have hT_ge_Y₀ : Y₀ ≤ (T : ℝ) := by
    have hceil : max Y₀ (Um 5 + 1) ≤ (⌈max Y₀ (Um 5 + 1)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hceil_T : (⌈max Y₀ (Um 5 + 1)⌉₊ : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast le_max_right 100 ⌈max Y₀ (Um 5 + 1)⌉₊
    exact (le_max_left _ _).trans (hceil.trans hceil_T)
  have hTU : Um 5 < (T : ℝ) := by
    have hceil : max Y₀ (Um 5 + 1) ≤ (⌈max Y₀ (Um 5 + 1)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hceil_T : (⌈max Y₀ (Um 5 + 1)⌉₊ : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast le_max_right 100 ⌈max Y₀ (Um 5 + 1)⌉₊
    have hplus : Um 5 + 1 ≤ (T : ℝ) :=
      (le_max_right _ _).trans (hceil.trans hceil_T)
    linarith
  have hsqrtT_pos : 0 < Real.sqrt (T : ℝ) := by
    exact Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hT1)
  have hcoef_small : C / Real.sqrt (T : ℝ) < η / 2 := by
    have hdist := hY₀ (T : ℝ) hT_ge_Y₀
    simpa [Real.dist_eq, abs_of_pos hCpos, abs_of_pos hsqrtT_pos] using hdist
  rcases eventually_good_upper_bound ε hε T hT100 hTU with ⟨N, hN1, hgood⟩
  let X : ℝ := max 1 (2 * (N : ℝ) / η)
  refine ⟨X, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx1
  let E : Set ℕ :=
    {n : ℕ | n ≤ ⌊x⌋₊ ∧
      ¬ (HChain n : ℝ) ≤ (1 + ε) * (logStar (n : ℝ) : ℝ)}
  let S : Set ℕ := {n : ℕ | n < N}
  let B : Set ℕ :=
    {n : ℕ | 0 < n ∧ n ≤ ⌊x⌋₊ ∧
      ∃ d e : ℕ, IsHBadPair d e ∧ (T : ℝ) ≤ d ∧ d ∣ n ∧ e ∣ n}
  have hsub : E ⊆ S ∪ B := by
    intro n hn
    by_cases hnN : n < N
    · exact Or.inl hnN
    · right
      have hNn : N ≤ n := le_of_not_gt hnN
      have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) (hN1.trans hNn)
      have hbad : ∃ d e : ℕ, IsHBadPair d e ∧ (T : ℝ) ≤ d ∧ d ∣ n ∧ e ∣ n := by
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
  have hB_bound : (Nat.card B : ℝ) ≤ C * x / Real.sqrt (T : ℝ) := by
    simpa [B, ge_iff_le] using hbad_bound x hx1 (T : ℝ) hT1
  have hcardE_real : (Nat.card E : ℝ) ≤ (N : ℝ) + (Nat.card B : ℝ) := by
    exact_mod_cast hcardE_nat
  have hratio_E :
      (Nat.card E : ℝ) / x ≤ (N : ℝ) / x + (Nat.card B : ℝ) / x := by
    calc
      (Nat.card E : ℝ) / x ≤ ((N : ℝ) + (Nat.card B : ℝ)) / x :=
        div_le_div_of_nonneg_right hcardE_real hxpos.le
      _ = (N : ℝ) / x + (Nat.card B : ℝ) / x := by ring
  have hB_ratio : (Nat.card B : ℝ) / x ≤ C / Real.sqrt (T : ℝ) := by
    have htmp := div_le_div_of_nonneg_right hB_bound hxpos.le
    have hsimp : (C * x / Real.sqrt (T : ℝ)) / x = C / Real.sqrt (T : ℝ) := by
      field_simp [hxpos.ne', hsqrtT_pos.ne']
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
      _ ≤ η / 2 + C / Real.sqrt (T : ℝ) := add_le_add hsmall_ratio hB_ratio
      _ < η / 2 + η / 2 := by nlinarith
      _ = η := by ring
  have hratio_nonneg : 0 ≤ (Nat.card E : ℝ) / x := by positivity
  change dist ((Nat.card E : ℝ) / x) 0 < η
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hratio_nonneg]
  exact hratio_lt

end Erdos696
