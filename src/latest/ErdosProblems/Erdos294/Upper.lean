/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos294.Definitions
import ErdosProblems.Erdos294.PrescribedFourier
import ErdosProblems.Erdos285.Lemma12

/-!
# The prime obstruction for the upper bound in Erdős Problem 294

This file formalizes the elementary half of Liu--Sawhney Theorem 1.6.  If a
prime `t` is large compared with `N / log N`, clearing a hypothetical unit
fraction representation modulo `t` forces a positive multiple of `t` to be
strictly smaller than `t`.
-/

open Filter Real
open scoped BigOperators Topology

namespace Erdos294.Upper

open Finset
open Erdos285.PrimePowers
open Erdos294.PrescribedFourier
open UnitFractions

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Quotients `n / t` contributed by denominators divisible by `t`. -/
def primeQuotients (A : Finset ℕ) (t : ℕ) : Finset ℕ :=
  (A.filter fun n ↦ t ∣ n).image fun n ↦ n / t

@[simp] lemma mem_primeQuotients {A : Finset ℕ} {t r : ℕ} :
    r ∈ primeQuotients A t ↔
      ∃ n ∈ A, t ∣ n ∧ n / t = r := by
  simp [primeQuotients, and_assoc]

lemma div_injective_on_multiples {t a b : ℕ} (ht : 0 < t)
    (ha : t ∣ a) (hb : t ∣ b) (hdiv : a / t = b / t) : a = b := by
  calc
    a = a / t * t := (Nat.div_mul_cancel ha).symm
    _ = b / t * t := by rw [hdiv]
    _ = b := Nat.div_mul_cancel hb

/-- Dividing through a chain of exact divisors. -/
lemma div_eq_div_mul_div {r L d : ℕ} (hr : 0 < r) (hL : 0 < L)
    (hrL : r ∣ L) (hLd : L ∣ d) :
    d / r = (d / L) * (L / r) := by
  obtain ⟨b, rfl⟩ := hrL
  obtain ⟨a, rfl⟩ := hLd
  have hrb : 0 < r * b := hL
  calc
    (r * b * a) / r = b * a := by
      rw [show r * b * a = r * (b * a) by ring,
        Nat.mul_div_cancel_left _ hr]
    _ = a * b := Nat.mul_comm _ _
    _ = ((r * b * a) / (r * b)) * ((r * b) / r) := by
      rw [Nat.mul_div_cancel_left _ hrb, Nat.mul_div_cancel_left _ hr]

lemma initialLcm_pos (m : ℕ) : 0 < initialLcm m := by
  rw [initialLcm, Nat.pos_iff_ne_zero, Finset.lcm_ne_zero_iff]
  intro r hr
  exact Nat.ne_of_gt (Finset.mem_Icc.mp hr).1

/-- A prime square cannot divide the LCM of integers all below that square. -/
lemma prime_sq_not_dvd_lcm {N t : ℕ} {A : Finset ℕ}
    (ht : t.Prime) (hApos : ∀ n ∈ A, n ≠ 0)
    (hAN : ∀ n ∈ A, n ≤ N) (hNt : N < t ^ 2) :
    ¬ t ^ 2 ∣ A.lcm id := by
  intro hdiv
  obtain ⟨n, hnA, htn⟩ :=
    Erdos285.Lemma12.isPrimePow_dvd_finsetLcm
      (ht.isPrimePow.pow (by norm_num : (2 : ℕ) ≠ 0)) hApos hdiv
  have hle : t ^ 2 ≤ n := Nat.le_of_dvd (hApos n hnA |> Nat.pos_of_ne_zero) htn
  exact (Nat.not_lt_of_ge (hle.trans (hAN n hnA))) hNt

/-- Finite prime obstruction.  The numerical hypothesis is exactly the one
needed after bounding the LCM of all possible quotients `n / t`. -/
theorem not_represents_of_prime
    {N t : ℕ} (ht : t.Prime) (htN : t ≤ N) (hNtSq : N < t ^ 2)
    (hsmall : (N / t) * initialLcm (N / t) < t) :
    ¬ Erdos294.Represents N t := by
  rintro ⟨htpos, A, htA, hbounds, hsum⟩
  have ht0 : 0 < t := ht.pos
  have hA0 : 0 ∉ A := by
    intro hzero
    have := (hbounds 0 hzero).1
    omega
  let D : ℕ := A.lcm id
  let d : ℕ := D / t
  let B : Finset ℕ := primeQuotients A t
  let L : ℕ := B.lcm id
  let s : ℕ := ∑ r ∈ B, L / r

  have htD : t ∣ D := by
    exact Finset.dvd_lcm htA
  have hD_eq : D = t * d := by
    dsimp [d]
    exact (Nat.mul_div_cancel' htD).symm
  have hD0 : D ≠ 0 := by
    dsimp [D]
    exact lcm_ne_zero_of_zero_not_mem hA0
  have htsqD : ¬ t ^ 2 ∣ D := by
    apply prime_sq_not_dvd_lcm ht
    · intro n hn
      exact fun hn0 ↦ hA0 (hn0 ▸ hn)
    · intro n hn
      exact (hbounds n hn).2
    · exact hNtSq
  have htd : ¬ t ∣ d := by
    intro h
    apply htsqD
    obtain ⟨a, ha⟩ := h
    refine ⟨a, ?_⟩
    rw [pow_two, hD_eq, ha]
    ring

  have hBsub : B ⊆ Finset.Icc 1 (N / t) := by
    intro r hr
    obtain ⟨n, hnA, htn, rfl⟩ := mem_primeQuotients.mp hr
    have htnle : t ≤ n := (hbounds n hnA).1
    have hmul : n / t * t ≤ N := by
      rw [Nat.div_mul_cancel htn]
      exact (hbounds n hnA).2
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos htnle ht0, (Nat.le_div_iff_mul_le ht0).2 hmul⟩
  have honeB : 1 ∈ B := by
    rw [mem_primeQuotients]
    exact ⟨t, htA, dvd_rfl, Nat.div_self ht0⟩
  have hBpos : ∀ r ∈ B, r ≠ 0 := by
    intro r hr
    exact Nat.ne_of_gt (Finset.mem_Icc.mp (hBsub hr)).1
  have hrD : ∀ r ∈ B, r ∣ d := by
    intro r hr
    obtain ⟨n, hnA, htn, hnquot⟩ := mem_primeQuotients.mp hr
    have hnD : n ∣ D := Finset.dvd_lcm hnA
    have hne : n = t * r := by
      calc
        n = t * (n / t) := (Nat.mul_div_cancel' htn).symm
        _ = t * r := by rw [hnquot]
    rw [hne, hD_eq] at hnD
    exact (Nat.mul_dvd_mul_iff_left ht0).mp hnD
  have hLpos : 0 < L := by
    dsimp [L]
    rw [Nat.pos_iff_ne_zero, Finset.lcm_ne_zero_iff]
    exact hBpos
  have hLd : L ∣ d := by
    dsimp [L]
    exact Finset.lcm_dvd hrD
  have hrL : ∀ r ∈ B, r ∣ L := by
    intro r hr
    exact Finset.dvd_lcm hr
  have hL_initial : L ∣ initialLcm (N / t) := by
    dsimp [L, initialLcm]
    exact Finset.lcm_mono hBsub
  have hLle : L ≤ initialLcm (N / t) :=
    Nat.le_of_dvd (initialLcm_pos (N / t)) hL_initial
  have hBcard : B.card ≤ N / t := by
    have := Finset.card_le_card hBsub
    simpa using this

  have hspos : 0 < s := by
    have hterm : 0 < L / 1 := by simpa using hLpos
    dsimp [s]
    have hle : L / 1 ≤ ∑ r ∈ B, L / r := by
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) honeB
    exact hterm.trans_le hle
  have hsle : s ≤ (N / t) * initialLcm (N / t) := by
    calc
      s ≤ ∑ _r ∈ B, L := by
        dsimp [s]
        exact Finset.sum_le_sum fun r hr ↦ Nat.div_le_self L r
      _ = B.card * L := by simp
      _ ≤ (N / t) * initialLcm (N / t) :=
        Nat.mul_le_mul hBcard hLle
  have hst : s < t := hsle.trans_lt hsmall

  have hscaled : scaledNumerator A A = D := by
    have hrec := rec_sum_eq_scaledNumerator_div hA0 (fun _ h ↦ h)
    rw [hsum] at hrec
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
    have hcast : (scaledNumerator A A : ℚ) = D := by
      apply (div_eq_one_iff_eq hDq).mp
      simpa [D] using hrec.symm
    exact_mod_cast hcast
  have hsumSplit :
      (∑ n ∈ A.filter (fun n ↦ t ∣ n), D / n) +
        (∑ n ∈ A.filter (fun n ↦ ¬ t ∣ n), D / n) = D := by
    rw [Finset.sum_filter_add_sum_filter_not]
    simpa [scaledNumerator, D] using hscaled
  have hnonmultiple :
      t ∣ ∑ n ∈ A.filter (fun n ↦ ¬ t ∣ n), D / n := by
    apply Finset.dvd_sum
    intro n hn
    have hnA := (Finset.mem_filter.mp hn).1
    have htnd := (Finset.mem_filter.mp hn).2
    have hnD : n ∣ D := Finset.dvd_lcm hnA
    have hmul : t ∣ n * (D / n) := by
      rw [Nat.mul_div_cancel' hnD]
      exact htD
    exact (ht.dvd_mul.mp hmul).resolve_left htnd
  have hmultiple_eq :
      (∑ n ∈ A.filter (fun n ↦ t ∣ n), D / n) =
        ∑ r ∈ B, d / r := by
    have hinj : Set.InjOn (fun n ↦ n / t) ↑(A.filter fun n ↦ t ∣ n) := by
      intro a ha b hb hab
      exact div_injective_on_multiples ht0
        (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
    calc
      (∑ n ∈ A.filter (fun n ↦ t ∣ n), D / n) =
          ∑ n ∈ A.filter (fun n ↦ t ∣ n), d / (n / t) := by
        apply Finset.sum_congr rfl
        intro n hn
        have htn := (Finset.mem_filter.mp hn).2
        have hn_eq : n = t * (n / t) := (Nat.mul_div_cancel' htn).symm
        calc
          D / n = (t * d) / (t * (n / t)) :=
            congrArg₂ Nat.div hD_eq hn_eq
          _ = d / (n / t) := Nat.mul_div_mul_left d (n / t) ht0
      _ = ∑ r ∈ B, d / r := by
        dsimp [B, primeQuotients]
        rw [Finset.sum_image hinj]
  have hfactor : (∑ r ∈ B, d / r) = (d / L) * s := by
    dsimp [s]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    exact div_eq_div_mul_div (Nat.pos_of_ne_zero (hBpos r hr)) hLpos
      (hrL r hr) hLd
  have htMultiple : t ∣ ∑ r ∈ B, d / r := by
    rw [← hmultiple_eq]
    apply (Nat.dvd_add_iff_left hnonmultiple).2
    rw [hsumSplit]
    exact htD
  have htProd : t ∣ (d / L) * s := by simpa [hfactor] using htMultiple
  have htDiv : ¬ t ∣ d / L := by
    intro h
    apply htd
    have hquot : d / L ∣ d := by
      refine ⟨L, ?_⟩
      simpa [mul_comm] using (Nat.div_mul_cancel hLd).symm
    exact h.trans hquot
  have hts : t ∣ s := (ht.dvd_mul.mp htProd).resolve_left htDiv
  exact (Nat.not_lt_of_ge (Nat.le_of_dvd hspos hts)) hst

/-! ## Asymptotic selection of the obstructing prime -/

lemma eventually_log_pow_four_lt_nat :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ 4 < (N : ℝ) := by
  have hlittle := Real.isLittleO_pow_log_id_atTop (n := 4)
  have hbound := hlittle.bound (show 0 < (1 / 2 : ℝ) by norm_num)
  have hnat := tendsto_natCast_atTop_atTop.eventually hbound
  filter_upwards [hnat, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hhalf : Real.log (N : ℝ) ^ 4 ≤ (1 / 2 : ℝ) * N := by
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hlog0,
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N), id_eq] at hN
    exact hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  linarith

/-- Bertrand's postulate and the exponential LCM estimate give the desired
`O(N / log N)` forbidden denominator. -/
theorem eventually_firstForbidden_le_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        (Erdos294.firstForbidden N : ℝ) ≤ C * Erdos294.upperProfile N := by
  obtain ⟨Clcm, hClcm, hLCM⟩ := exists_initialLcm_le_exp
  let a : ℝ := 4 * (Clcm + 1)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha1 : 1 ≤ a := by
    dsimp [a]
    linarith
  let C : ℝ := 4 * a
  have hC : 0 < C := mul_pos (by norm_num) ha
  refine ⟨C, hC, ?_⟩
  have hlogLarge :
      ∀ᶠ N : ℕ in atTop, 4 * a ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 * a))
  filter_upwards [eventually_log_pow_four_lt_nat, hlogLarge,
    eventually_ge_atTop (4 : ℕ)] with N hlog4 hlogLargeN hN4
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le (mul_pos (by norm_num) ha) hlogLargeN
  have hlogSq : Real.log (N : ℝ) ^ 2 < (N : ℝ) := by
    have hfour : (4 : ℝ) ≤ 4 * a := by nlinarith
    have hlogOne : 1 ≤ Real.log (N : ℝ) :=
      (by norm_num : (1 : ℝ) ≤ 4) |>.trans (hfour.trans hlogLargeN)
    have hpow : Real.log (N : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ 4 := by
      nlinarith [sq_nonneg (Real.log (N : ℝ) ^ 2 - 1)]
    exact hpow.trans_lt hlog4
  have hlogSq_lt_sqrt : Real.log (N : ℝ) ^ 2 < Real.sqrt (N : ℝ) := by
    have hsqrt0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have hsqrtSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
      Real.sq_sqrt hNR.le
    nlinarith
  let x : ℝ := a * (N : ℝ) / Real.log (N : ℝ)
  let m : ℕ := ⌈x⌉₊
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hx1 : 1 ≤ x := by
    have hlogLeN : Real.log (N : ℝ) ≤ (N : ℝ) := by
      exact (Real.log_le_sub_one_of_pos hNR).trans (by linarith)
    rw [le_div_iff₀ hlog]
    have haN : (N : ℝ) ≤ a * (N : ℝ) := by nlinarith
    simpa using hlogLeN.trans haN
  have hm0 : m ≠ 0 := by
    have hmge : (1 : ℝ) ≤ (m : ℝ) := hx1.trans (Nat.le_ceil x)
    exact fun hm ↦ by norm_num [m, hm] at hmge
  obtain ⟨t, ht, hmt, htm⟩ := Nat.bertrand m hm0
  have hxm : x ≤ (m : ℝ) := Nat.le_ceil x
  have hmtR : x < (t : ℝ) :=
    hxm.trans_lt (by exact_mod_cast hmt)
  have hmUpper : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one hx.le
  have hmTwoX : (m : ℝ) ≤ 2 * x := by linarith
  have htUpper : (t : ℝ) ≤ 4 * x := by
    have : (t : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast htm
    linarith
  have hfourxN : 4 * x ≤ (N : ℝ) := by
    dsimp [x]
    rw [show 4 * (a * (N : ℝ) / Real.log (N : ℝ)) =
      (4 * a * (N : ℝ)) / Real.log (N : ℝ) by ring,
      div_le_iff₀ hlog]
    nlinarith
  have htN : t ≤ N := by
    exact_mod_cast htUpper.trans hfourxN
  have hxSq : (N : ℝ) < x ^ 2 := by
    dsimp [x]
    rw [div_pow]
    apply (lt_div_iff₀ (sq_pos_of_pos hlog)).2
    have : Real.log (N : ℝ) ^ 2 < a ^ 2 * (N : ℝ) := by
      exact hlogSq.trans_le (by nlinarith [sq_nonneg (a - 1), hNR])
    nlinarith
  have hNtSq : N < t ^ 2 := by
    have htSqR : (N : ℝ) < (t : ℝ) ^ 2 :=
      hxSq.trans_le (pow_le_pow_left₀ hx.le hmtR.le 2)
    exact_mod_cast htSqR
  let q : ℕ := N / t
  have hqCast : (q : ℝ) ≤ (N : ℝ) / t := by
    exact Nat.cast_div_le
  have hqLog : (q : ℝ) < Real.log (N : ℝ) / a := by
    have hNx : (N : ℝ) / t < (N : ℝ) / x := by
      apply (div_lt_div_iff₀ (by exact_mod_cast ht.pos) hx).2
      nlinarith
    have hNxEq : (N : ℝ) / x = Real.log (N : ℝ) / a := by
      dsimp [x]
      field_simp [ha.ne', hlog.ne']
    exact hqCast.trans_lt (hNx.trans_eq hNxEq)
  have hqLogWeak : (q : ℝ) ≤ Real.log (N : ℝ) := by
    exact hqLog.le.trans (div_le_self hlog.le ha1)
  have hCq : Clcm * (q : ℝ) ≤ Real.log (N : ℝ) / 2 := by
    have hratio : Clcm / a ≤ 1 / 4 := by
      dsimp [a]
      rw [div_le_iff₀ (mul_pos (by norm_num) (by linarith : 0 < Clcm + 1))]
      nlinarith
    calc
      Clcm * (q : ℝ) ≤ Clcm * (Real.log (N : ℝ) / a) :=
        mul_le_mul_of_nonneg_left hqLog.le hClcm.le
      _ = (Clcm / a) * Real.log (N : ℝ) := by ring
      _ ≤ (1 / 4 : ℝ) * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_right hratio hlog.le
      _ ≤ Real.log (N : ℝ) / 2 := by linarith
  have hLcmSqrt : (initialLcm q : ℝ) ≤ Real.sqrt (N : ℝ) := by
    calc
      (initialLcm q : ℝ) ≤ Real.exp (Clcm * q) := hLCM q
      _ ≤ Real.exp (Real.log (N : ℝ) / 2) :=
        Real.exp_le_exp.mpr hCq
      _ = Real.sqrt (N : ℝ) := by
        rw [Real.exp_half, Real.exp_log hNR]
  have hsmallR :
      ((q * initialLcm q : ℕ) : ℝ) < (t : ℝ) := by
    have hqL :
        ((q * initialLcm q : ℕ) : ℝ) ≤
          Real.log (N : ℝ) * Real.sqrt (N : ℝ) := by
      push_cast
      calc
        (q : ℝ) * initialLcm q ≤
            Real.log (N : ℝ) * initialLcm q :=
          mul_le_mul_of_nonneg_right hqLogWeak (by positivity)
        _ ≤ Real.log (N : ℝ) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_left hLcmSqrt hlog.le
    have hlogSqrtN :
        Real.log (N : ℝ) * Real.sqrt (N : ℝ) < x := by
      rw [lt_div_iff₀ hlog]
      have hsqrtSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
        Real.sq_sqrt hNR.le
      have hcore :
          Real.log (N : ℝ) ^ 2 * Real.sqrt (N : ℝ) < (N : ℝ) := by
        nlinarith [Real.sqrt_nonneg (N : ℝ)]
      nlinarith [ha1]
    exact hqL.trans_lt (hlogSqrtN.trans hmtR)
  have hsmall : q * initialLcm q < t := by exact_mod_cast hsmallR
  have hnrep : ¬ Erdos294.Represents N t :=
    not_represents_of_prime ht htN hNtSq (by simpa [q] using hsmall)
  have hfirst : Erdos294.firstForbidden N ≤ t :=
    Nat.find_min' (Erdos294.exists_positive_not_represents N)
      ⟨ht.one_le, hnrep⟩
  calc
    (Erdos294.firstForbidden N : ℝ) ≤ (t : ℝ) := by exact_mod_cast hfirst
    _ ≤ C * Erdos294.upperProfile N := by
      dsimp [C, Erdos294.upperProfile, x]
      convert htUpper using 1 <;> ring

end

end Erdos294.Upper
