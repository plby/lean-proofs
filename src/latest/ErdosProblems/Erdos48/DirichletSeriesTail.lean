/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.WeightedSeriesDetector
import Mathlib.Analysis.Complex.Exponential

/-!
# Exponentially damped tails of weighted von Mangoldt series

The elementary inequalities in this file are the quantitative core of the
Dirichlet-series truncation.  A quarter of the factor `n ^ (-eta)` absorbs
the logarithmic weight, another quarter supplies an exponentially small
tail factor, and the remaining half is summed by the Chebyshev pole-order
bound.
-/

namespace Erdos48

open Complex LSeries
open BoundedGaps.Maynard

noncomputable section

/-- Exponential damping absorbs any fixed power of the logarithm. -/
theorem log_pow_mul_rpow_neg_quarter_le
    (eta : ℝ) (heta : 0 < eta) (n k : ℕ) (hn : 0 < n) :
    Real.log n ^ k * (n : ℝ) ^ (-eta / 4) ≤
      k.factorial * (4 / eta) ^ k := by
  let x : ℝ := eta * Real.log n / 4
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hpow : x ^ k ≤ (k.factorial : ℝ) * Real.exp x := by
    have h := Real.pow_div_factorial_le_exp x hx k
    rw [div_le_iff₀ hfac] at h
    simpa [mul_comm] using h
  have hdec : x ^ k * Real.exp (-x) ≤ (k.factorial : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-x)).le
    calc
      x ^ k * Real.exp (-x) ≤
          (k.factorial : ℝ) * Real.exp x * Real.exp (-x) := h
      _ = (k.factorial : ℝ) := by
        rw [mul_assoc, ← Real.exp_add]
        simp
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hrpow : (n : ℝ) ^ (-eta / 4) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos hnreal]
    congr 1
    dsimp [x]
    ring
  have hlog : Real.log n = (4 / eta) * x := by
    dsimp [x]
    field_simp [heta.ne']
  rw [hrpow, hlog, mul_pow]
  calc
    ((4 / eta) ^ k * x ^ k) * Real.exp (-x) =
        (4 / eta) ^ k * (x ^ k * Real.exp (-x)) := by ring
    _ ≤ (4 / eta) ^ k * (k.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = (k.factorial : ℝ) * (4 / eta) ^ k := by ring

/-- Past `exp (R / eta)`, a second quarter of the exponential damping is at
most `exp (-R/4)`. -/
theorem rpow_neg_quarter_le_exp_neg_quarter
    (eta R : ℝ) (heta : 0 < eta) {N n : ℕ}
    (hN : Real.exp (R / eta) ≤ (N : ℝ)) (hn : N < n) :
    (n : ℝ) ^ (-eta / 4) ≤ Real.exp (-R / 4) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hexp : Real.exp (R / eta) < (n : ℝ) :=
    hN.trans_lt (by exact_mod_cast hn)
  have hlog : R / eta < Real.log n :=
    (Real.lt_log_iff_exp_lt hnreal).2 hexp
  have hlog' : R < eta * Real.log n :=
    by simpa [mul_comm] using (div_lt_iff₀ heta).mp hlog
  rw [Real.rpow_def_of_pos hnreal]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Pointwise three-way split of a weighted von Mangoldt tail term. -/
theorem weighted_vonMangoldt_tail_term_le
    (eta R : ℝ) (heta : 0 < eta) {N n : ℕ}
    (hN : Real.exp (R / eta) ≤ (N : ℝ)) (hn : N < n) (k : ℕ) :
    Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
        (n : ℝ) ^ (-(1 + eta)) ≤
      Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
        (ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(1 + eta / 2))) := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlog := log_pow_mul_rpow_neg_quarter_le eta heta n k hnpos
  have hcut :=
    rpow_neg_quarter_le_exp_neg_quarter eta R heta hN hn
  have hsplit :
      (n : ℝ) ^ (-(1 + eta)) =
        (n : ℝ) ^ (-eta / 4) * (n : ℝ) ^ (-eta / 4) *
          (n : ℝ) ^ (-(1 + eta / 2)) := by
    calc
      (n : ℝ) ^ (-(1 + eta)) =
          (n : ℝ) ^ ((-eta / 4) + (-eta / 4) + (-(1 + eta / 2))) := by
        congr 1
        ring
      _ = (n : ℝ) ^ (-eta / 4) * (n : ℝ) ^ (-eta / 4) *
          (n : ℝ) ^ (-(1 + eta / 2)) := by
        rw [Real.rpow_add hnreal, Real.rpow_add hnreal]
  have hfirst :
      (Real.log n ^ k * (n : ℝ) ^ (-eta / 4)) *
          (n : ℝ) ^ (-eta / 4) ≤
        ((k.factorial : ℝ) * (4 / eta) ^ k) *
          Real.exp (-R / 4) := by
    exact mul_le_mul hlog hcut
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (by positivity)
  rw [hsplit]
  have hweight :
      0 ≤ ArithmeticFunction.vonMangoldt n *
        (n : ℝ) ^ (-(1 + eta / 2)) := by positivity
  calc
    Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
          ((n : ℝ) ^ (-eta / 4) * (n : ℝ) ^ (-eta / 4) *
            (n : ℝ) ^ (-(1 + eta / 2))) =
        ((Real.log n ^ k * (n : ℝ) ^ (-eta / 4)) *
          (n : ℝ) ^ (-eta / 4)) *
            (ArithmeticFunction.vonMangoldt n *
              (n : ℝ) ^ (-(1 + eta / 2))) := by ring
    _ ≤ (((k.factorial : ℝ) * (4 / eta) ^ k) *
          Real.exp (-R / 4)) *
            (ArithmeticFunction.vonMangoldt n *
              (n : ℝ) ^ (-(1 + eta / 2))) :=
      mul_le_mul_of_nonneg_right hfirst hweight
    _ = Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
        (ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(1 + eta / 2))) := by ring

/-- Absolute summability of the positive von Mangoldt Dirichlet series in
real-rpow form. -/
theorem summable_vonMangoldt_mul_rpow_neg
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma)) := by
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (sigma : ℂ)) (by simpa using hsigma)
  rw [LSeriesSummable] at hs
  refine hs.norm.congr ?_
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_re]
    ring

/-- The exponentially damped weighted von Mangoldt tail is controlled by
the full positive series at the shifted abscissa `1 + eta/2`. -/
theorem weighted_vonMangoldt_tail_tsum_le
    (eta R : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (N k : ℕ) (hN : Real.exp (R / eta) ≤ (N : ℝ)) :
    (∑' n : ℕ, if N < n then
        Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(1 + eta)) else 0) ≤
      Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
        ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2)) := by
  let a : ℕ → ℝ := fun n ↦
    if N < n then
      Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
        (n : ℝ) ^ (-(1 + eta))
    else 0
  let b : ℕ → ℝ := fun n ↦
    ArithmeticFunction.vonMangoldt n *
      (n : ℝ) ^ (-(1 + eta / 2))
  let K : ℝ := Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : Summable b := by
    dsimp [b]
    exact summable_vonMangoldt_mul_rpow_neg (by linarith)
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    dsimp [a]
    split <;> positivity
  have hab : ∀ n, a n ≤ K * b n := by
    intro n
    dsimp [a]
    split_ifs with hn
    · simpa only [K, b, mul_assoc] using
        weighted_vonMangoldt_tail_term_le eta R heta hN hn k
    · exact mul_nonneg hK (by dsimp [b]; positivity)
  have ha : Summable a :=
    Summable.of_nonneg_of_le ha0 hab (hb.mul_left K)
  have hpositive := vonMangoldt_tsum_le_chebyshev_div_sub_one
    (sigma := 1 + eta / 2) (by linarith)
  have htsumB :
      (∑' n, b n) ≤
        (Real.log 4 + 4) * (1 + eta / 2) / (eta / 2) := by
    have heq :
        (∑' n, b n) =
          ∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            (n : ℝ) ^ (1 + eta / 2) := by
      apply tsum_congr
      intro n
      dsimp [b]
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
      ring
    rw [heq]
    simpa only [add_sub_cancel_left] using hpositive
  change (∑' n, a n) ≤ K *
    ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2))
  calc
    (∑' n, a n) ≤ ∑' n, K * b n := ha.tsum_le_tsum hab (hb.mul_left K)
    _ = K * ∑' n, b n := tsum_mul_left
    _ ≤ K * ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2)) :=
      mul_le_mul_of_nonneg_left htsumB hK

/-- A weighted twisted `LSeries` differs from its truncation at `N` by the
same exponentially damped tail majorant. -/
theorem norm_weighted_vonMangoldt_LSeries_sub_sum_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (eta R t : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (N k : ℕ) (hN1 : 1 ≤ N)
    (hN : Real.exp (R / eta) ≤ (N : ℝ)) :
    let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
    let c : ℕ → ℂ := fun n ↦
      (Real.log n : ℂ) ^ k * chi n *
        (ArithmeticFunction.vonMangoldt n : ℂ)
    ‖LSeries c z - ∑ n ∈ Finset.Icc 1 N, LSeries.term c z n‖ ≤
      Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
        ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2)) := by
  dsimp only
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let c : ℕ → ℂ := fun n ↦
    (Real.log n : ℂ) ^ k * chi n *
      (ArithmeticFunction.vonMangoldt n : ℂ)
  let a : ℕ → ℝ := fun n ↦
    if N < n then
      Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
        (n : ℝ) ^ (-(1 + eta))
    else 0
  let b : ℕ → ℝ := fun n ↦
    ArithmeticFunction.vonMangoldt n *
      (n : ℝ) ^ (-(1 + eta / 2))
  let K : ℝ := Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k
  have hzre : z.re = 1 + eta := by simp [z]
  have hz1 : 1 < z.re := by rw [hzre]; linarith
  let base : ℕ → ℂ :=
    (fun n : ℕ ↦ chi n) *
      fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)
  have habs : LSeries.abscissaOfAbsConv base < z.re :=
    (abscissaOfAbsConv_twist_vonMangoldt_le_one chi).trans_lt
      (by exact_mod_cast hz1)
  have hiter : LSeriesSummable ((LSeries.logMul^[k]) base) z :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa only [LSeries.absicssaOfAbsConv_logPowMul] using habs)
  have hcoeff (n : ℕ) : (LSeries.logMul^[k]) base n = c n := by
    rw [iterate_logMul_apply]
    dsimp [base, c]
    ring
  have hc : LSeriesSummable c z :=
    (LSeriesSummable_congr z fun {_} _ ↦ hcoeff _).mp hiter
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : Summable b := by
    dsimp [b]
    exact summable_vonMangoldt_mul_rpow_neg (by linarith)
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    dsimp [a]
    split <;> positivity
  have hab : ∀ n, a n ≤ K * b n := by
    intro n
    dsimp [a]
    split_ifs with hn
    · simpa only [K, b, mul_assoc] using
        weighted_vonMangoldt_tail_term_le eta R heta hN hn k
    · exact mul_nonneg hK (by dsimp [b]; positivity)
  have ha : Summable a :=
    Summable.of_nonneg_of_le ha0 hab (hb.mul_left K)
  let S : Finset ℕ := Finset.Icc 1 N
  have hterm (n : ℕ) (hnS : n ∉ S) :
      ‖LSeries.term c z n‖ ≤ a n := by
    by_cases hn0 : n = 0
    · subst n
      simp [a]
    have hnTail : N < n := by
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      dsimp [S] at hnS
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnS
      omega
    dsimp [a]
    rw [if_pos hnTail, LSeries.norm_term_eq, if_neg hn0]
    have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hchi : ‖chi n‖ ≤ 1 := chi.norm_le_one (n : ZMod q)
    have hcNorm : ‖c n‖ ≤
        Real.log n ^ k * ArithmeticFunction.vonMangoldt n := by
      dsimp [c]
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hlog0, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hweight :
          0 ≤ Real.log n ^ k * ArithmeticFunction.vonMangoldt n := by
        positivity
      calc
        Real.log n ^ k * ‖chi n‖ * ArithmeticFunction.vonMangoldt n =
            ‖chi n‖ *
              (Real.log n ^ k * ArithmeticFunction.vonMangoldt n) := by ring
        _ ≤ 1 * (Real.log n ^ k * ArithmeticFunction.vonMangoldt n) :=
          mul_le_mul_of_nonneg_right hchi hweight
        _ = Real.log n ^ k * ArithmeticFunction.vonMangoldt n := one_mul _
    rw [hzre]
    calc
      ‖c n‖ / (n : ℝ) ^ (1 + eta) ≤
          (Real.log n ^ k * ArithmeticFunction.vonMangoldt n) /
            (n : ℝ) ^ (1 + eta) := by gcongr
      _ = Real.log n ^ k * ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(1 + eta)) := by
        rw [Real.rpow_neg (Nat.cast_nonneg n)]
        ring
  change ‖LSeries c z - ∑ n ∈ S, LSeries.term c z n‖ ≤ _
  rw [LSeries, ← hc.sum_add_tsum_subtype_compl S, add_sub_cancel_left]
  calc
    ‖∑' n : {n // n ∉ S}, LSeries.term c z n‖ ≤
        ∑' n : {n // n ∉ S}, ‖LSeries.term c z n‖ :=
      norm_tsum_le_tsum_norm (hc.norm.subtype _)
    _ ≤ ∑' n : {n // n ∉ S}, a n :=
      (hc.norm.subtype _).tsum_le_tsum
        (fun n ↦ hterm n n.property) (ha.subtype _)
    _ ≤ ∑' n, a n := ha.tsum_subtype_le a {n | n ∉ S} ha0
    _ ≤ Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
        ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2)) := by
      simpa only [a] using
        weighted_vonMangoldt_tail_tsum_le eta R heta heta1 N k hN

/-- A single truncation-radius constant makes the tail smaller than half of
the pointwise detector lower bound for every order in a fixed finite range. -/
theorem exists_weighted_vonMangoldt_tail_budget (J : ℕ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (eta : ℝ), 0 < eta → eta ≤ 1 →
        ∀ k : ℕ, k + 1 ≤ J →
          Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
              ((Real.log 4 + 4) * (1 + eta / 2) / (eta / 2)) ≤
            k.factorial * (1 / 24 : ℝ) * (2 * eta)⁻¹ ^ (k + 1) := by
  let C : ℝ := Real.log 4 + 4
  let D : ℝ := 1 + 72 * C * (4 : ℝ) ^ J * (2 : ℝ) ^ (J + 1)
  let R : ℝ := 4 * Real.log D
  have hC : 0 < C := by dsimp [C]; positivity
  have hD1 : 1 < D := by
    dsimp [D]
    have : 0 < 72 * C * (4 : ℝ) ^ J * (2 : ℝ) ^ (J + 1) := by
      positivity
    linarith
  have hD : 0 < D := zero_lt_one.trans hD1
  have hR : 0 < R := by
    dsimp [R]
    exact mul_pos (by norm_num) (Real.log_pos hD1)
  refine ⟨R, hR, ?_⟩
  intro eta heta heta1 k hkJ
  have hexp : Real.exp (-R / 4) = D⁻¹ := by
    have harg : -R / 4 = -Real.log D := by dsimp [R]; ring
    rw [harg, Real.exp_neg, Real.exp_log hD]
  have h4 : (4 : ℝ) ^ k ≤ (4 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (J + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hprod :
      72 * C * (4 : ℝ) ^ k * (2 : ℝ) ^ (k + 1) ≤ D := by
    calc
      72 * C * (4 : ℝ) ^ k * (2 : ℝ) ^ (k + 1) ≤
          72 * C * (4 : ℝ) ^ J * (2 : ℝ) ^ (J + 1) := by
        gcongr
      _ ≤ D := by dsimp [D]; linarith
  have hcoef :
      Real.exp (-R / 4) * 3 * C * (4 : ℝ) ^ k ≤
        1 / (24 * (2 : ℝ) ^ (k + 1)) := by
    rw [hexp]
    rw [le_div_iff₀ (by positivity : 0 < 24 * (2 : ℝ) ^ (k + 1))]
    calc
      D⁻¹ * 3 * C * (4 : ℝ) ^ k *
          (24 * (2 : ℝ) ^ (k + 1)) =
          (72 * C * (4 : ℝ) ^ k * (2 : ℝ) ^ (k + 1)) / D := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ 1 := (div_le_one hD).2 hprod
  have hratio :
      C * (1 + eta / 2) / (eta / 2) ≤ 3 * C / eta := by
    rw [div_le_div_iff₀ (by positivity : 0 < eta / 2) heta]
    have hsmall : 1 + eta / 2 ≤ (3 / 2 : ℝ) := by linarith
    have hCeta : 0 ≤ C * eta := by positivity
    calc
      C * (1 + eta / 2) * eta = (1 + eta / 2) * (C * eta) := by ring
      _ ≤ (3 / 2 : ℝ) * (C * eta) :=
        mul_le_mul_of_nonneg_right hsmall hCeta
      _ = 3 * C * (eta / 2) := by ring
  have htail :
      Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
          (C * (1 + eta / 2) / (eta / 2)) ≤
        Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
          (3 * C / eta) := by
    exact mul_le_mul_of_nonneg_left hratio (by positivity)
  have hleftEq :
      Real.exp (-R / 4) * k.factorial * (4 / eta) ^ k *
          (3 * C / eta) =
        (Real.exp (-R / 4) * 3 * C * (4 : ℝ) ^ k) *
          k.factorial * eta⁻¹ ^ (k + 1) := by
    rw [div_pow, inv_pow]
    field_simp [heta.ne']
    ring
  have hrightEq :
      k.factorial * (1 / 24 : ℝ) * (2 * eta)⁻¹ ^ (k + 1) =
        (1 / (24 * (2 : ℝ) ^ (k + 1))) *
          k.factorial * eta⁻¹ ^ (k + 1) := by
    rw [mul_inv_rev, mul_pow, inv_pow]
    field_simp [heta.ne']
    rw [← mul_pow]
    norm_num
  dsimp [C] at htail ⊢
  refine htail.trans ?_
  rw [hleftEq, hrightEq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by positivity)

end

end Erdos48
