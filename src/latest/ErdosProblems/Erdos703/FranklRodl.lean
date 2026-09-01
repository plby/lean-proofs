import ErdosProblems.Erdos703.Iteration
import ErdosProblems.Erdos703.Endpoints

/-!
# The Frankl--Rödl iteration for Erdős Problem 703

This file combines the finite coordinate-section iteration with its two
McDiarmid endpoint estimates.  Everything is quantitative and finite.
-/

namespace Erdos703FranklRodl

open Nat Finset Real
open scoped BigOperators

noncomputable section

lemma log_one_add_lower {s : ℝ} (hs0 : 0 ≤ s) :
    s - s ^ 2 ≤ Real.log (1 + s) := by
  have hpos : 0 < 1 + s := by linarith
  have hbase := Real.one_sub_inv_le_log_of_pos hpos
  have heq : 1 - (1 + s)⁻¹ = s / (1 + s) := by
    field_simp [ne_of_gt hpos]
    ring
  rw [heq] at hbase
  have hfrac : s - s ^ 2 ≤ s / (1 + s) := by
    apply (le_div_iff₀ hpos).2
    nlinarith [mul_nonneg hs0 (sq_nonneg s)]
  exact hfrac.trans hbase

lemma log_fr_bad_lower {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) :
    -s - 4 * s ^ 2 ≤ Real.log (1 - s - 2 * s ^ 2) := by
  have hq : 0 < 1 - s - 2 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hbase := Real.one_sub_inv_le_log_of_pos hq
  have hcoef : 0 ≤ 1 - 6 * s - 8 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hpoly : 0 ≤ s ^ 2 * (1 - 6 * s - 8 * s ^ 2) :=
    mul_nonneg (sq_nonneg s) hcoef
  have hmul : (-s - 4 * s ^ 2) * (1 - s - 2 * s ^ 2) ≤ -(s + 2 * s ^ 2) := by
    nlinarith
  have heq : 1 - (1 - s - 2 * s ^ 2)⁻¹ =
      -(s + 2 * s ^ 2) / (1 - s - 2 * s ^ 2) := by
    apply (eq_div_iff hq.ne').2
    rw [sub_mul, one_mul, inv_mul_cancel₀ hq.ne']
    ring
  rw [heq] at hbase
  have hdiv : -s - 4 * s ^ 2 ≤
      -(s + 2 * s ^ 2) / (1 - s - 2 * s ^ 2) :=
    (le_div_iff₀ hq).2 hmul
  exact hdiv.trans hbase

lemma log_one_sub_sq_lower {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) :
    -2 * s ^ 2 ≤ Real.log (1 - s ^ 2) := by
  have hc : 0 < 1 - s ^ 2 := by nlinarith [sq_nonneg s]
  have hbase := Real.one_sub_inv_le_log_of_pos hc
  have hs_sq : s ^ 2 ≤ (1 / 10 : ℝ) ^ 2 :=
    by simpa [pow_two] using mul_self_le_mul_self hs0 hs
  have hmul : (-2 * s ^ 2) * (1 - s ^ 2) ≤ -(s ^ 2) := by
    nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) (sq_nonneg s)]
  have heq : 1 - (1 - s ^ 2)⁻¹ = -(s ^ 2) / (1 - s ^ 2) := by
    field_simp [ne_of_gt hc]
    ring
  rw [heq] at hbase
  exact ((le_div_iff₀ hc).2 hmul).trans hbase

/-- The logarithmic bookkeeping behind equation (8) of Frankl--Rödl.
The deliberately generous constant `20` keeps the later arithmetic robust. -/
lemma good_bad_balance {n A B : ℕ} {s p pstar : ℝ}
    (hs0 : 0 < s) (hs : s ≤ 1 / 10) (hsteps : A + B ≤ n)
    (hp : (1 - s ^ 2) ^ n < p)
    (hgain : (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * p ≤ pstar)
    (hpstar : pstar ≤ 1) :
    (A : ℝ) - B < 20 * s * n := by
  have hsnonneg : 0 ≤ s := hs0.le
  have hgpos : 0 < 1 + s := by linarith
  have hqpos : 0 < 1 - s - 2 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hcpos : 0 < 1 - s ^ 2 := by nlinarith [sq_nonneg s]
  have hppos : 0 < p := (pow_pos hcpos n).trans hp
  have hprodpos : 0 < (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * p := by positivity
  have hprodle : (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * p ≤ 1 :=
    hgain.trans hpstar
  have hlogle := Real.log_le_log hprodpos hprodle
  rw [Real.log_one] at hlogle
  have hlogexpand :
      Real.log ((1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * p) =
        (A : ℝ) * Real.log (1 + s) +
          (B : ℝ) * Real.log (1 - s - 2 * s ^ 2) + Real.log p := by
    rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hgpos.ne')
          (pow_ne_zero _ hqpos.ne')) hppos.ne',
      Real.log_mul (pow_ne_zero _ hgpos.ne') (pow_ne_zero _ hqpos.ne'),
      Real.log_pow, Real.log_pow]
  rw [hlogexpand] at hlogle
  have hlogp := Real.log_lt_log (pow_pos hcpos n) hp
  rw [Real.log_pow] at hlogp
  have hglog := log_one_add_lower hsnonneg
  have hqlog := log_fr_bad_lower hsnonneg hs
  have hclog := log_one_sub_sq_lower hsnonneg hs
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hstepsR : (A : ℝ) + B ≤ n := by exact_mod_cast hsteps
  have hslack : 0 ≤ (n : ℝ) - ((A : ℝ) + B) := sub_nonneg.mpr hstepsR
  by_contra hnot
  push Not at hnot
  have hlower :
      0 < (A : ℝ) * Real.log (1 + s) +
          (B : ℝ) * Real.log (1 - s - 2 * s ^ 2) + Real.log p := by
    have h1 := mul_le_mul_of_nonneg_left hglog hA0
    have h2 := mul_le_mul_of_nonneg_left hqlog hB0
    have h3 := mul_le_mul_of_nonneg_left hclog hn0
    nlinarith [mul_nonneg hsnonneg hslack]
  linarith

lemma exp_neg_le_one_sub_half {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  have habs := Real.abs_exp_sub_one_sub_id_le (x := -x) (by
    rw [abs_neg, abs_of_nonneg hx0]
    linarith)
  have hleft : Real.exp (-x) - 1 + x ≤ |Real.exp (-x) - 1 + x| :=
    le_abs_self _
  have hsquare : x ^ 2 ≤ x / 2 := by nlinarith
  rw [sub_neg_eq_add] at habs
  nlinarith

lemma fr_gain_lower {s : ℝ} {n A B : ℕ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) (hsteps : A + B ≤ n) :
    ((1 - s - 2 * s ^ 2) * (1 - s ^ 2)) ^ n ≤
      (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * (1 - s ^ 2) ^ n := by
  let q : ℝ := 1 - s - 2 * s ^ 2
  have hq0 : 0 ≤ q := by dsimp [q]; nlinarith [sq_nonneg s]
  have hq1 : q ≤ 1 := by dsimp [q]; nlinarith [sq_nonneg s]
  have hqg : q ≤ 1 + s := by dsimp [q]; nlinarith [sq_nonneg s]
  have hc0 : 0 ≤ 1 - s ^ 2 := by
    have hs_sq : s ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hs0 hs
    nlinarith
  have hpowexp : q ^ n ≤ q ^ (A + B) :=
    pow_le_pow_of_le_one hq0 hq1 hsteps
  have hpowbase : q ^ A ≤ (1 + s) ^ A :=
    pow_le_pow_left₀ hq0 hqg A
  calc
    (q * (1 - s ^ 2)) ^ n = q ^ n * (1 - s ^ 2) ^ n := mul_pow _ _ _
    _ ≤ q ^ (A + B) * (1 - s ^ 2) ^ n :=
      mul_le_mul_of_nonneg_right hpowexp (pow_nonneg hc0 n)
    _ = q ^ A * q ^ B * (1 - s ^ 2) ^ n := by rw [pow_add]
    _ ≤ (1 + s) ^ A * q ^ B * (1 - s ^ 2) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hc0 n)
      exact mul_le_mul_of_nonneg_right hpowbase (pow_nonneg hq0 B)
  
lemma fr_constant_exp_gap {eta : ℝ} (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    Real.exp (-(eta ^ 2 / 128)) <
      (1 - eta ^ 3 / 65536 - 2 * (eta ^ 3 / 65536) ^ 2) *
        (1 - (eta ^ 3 / 65536) ^ 2) := by
  let s : ℝ := eta ^ 3 / 65536
  let x : ℝ := eta ^ 2 / 128
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs : s < 1 / 10 := by
    dsimp [s]
    nlinarith [sq_pos_of_pos heta0, mul_pos (sq_pos_of_pos heta0) heta0]
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx : x ≤ 1 / 2 := by
    dsimp [x]
    nlinarith [sq_nonneg eta]
  have hsmall : 4 * s < x / 2 := by
    dsimp [s, x]
    have heta64 : eta < 64 := heta.trans (by norm_num)
    nlinarith [mul_pos (sq_pos_of_pos heta0) (sub_pos.mpr heta64)]
  have hD : 1 - 4 * s ≤ (1 - s - 2 * s ^ 2) * (1 - s ^ 2) := by
    have hpos : 0 ≤ s * (3 - 3 * s + s ^ 2 + 2 * s ^ 3) := by
      apply mul_nonneg hs0.le
      nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) hs0.le]
    nlinarith
  have hexp := exp_neg_le_one_sub_half hx0 hx
  change Real.exp (-x) < (1 - s - 2 * s ^ 2) * (1 - s ^ 2)
  exact hexp.trans_lt (lt_of_lt_of_le (by linarith) hD)

lemma fr_high_endpoint_bound {eta s : ℝ} {n r : ℕ}
    (heta0 : 0 < eta) (h20s : 20 * s < eta / 2) (hn : 0 < n)
    (hrlow : eta * n < r) {F G : Erdos703Iteration.Family n}
    (res : Erdos703Iteration.FRResult s (a := r) (b := r) F G)
    (hbalance : (res.A : ℝ) - res.B < 20 * s * n) (ha0 : res.a' = 0) :
    Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤
      Real.exp (-((eta ^ 2 / 128) * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmle : res.m' ≤ n := by have h := res.steps; omega
  have hmleR : (res.m' : ℝ) ≤ n := by exact_mod_cast hmle
  have hbB : res.b' = res.B := by
    have hl : res.a' + res.B + res.d = r := by simpa using res.lower
    have hu : res.b' + res.d = r := by simpa using res.upper
    omega
  have hrAB : (r : ℝ) ≤ res.A + res.B := by
    have hl : res.a' + res.B + res.d = r := by simpa using res.lower
    have hd : res.d ≤ res.A := res.shifts
    exact_mod_cast (show r ≤ res.A + res.B by omega)
  have h20sn : 20 * s * n < eta / 2 * n :=
    mul_lt_mul_of_pos_right h20s hnR
  have hBlarge : eta * n / 4 < (res.B : ℝ) := by
    have hrlowR : eta * n < (r : ℝ) := hrlow
    nlinarith
  have hBpos : 0 < res.B := by
    have : (0 : ℝ) < res.B := lt_of_le_of_lt (by positivity) hBlarge
    exact_mod_cast this
  have hmpos : 0 < res.m' := by
    have hb_le := res.interval.2
    rw [hbB] at hb_le
    omega
  have hmR : (0 : ℝ) < res.m' := by exact_mod_cast hmpos
  have hcross : ∀ S ∈ res.F', ∀ T ∈ res.G',
      (res.B : ℝ) ≤ # (S ∩ T) := by
    intro S hS T hT
    rcases res.avoids S hS T hT with hlt | hgt
    · omega
    · rw [hbB] at hgt
      exact_mod_cast hgt.le
  have hhigh := Erdos703Endpoints.cross_high hmpos
    (Erdos703Endpoints.fairCubeMcDiarmid res.m') res.F' res.G'
    (res.B : ℝ) (by positivity) hcross
  have hBbase0 : 0 ≤ eta * n / 4 := by positivity
  have hBsq := mul_self_lt_mul_self hBbase0 hBlarge
  have hdiv : (eta ^ 2 / 128) * n ≤ (res.B : ℝ) ^ 2 / res.m' := by
    apply (le_div_iff₀ hmR).2
    have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta0
    have hmnonneg : (0 : ℝ) ≤ res.m' := hmR.le
    have hprodle :=
      mul_le_mul_of_nonneg_left hmleR (mul_nonneg heta2.le hnR.le)
    nlinarith [sq_nonneg (res.B : ℝ)]
  have hexp : Real.exp (-(res.B : ℝ) ^ 2 / res.m') ≤
      Real.exp (-((eta ^ 2 / 128) * n)) := by
    apply Real.exp_le_exp.mpr
    simpa [neg_div] using neg_le_neg hdiv
  exact hhigh.trans hexp

lemma fr_low_endpoint_bound {eta s : ℝ} {n r : ℕ}
    (heta0 : 0 < eta) (heta : eta < 1 / 2) (h10s : 10 * s < eta / 2)
    (hn : 0 < n) (hrhigh : (r : ℝ) < (1 / 2 - eta) * n)
    (habsorb : Real.log 4 < eta ^ 2 * n / 128)
    {F G : Erdos703Iteration.Family n}
    (res : Erdos703Iteration.FRResult s (a := r) (b := r) F G)
    (hbalance : (res.A : ℝ) - res.B < 20 * s * n) (hbm : res.b' = res.m') :
    Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤
      Real.exp (-((eta ^ 2 / 128) * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hba : res.b' = res.a' + res.B := by
    have hu : res.b' + res.d = r := by simpa using res.upper
    have hl : res.a' + res.B + res.d = r := by simpa using res.lower
    omega
  have hmAB : res.m' = res.a' + res.B := by omega
  have hnr : (1 / 2 + eta) * n < (n : ℝ) - r := by nlinarith
  have hnrAB : (n : ℝ) - r = (res.A : ℝ) + res.B - res.d := by
    have hsR : (res.m' : ℝ) + res.A + res.B = n := by
      exact_mod_cast res.steps
    have hu : res.b' + res.d = r := by simpa using res.upper
    rw [hbm] at hu
    have huR : (res.m' : ℝ) + res.d = r := by exact_mod_cast hu
    linarith
  have hBlarge : (1 / 4 + eta / 2 - 10 * s) * n < (res.B : ℝ) := by
    rw [hnrAB] at hnr
    have hd0 : (0 : ℝ) ≤ res.d := by positivity
    nlinarith
  have hcoef : (1 / 4 : ℝ) < 1 / 4 + eta / 2 - 10 * s := by linarith
  have hmul : (1 / 4 : ℝ) * n <
      (1 / 4 + eta / 2 - 10 * s) * n :=
    mul_lt_mul_of_pos_right hcoef hnR
  have hmul' : (n : ℝ) / 4 <
      (1 / 4 + eta / 2 - 10 * s) * n := by
    simpa [div_eq_mul_inv, mul_comm] using hmul
  have hBn4 : (n : ℝ) / 4 < res.B := hmul'.trans hBlarge
  have hBm : (1 / 2 + eta / 2) * res.m' < (res.B : ℝ) := by
    have hmr : (res.m' : ℝ) < (1 / 2 - eta) * n := by
      have hmd : res.m' ≤ r := by
        have hu : res.b' + res.d = r := by simpa using res.upper
        rw [hbm] at hu
        omega
      have hmdR : (res.m' : ℝ) ≤ r := by exact_mod_cast hmd
      exact hmdR.trans_lt hrhigh
    have hcoefpos : 0 < 1 / 2 + eta / 2 := by linarith
    have hprod := mul_lt_mul_of_pos_left hmr hcoefpos
    have hcoefMargin :
        (1 / 2 + eta / 2) * (1 / 2 - eta) ≤
          1 / 4 + eta / 2 - 10 * s := by
      have hpositive : 0 < 3 * eta / 4 + eta ^ 2 / 2 - 10 * s := by
        nlinarith [sq_nonneg eta]
      nlinarith
    have hmargin :
        (1 / 2 + eta / 2) * ((1 / 2 - eta) * n) ≤
          (1 / 4 + eta / 2 - 10 * s) * n := by
      calc
        (1 / 2 + eta / 2) * ((1 / 2 - eta) * n) =
            ((1 / 2 + eta / 2) * (1 / 2 - eta)) * n := by ring
        _ ≤ (1 / 4 + eta / 2 - 10 * s) * n :=
          mul_le_mul_of_nonneg_right hcoefMargin hnR.le
    exact (hprod.trans_le hmargin).trans hBlarge
  have hmpos : 0 < res.m' := by
    have hnquarter0 : (0 : ℝ) ≤ n / 4 := by positivity
    have hBposR : (0 : ℝ) < res.B := hnquarter0.trans_lt hBn4
    have hBpos : 0 < res.B := by exact_mod_cast hBposR
    have hBmle : res.B ≤ res.m' := by rw [hmAB]; omega
    exact hBpos.trans_le hBmle
  have hcross : ∀ S ∈ res.F', ∀ T ∈ res.G',
      (#(S ∩ T) : ℝ) < (1 / 2 - eta / 2) * res.m' := by
    intro S hS T hT
    have hcardm : #(S ∩ T) ≤ res.m' := by
      calc
        #(S ∩ T) ≤ #S := card_le_card inter_subset_left
        _ ≤ #(Finset.univ : Finset (Fin res.m')) := card_le_univ _
        _ = res.m' := by simp
    have hcarda : #(S ∩ T) < res.a' := by
      rcases res.avoids S hS T hT with hlt | hgt
      · exact hlt
      · omega
    have hcast : (#(S ∩ T) : ℝ) < res.a' := by exact_mod_cast hcarda
    have hmaR : (res.m' : ℝ) = res.a' + res.B := by exact_mod_cast hmAB
    nlinarith
  have hlow := Erdos703Endpoints.cross_low hmpos
    (Erdos703Endpoints.fairCubeMcDiarmid res.m')
    (Erdos703Endpoints.cubeMean_card res.m') res.F' res.G'
    (eta / 2) (by positivity) hcross
  have hterm1 :
      2 * Real.exp (-((eta / 2) ^ 2 * res.m') / 2) ≤
        4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4) := by
    have he : Real.exp (-((eta / 2) ^ 2 * res.m') / 2) ≤
        Real.exp (-((eta / 2) ^ 2 * res.m') / 4) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ (eta / 2) ^ 2 * (res.m' : ℝ) := by positivity
      linarith
    nlinarith [Real.exp_pos (-((eta / 2) ^ 2 * res.m') / 4)]
  have hmax :
      max (2 * Real.exp (-((eta / 2) ^ 2 * res.m') / 2))
          (4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4)) ≤
        4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4) :=
    max_le hterm1 (le_refl _)
  have habs :
      4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4) ≤
        Real.exp (-((eta ^ 2 / 128) * n)) := by
    have hfour : 4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4) =
        Real.exp (Real.log 4 + -((eta / 2) ^ 2 * res.m') / 4) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    rw [hfour]
    apply Real.exp_le_exp.mpr
    have hBmle : res.B ≤ res.m' := by rw [hmAB]; omega
    have hBmleR : (res.B : ℝ) ≤ res.m' := by exact_mod_cast hBmle
    have hmquarter : (n : ℝ) / 4 < res.m' := hBn4.trans_le hBmleR
    have hscalePos : 0 < eta ^ 2 / 16 := by positivity
    have hscaled := mul_lt_mul_of_pos_left hmquarter hscalePos
    nlinarith
  exact (hlow.trans hmax).trans habs

/-- Quantitative cross-family forbidden-intersection theorem in sufficiently
large dimension.  This is the Frankl--Rödl theorem in the exact form used for
Erdős Problem 703. -/
theorem cross_forbidden_intersection_large {eta : ℝ}
    (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    ∃ N : ℕ, ∀ {n r : ℕ}, N ≤ n →
      eta * n < r → r < (1 / 2 - eta) * n →
      ∀ F G : Erdos703Iteration.Family n,
        Erdos703Iteration.CrossAvoids r r F G →
        Erdos703Iteration.density F * Erdos703Iteration.density G ≤
          (1 - (eta ^ 3 / 65536) ^ 2) ^ n := by
  let s : ℝ := eta ^ 3 / 65536
  let q : ℝ := 1 - s - 2 * s ^ 2
  let c : ℝ := 1 - s ^ 2
  let x : ℝ := eta ^ 2 / 128
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs : s ≤ 1 / 10 := by
    dsimp [s]
    have heta64 : eta < 64 := heta.trans (by norm_num)
    have hmul := mul_pos (sq_pos_of_pos heta0) (sub_pos.mpr heta64)
    nlinarith [sq_nonneg eta]
  have hq0 : 0 < q := by dsimp [q]; nlinarith [sq_nonneg s]
  have hq1 : q ≤ 1 := by dsimp [q]; nlinarith [sq_nonneg s]
  have hc0 : 0 < c := by dsimp [c]; nlinarith [sq_nonneg s]
  have h20s : 20 * s < eta / 2 := by
    dsimp [s]
    have heta0' : 0 < eta ^ 2 := sq_pos_of_pos heta0
    have hetaBound : eta < 819 := heta.trans (by norm_num)
    nlinarith [mul_pos heta0' (sub_pos.mpr hetaBound)]
  have h10s : 10 * s < eta / 2 := lt_trans (by linarith) h20s
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (128 * Real.log 4 / eta ^ 2)
  refine ⟨max N₀ 1, ?_⟩
  intro n r hnN hrlow hrhigh F G havoid
  have hnN₀ : N₀ ≤ n := (le_max_left _ _).trans hnN
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < max N₀ 1) hnN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrnR : (r : ℝ) < n := hrhigh.trans_le (by
    have : 1 / 2 - eta ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_right this hnR.le)
  have hrn : r ≤ n := by exact_mod_cast hrnR.le
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta0
  have hNmul : 128 * Real.log 4 < (N₀ : ℝ) * eta ^ 2 := by
    exact (div_lt_iff₀ heta2).mp hN₀
  have hnN₀R : (N₀ : ℝ) ≤ n := by exact_mod_cast hnN₀
  have habsorb : Real.log 4 < eta ^ 2 * n / 128 := by
    nlinarith [mul_le_mul_of_nonneg_right hnN₀R heta2.le]
  by_contra hnot
  push Not at hnot
  have hp : c ^ n < Erdos703Iteration.density F * Erdos703Iteration.density G := by
    simpa [c, s] using hnot
  let res := Erdos703Iteration.fr_iterate hs0.le hs F G (le_refl r)
    hrn
    havoid
  have hsteps : res.A + res.B ≤ n := by
    have h := res.steps
    omega
  have hpstar :
      Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤ 1 := by
    calc
      Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤
          1 * 1 := mul_le_mul (Erdos703Iteration.density_le_one _)
            (Erdos703Iteration.density_le_one _)
            (Erdos703Iteration.density_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hbalance : (res.A : ℝ) - res.B < 20 * s * n :=
    good_bad_balance hs0 hs hsteps hp (by simpa [mul_assoc] using res.density_gain) hpstar
  have hmle : res.m' ≤ n := by
    have h := res.steps
    omega
  have hmleR : (res.m' : ℝ) ≤ n := by exact_mod_cast hmle
  have hterminal :
      Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤
        Real.exp (-(x * n)) := by
    rcases res.terminal with ha0 | hbm
    · simpa [x] using
        fr_high_endpoint_bound heta0 h20s hn hrlow res hbalance ha0
    · simpa [x] using
        fr_low_endpoint_bound heta0 heta h10s hn hrhigh habsorb res hbalance hbm
  have hDgain : (q * c) ^ n <
      Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' := by
    have hbase := fr_gain_lower hs0.le hs hsteps
    change (q * c) ^ n ≤
        (1 + s) ^ res.A * q ^ res.B * c ^ n at hbase
    have hcoefpos : 0 < (1 + s) ^ res.A * q ^ res.B := by positivity
    have hmiddle :
        (1 + s) ^ res.A * q ^ res.B * c ^ n <
          (1 + s) ^ res.A * q ^ res.B *
            (Erdos703Iteration.density F * Erdos703Iteration.density G) :=
      mul_lt_mul_of_pos_left hp hcoefpos
    have hgain :
        (1 + s) ^ res.A * q ^ res.B *
            (Erdos703Iteration.density F * Erdos703Iteration.density G) ≤
          Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' := by
      simpa [q, mul_assoc] using res.density_gain
    exact hbase.trans_lt (hmiddle.trans_le hgain)
  have hgap : Real.exp (-x) < q * c := by
    simpa [x, q, c, s] using fr_constant_exp_gap heta0 heta
  have hpows : Real.exp (-x) ^ n < (q * c) ^ n :=
    pow_lt_pow_left₀ hgap (Real.exp_nonneg _) hn.ne'
  have hexppow : Real.exp (-x) ^ n = Real.exp (-(x * n)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexppow] at hpows
  linarith

/-- The one-family density consequence, with an explicit base strictly below
one. -/
theorem forbidden_family_density_large {eta : ℝ}
    (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    ∃ N : ℕ, ∀ {n r : ℕ}, N ≤ n →
      eta * n < r → r < (1 / 2 - eta) * n →
      ∀ F : Erdos703Iteration.Family n,
        Erdos703Iteration.CrossAvoids r r F F →
        Erdos703Iteration.density F <
          (1 - (eta ^ 3 / 65536) ^ 2 / 4) ^ n := by
  obtain ⟨N, hN⟩ := cross_forbidden_intersection_large heta0 heta
  refine ⟨max N 1, ?_⟩
  intro n r hnN hrlow hrhigh F havoid
  have hnN' : N ≤ n := (le_max_left _ _).trans hnN
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < max N 1) hnN
  have hcross := hN hnN' hrlow hrhigh F F havoid
  let u : ℝ := (eta ^ 3 / 65536) ^ 2
  let b : ℝ := 1 - u / 4
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    have heta64 : eta < 64 := heta.trans (by norm_num)
    have hsmall : eta ^ 3 / 65536 < 1 := by
      have := mul_pos (sq_pos_of_pos heta0) (sub_pos.mpr heta64)
      nlinarith [sq_nonneg eta]
    have hsq := mul_self_lt_mul_self
      (by positivity : 0 ≤ eta ^ 3 / 65536) hsmall
    simpa [pow_two] using hsq
  have hb0 : 0 < b := by dsimp [b]; nlinarith
  have hcb : 1 - u < b ^ 2 := by
    dsimp [b]
    nlinarith [sq_pos_of_pos hu0]
  have hcpow : (1 - u) ^ n < (b ^ 2) ^ n :=
    pow_lt_pow_left₀ hcb (by linarith : 0 ≤ 1 - u) hn.ne'
  by_contra hnot
  push Not at hnot
  have hsq : b ^ n * b ^ n ≤
      Erdos703Iteration.density F * Erdos703Iteration.density F :=
    mul_le_mul hnot hnot (pow_nonneg hb0.le n)
      (Erdos703Iteration.density_nonneg F)
  have hid : b ^ n * b ^ n = (b ^ 2) ^ n := by
    rw [pow_two, mul_pow]
  rw [hid] at hsq
  change Erdos703Iteration.density F * Erdos703Iteration.density F ≤
    (1 - u) ^ n at hcross
  linarith

lemma density_lt_base_pow_of_card_lt {N n : ℕ} (hN : 1 ≤ N)
    (hnN : n < N) {F : Erdos703Iteration.Family n}
    (hproper : #F < 2 ^ n) :
    Erdos703Iteration.density F <
      (1 - 1 / (2 : ℝ) ^ (2 * N)) ^ n := by
  let u : ℝ := 1 / (2 : ℝ) ^ (2 * N)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * N))).2 (by
      have hp : (1 : ℝ) < (2 : ℝ) ^ (2 * N) :=
        one_lt_pow₀ (by norm_num) (by omega)
      exact hp.le)
  have hBernoulli : 1 - (n : ℝ) * u ≤ (1 - u) ^ n := by
    have h := one_add_mul_le_pow (a := -u) (by linarith) n
    simpa [sub_eq_add_neg, mul_neg] using h
  have hnatpow : n * 2 ^ n < 2 ^ (2 * N) := by
    have hn2N : n < 2 ^ N := hnN.trans_le (Nat.le_of_lt N.lt_two_pow_self)
    have hpow : 2 ^ n ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) hnN.le
    calc
      n * 2 ^ n < 2 ^ N * 2 ^ n := Nat.mul_lt_mul_of_pos_right hn2N (pow_pos (by omega) _)
      _ ≤ 2 ^ N * 2 ^ N := Nat.mul_le_mul_left _ hpow
      _ = 2 ^ (2 * N) := by rw [← pow_add]; congr 1; omega
  have hnu : (n : ℝ) * u < 1 / (2 : ℝ) ^ n := by
    dsimp [u]
    rw [mul_one_div]
    have hcast : (n : ℝ) * (2 : ℝ) ^ n < (2 : ℝ) ^ (2 * N) := by
      exact_mod_cast hnatpow
    exact (div_lt_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hcast)
  have hcard : (#F : ℝ) ≤ (2 : ℝ) ^ n - 1 := by
    have hnat : #F + 1 ≤ 2 ^ n := by omega
    have hcast : (#F : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat
    linarith
  change (#F : ℝ) / (2 : ℝ) ^ n < (1 - u) ^ n
  have hdensity : (#F : ℝ) / (2 : ℝ) ^ n ≤
      1 - 1 / (2 : ℝ) ^ n := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).2
    field_simp
    linarith
  have hgap : 1 - 1 / (2 : ℝ) ^ n < 1 - (n : ℝ) * u := by linarith
  exact hdensity.trans_lt (hgap.trans_le hBernoulli)

lemma card_lt_cube_of_cross_avoids {n r : ℕ} (hrn : r ≤ n)
    {F : Erdos703Iteration.Family n}
    (havoid : Erdos703Iteration.CrossAvoids r r F F) : #F < 2 ^ n := by
  have hsub : F ⊆ (Finset.univ : Finset (Fin n)).powerset := by simp
  have hproper : F ⊂ (Finset.univ : Finset (Fin n)).powerset := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    have hnonempty : ((Finset.univ : Finset (Fin n)).powersetCard r).Nonempty := by
      apply card_pos.mp
      rw [card_powersetCard]
      simpa using Nat.choose_pos hrn
    obtain ⟨S, hS⟩ := hnonempty
    have hSdata := mem_powersetCard.mp hS
    have hSF : S ∈ F := by rw [heq]; exact mem_powerset.mpr hSdata.1
    rcases havoid S hSF S hSF with hlt | hgt <;>
      have hself : #(S ∩ S) = r := by simpa using hSdata.2
    · omega
    · omega
  simpa using card_lt_card hproper

/-- Uniform all-dimensions form of the one-family theorem. -/
theorem forbidden_family_density {eta : ℝ}
    (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      ∀ {n r : ℕ}, eta * n < r → r < (1 / 2 - eta) * n →
        ∀ F : Erdos703Iteration.Family n,
          Erdos703Iteration.CrossAvoids r r F F →
          Erdos703Iteration.density F < b ^ n := by
  obtain ⟨N, hlarge⟩ := forbidden_family_density_large heta0 heta
  let M : ℕ := max N 1
  have hM : 1 ≤ M := by dsimp [M]; exact le_max_right _ _
  let u : ℝ := (eta ^ 3 / 65536) ^ 2
  let bLarge : ℝ := 1 - u / 4
  let bSmall : ℝ := 1 - 1 / (2 : ℝ) ^ (2 * M)
  let b : ℝ := max bLarge bSmall
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    have heta64 : eta < 64 := heta.trans (by norm_num)
    have hsmall : eta ^ 3 / 65536 < 1 := by
      have := mul_pos (sq_pos_of_pos heta0) (sub_pos.mpr heta64)
      nlinarith [sq_nonneg eta]
    have hsq := mul_self_lt_mul_self
      (by positivity : 0 ≤ eta ^ 3 / 65536) hsmall
    simpa [pow_two] using hsq
  have hbLarge0 : 0 < bLarge := by dsimp [bLarge]; nlinarith
  have hbLarge1 : bLarge < 1 := by dsimp [bLarge]; linarith
  have hbSmall0 : 0 < bSmall := by
    dsimp [bSmall]
    have hp : (1 : ℝ) < (2 : ℝ) ^ (2 * M) := by
      have : 0 < 2 * M := by omega
      exact one_lt_pow₀ (by norm_num) this.ne'
    have hfrac : (1 : ℝ) / (2 : ℝ) ^ (2 * M) < 1 :=
      (div_lt_one (by positivity)).2 hp
    linarith
  have hbSmall1 : bSmall < 1 := by
    dsimp [bSmall]
    have hpos : 0 < 1 / (2 : ℝ) ^ (2 * M) := by positivity
    linarith
  refine ⟨b, lt_of_lt_of_le hbLarge0 (le_max_left _ _),
    max_lt hbLarge1 hbSmall1, ?_⟩
  intro n r hrlow hrhigh F havoid
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hh
    subst n
    norm_num at hrhigh
    have hr0 : (0 : ℝ) ≤ r := by positivity
    linarith
  by_cases hnM : M ≤ n
  · have hnN : N ≤ n := (le_max_left _ _).trans hnM
    have h := hlarge hnN hrlow hrhigh F havoid
    change Erdos703Iteration.density F < bLarge ^ n at h
    exact h.trans_le (pow_le_pow_left₀ hbLarge0.le (le_max_left _ _) n)
  · have hnM' : n < M := Nat.lt_of_not_ge hnM
    have hrnR : (r : ℝ) < n := hrhigh.trans_le (by
      have hc : 1 / 2 - eta ≤ 1 := by linarith
      simpa using mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ n))
    have hrn : r ≤ n := by exact_mod_cast hrnR.le
    have hproper := card_lt_cube_of_cross_avoids hrn havoid
    have h := density_lt_base_pow_of_card_lt hM hnM' hproper
    change Erdos703Iteration.density F < bSmall ^ n at h
    exact h.trans_le (pow_le_pow_left₀ hbSmall0.le (le_max_right _ _) n)

end

end Erdos703FranklRodl
