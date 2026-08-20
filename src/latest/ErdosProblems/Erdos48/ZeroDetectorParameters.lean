/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PointwiseZeroDetector

/-!
# Uniform numerical parameters for the pointwise zero detector

After multiplication by `(2*eta)^j`, the four detector errors are bounded
respectively by a fixed geometric term, `O(eta log B)` times a geometric
term, and two `O(eta^2 log B)` terms.  This file chooses a fixed derivative
threshold and a small absolute `lambda` which make their sum fit the error
budget.
-/

namespace Erdos48

noncomputable section

/-- Fixed detector order and zero-free-width parameter which validate the
explicit pointwise error budget uniformly in the conductor and height. -/
theorem exists_pointwiseZeroDetector_parameters
    (Al Af Ad : ℕ) :
    ∃ L : ℕ, 2 ≤ L ∧ ∃ lambda : ℝ, 0 < lambda ∧
      ∀ (q : ℕ) (t eta : ℝ) (j : ℕ),
        4 ≤ (q : ℝ) * (|t| + 2) →
        0 < eta → eta ≤ 1 / 8 →
        eta * Real.log ((q : ℝ) * (|t| + 2)) ≤ lambda →
        L ≤ j →
        pointwiseZeroDetectorError Al Af Ad q t eta j ≤
          (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j := by
  let C : ℝ := Real.log 4 + 4
  have hC : 0 < C := by dsimp [C]; positivity
  have htarget : 0 < (1 : ℝ) / (48 * (64 * C)) := by positivity
  obtain ⟨L₀, hL₀⟩ := exists_pow_lt_of_lt_one htarget
    (by norm_num : (1 / 2 : ℝ) < 1)
  let L := max 2 L₀
  have hL2 : 2 ≤ L := le_max_left _ _
  have hgeomL : 64 * C * (1 / 2 : ℝ) ^ L ≤ 1 / 48 := by
    have hpow : (1 / 2 : ℝ) ^ L ≤ (1 / 2 : ℝ) ^ L₀ :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) (le_max_right _ _)
    have hsmall : 64 * C * (1 / 2 : ℝ) ^ L₀ < 1 / 48 := by
      have hpos : 0 < 48 * (64 * C) := by positivity
      calc
        64 * C * (1 / 2 : ℝ) ^ L₀ <
            64 * C * (1 / (48 * (64 * C))) := by
          exact mul_lt_mul_of_pos_left hL₀ (by positivity)
        _ = 1 / 48 := by field_simp
    exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hsmall.le
  let K : ℝ := 1 + 4096 * (Al : ℝ) / 3 + 4 * (Af : ℝ) +
    8 * (Ad : ℝ) / 3
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let lambda : ℝ := 1 / (96 * K)
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  refine ⟨L, hL2, lambda, hlambda, ?_⟩
  intro q t eta j hB4 heta0 heta8 hetalog hLj
  let u : ℝ := Real.log ((q : ℝ) * (|t| + 2))
  have hu : 0 ≤ u := Real.log_nonneg (by linarith)
  have heta : 0 ≤ eta := heta0.le
  have hhalfj : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ L :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hLj
  have hgeom : 64 * C * (1 / 2 : ℝ) ^ j ≤ 1 / 48 :=
    (mul_le_mul_of_nonneg_left hhalfj (by positivity)).trans hgeomL
  have hetaU : eta * u ≤ lambda := by simpa only [u] using hetalog
  have heta2U : eta ^ 2 * u ≤ lambda / 8 := by
    calc
      eta ^ 2 * u = eta * (eta * u) := by ring
      _ ≤ eta * lambda := mul_le_mul_of_nonneg_left hetaU heta
      _ ≤ (1 / 8 : ℝ) * lambda :=
        mul_le_mul_of_nonneg_right heta8 hlambda.le
      _ = lambda / 8 := by ring
  have hbase4 : 0 ≤ 4 * eta := by positivity
  have hbase4one : 4 * eta ≤ 1 := by linarith
  have hpow4 : (4 * eta) ^ j ≤ (4 * eta) ^ 2 :=
    pow_le_pow_of_le_one hbase4 hbase4one (hL2.trans hLj)
  have hbase2 : 0 ≤ 2 * eta := by positivity
  have hbase2one : 2 * eta ≤ 1 := by linarith
  have hpow2 : (2 * eta) ^ j ≤ (2 * eta) ^ 2 :=
    pow_le_pow_of_le_one hbase2 hbase2one (hL2.trans hLj)
  let c1 : ℝ := 64 * C * (1 / 2 : ℝ) ^ j
  let c2 : ℝ := (4096 * (Al : ℝ) / 3) * (eta * u) *
    (1 / 2 : ℝ) ^ j
  let c3 : ℝ := 2 * (Af : ℝ) * u * (4 * eta) ^ j
  let c4 : ℝ := 16 * (Ad : ℝ) * u / 3 * (2 * eta) ^ j
  have hc1 : c1 ≤ 1 / 48 := by simpa only [c1] using hgeom
  have hc2 : c2 ≤ (4096 * (Al : ℝ) / 3) * lambda := by
    dsimp [c2]
    have hhalfOne : (1 / 2 : ℝ) ^ j ≤ 1 := by
      exact (pow_le_one₀ (by positivity) (by norm_num))
    have hcoef : 0 ≤ 4096 * (Al : ℝ) / 3 := by positivity
    calc
      (4096 * (Al : ℝ) / 3) * (eta * u) * (1 / 2 : ℝ) ^ j ≤
          (4096 * (Al : ℝ) / 3) * lambda * (1 / 2 : ℝ) ^ j := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hetaU hcoef) (by positivity)
      _ ≤ (4096 * (Al : ℝ) / 3) * lambda := by
        exact mul_le_of_le_one_right (by positivity) hhalfOne
  have hc3 : c3 ≤ 4 * (Af : ℝ) * lambda := by
    dsimp [c3]
    calc
      2 * (Af : ℝ) * u * (4 * eta) ^ j ≤
          2 * (Af : ℝ) * u * (4 * eta) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hpow4 (mul_nonneg (by positivity) hu)
      _ = 32 * (Af : ℝ) * (eta ^ 2 * u) := by ring
      _ ≤ 32 * (Af : ℝ) * (lambda / 8) := by
        exact mul_le_mul_of_nonneg_left heta2U (by positivity)
      _ = 4 * (Af : ℝ) * lambda := by ring
  have hc4 : c4 ≤ 8 * (Ad : ℝ) / 3 * lambda := by
    dsimp [c4]
    calc
      16 * (Ad : ℝ) * u / 3 * (2 * eta) ^ j ≤
          16 * (Ad : ℝ) * u / 3 * (2 * eta) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hpow2 (by positivity)
      _ = (64 * (Ad : ℝ) / 3) * (eta ^ 2 * u) := by ring
      _ ≤ (64 * (Ad : ℝ) / 3) * (lambda / 8) := by
        exact mul_le_mul_of_nonneg_left heta2U (by positivity)
      _ = 8 * (Ad : ℝ) / 3 * lambda := by ring
  have hrest : c2 + c3 + c4 ≤ K * lambda := by
    dsimp [K]
    linarith
  have hKlambda : K * lambda = 1 / 96 := by
    dsimp [lambda]
    field_simp
  have hcoeff : c1 + c2 + c3 + c4 ≤ 1 / 12 := by
    rw [hKlambda] at hrest
    nlinarith
  let X : ℝ := (2 * eta) ^ j
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hratio : (2 * eta) / (4 * eta) = (1 / 2 : ℝ) := by
    field_simp [heta0.ne']
    norm_num
  have ht1 :
      (64 * C / (4 * eta) ^ j) * X = c1 := by
    dsimp [X, c1]
    calc
      (64 * C / (4 * eta) ^ j) * (2 * eta) ^ j =
          64 * C * ((2 * eta) ^ j / (4 * eta) ^ j) := by ring
      _ = 64 * C * ((2 * eta) / (4 * eta)) ^ j := by rw [div_pow]
      _ = 64 * C * (1 / 2 : ℝ) ^ j := by rw [hratio]
  have ht2 :
      (((1024 * (Al : ℝ) / 3) * u) / (4 * eta) ^ (j - 1)) * X = c2 := by
    let k := j - 1
    have hk : j - 1 = k := rfl
    have hj : j = k + 1 := by dsimp [k]; omega
    dsimp [X, c2]
    rw [show (1 / 2 : ℝ) ^ j =
        ((2 * eta) / (4 * eta)) ^ j by rw [hratio]]
    rw [div_pow, hk, hj, pow_succ, pow_succ]
    field_simp [heta0.ne']
    ring
  have ht3 :
      ((2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j) * X = c3 := by
    dsimp [X, c3]
    calc
      ((2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j) * (2 * eta) ^ j =
          2 * (Af : ℝ) * u *
            ((2 * eta) ^ j / (1 / 2 : ℝ) ^ j) := by ring
      _ = 2 * (Af : ℝ) * u *
            ((2 * eta) / (1 / 2 : ℝ)) ^ j := by rw [← div_pow]
      _ = 2 * (Af : ℝ) * u * (4 * eta) ^ j := by ring_nf
  have ht4 :
      (16 * ((Ad : ℝ) * u) / 3) * X = c4 := by
    dsimp [X, c4]
    ring
  have herrorMul :
      pointwiseZeroDetectorError Al Af Ad q t eta j * X =
        c1 + c2 + c3 + c4 := by
    dsimp [pointwiseZeroDetectorError]
    change
      (64 * C / (4 * eta) ^ j +
          ((1024 * (Al : ℝ) / 3) * u) / (4 * eta) ^ (j - 1) +
          (2 * (Af : ℝ) * u) / (1 / 2 : ℝ) ^ j +
          16 * ((Ad : ℝ) * u) / 3) * X = _
    rw [add_mul, add_mul, add_mul, ht1, ht2, ht3, ht4]
  have hscaled :
      pointwiseZeroDetectorError Al Af Ad q t eta j * X ≤ 1 / 12 := by
    rw [herrorMul]
    exact hcoeff
  have htargetEq :
      (1 / 12 : ℝ) * (2 * eta)⁻¹ ^ j = (1 / 12 : ℝ) / X := by
    dsimp [X]
    rw [inv_pow]
    ring
  rw [htargetEq]
  exact (le_div_iff₀ hXpos).2 hscaled

end

end Erdos48
