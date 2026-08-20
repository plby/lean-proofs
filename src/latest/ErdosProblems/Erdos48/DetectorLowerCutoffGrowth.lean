/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.BandLimitedDetector
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Growth of the lower detector cutoff

The exponent `floor (8 log B)` was chosen so that the lower detector cutoff
dominates a fixed fourth power of every integral global parameter `B ≥ 2`.
-/

namespace Erdos48

noncomputable section

theorem pow_four_le_zeroDetectorLowerCutoff (b : ℕ) (hb : 2 ≤ b) :
    b ^ 4 ≤ zeroDetectorLowerCutoff (b : ℝ) := by
  let M : ℕ := zeroDetectorLowerLog (b : ℝ)
  have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbPos : (0 : ℝ) < b := by positivity
  have hlogb : Real.log 2 ≤ Real.log (b : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hbPos hbReal
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoeff : 0 ≤ 8 * Real.log 2 - 4 := by
    nlinarith [Real.log_two_gt_d9]
  have hcoeffStrong : 0 ≤ 8 * Real.log 2 - 5 := by
    nlinarith [Real.log_two_gt_d9]
  have hscale := mul_le_mul_of_nonneg_left hlogb hcoeff
  have hself : Real.log 2 ≤
      (8 * Real.log 2 - 4) * Real.log 2 := by
    have := mul_nonneg hlog2pos.le hcoeffStrong
    nlinarith
  have hfour : 4 * Real.log (b : ℝ) ≤
      (8 * Real.log (b : ℝ) - 1) * Real.log 2 := by
    nlinarith
  have hfloor : 8 * Real.log (b : ℝ) - 1 < (M : ℝ) := by
    dsimp [M, zeroDetectorLowerLog]
    exact Nat.sub_one_lt_floor _
  have hlogBound : 4 * Real.log (b : ℝ) ≤
      (M : ℝ) * Real.log 2 := by
    exact hfour.trans (mul_le_mul_of_nonneg_right hfloor.le hlog2pos.le)
  have hreal : ((b ^ 4 : ℕ) : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by
    push_cast
    calc
      (b : ℝ) ^ 4 = Real.exp (Real.log ((b : ℝ) ^ 4)) := by
        rw [Real.exp_log (by positivity)]
      _ ≤ Real.exp (Real.log ((2 : ℝ) ^ M)) := by
        apply Real.exp_le_exp.mpr
        rw [Real.log_pow]
        norm_num
        exact hlogBound
      _ = (2 : ℝ) ^ M := Real.exp_log (by positivity)
  have hnat : b ^ 4 ≤ 2 ^ M := by exact_mod_cast hreal
  simpa only [zeroDetectorLowerCutoff, M] using hnat

theorem detectorLowerCutoff_height_bound
    (Q T : ℕ) (hQ : 2 ≤ Q) :
    2 * (T + 2) ≤ zeroDetectorLowerCutoff
      ((Q : ℝ) * ((T : ℝ) + 2)) := by
  let b := Q * (T + 2)
  have hb : 2 ≤ b := by dsimp [b]; nlinarith
  have hpow := pow_four_le_zeroDetectorLowerCutoff b hb
  have hsmall : 2 * (T + 2) ≤ b ^ 4 := by
    have hfirst : 2 * (T + 2) ≤ b := by
      dsimp [b]
      exact Nat.mul_le_mul_right (T + 2) hQ
    exact hfirst.trans (Nat.le_pow (by omega : 0 < 4))
  have hcast : (b : ℝ) = (Q : ℝ) * ((T : ℝ) + 2) := by
    dsimp [b]
    push_cast
    ring
  rw [← hcast]
  exact hsmall.trans hpow

theorem detectorLowerCutoff_conductor_bound
    (Q T : ℕ) (hQ : 2 ≤ Q) :
    2 * Q ^ 2 ≤ zeroDetectorLowerCutoff
      ((Q : ℝ) * ((T : ℝ) + 2)) := by
  let b := Q * (T + 2)
  have hb : 2 ≤ b := by dsimp [b]; nlinarith
  have hpow := pow_four_le_zeroDetectorLowerCutoff b hb
  have hsmall : 2 * Q ^ 2 ≤ b ^ 4 := by
    have hQb : Q ≤ b := by
      dsimp [b]
      calc
        Q = Q * 1 := by omega
        _ ≤ Q * (T + 2) := Nat.mul_le_mul_left Q (by omega)
    have hsq : Q ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hQb 2
    have htwo : 2 ≤ b ^ 2 := hb.trans (Nat.le_pow (by omega : 0 < 2))
    calc
      2 * Q ^ 2 ≤ 2 * b ^ 2 := Nat.mul_le_mul_left 2 hsq
      _ ≤ b ^ 2 * b ^ 2 := Nat.mul_le_mul_right (b ^ 2) htwo
      _ = b ^ 4 := by ring
  have hcast : (b : ℝ) = (Q : ℝ) * ((T : ℝ) + 2) := by
    dsimp [b]
    push_cast
    ring
  rw [← hcast]
  exact hsmall.trans hpow

/-- The fourth-power lower cutoff is large enough for the genuinely hybrid
large sieve.  Keeping the product of height and conductor squared intact is
essential: it removes the spurious linear-height loss in the first version
of the detector envelope. -/
theorem detectorLowerCutoff_hybrid_bound
    (Q T : ℕ) (hQ : 2 ≤ Q) :
    2 * (T + 2) * Q ^ 2 ≤ zeroDetectorLowerCutoff
      ((Q : ℝ) * ((T : ℝ) + 2)) := by
  let b := Q * (T + 2)
  have hb : 2 ≤ b := by dsimp [b]; nlinarith
  have hpow := pow_four_le_zeroDetectorLowerCutoff b hb
  have hQb : Q ≤ b := by
    dsimp [b]
    calc
      Q = Q * 1 := by omega
      _ ≤ Q * (T + 2) := Nat.mul_le_mul_left Q (by omega)
  have hTb : T + 2 ≤ b := by
    dsimp [b]
    calc
      T + 2 = 1 * (T + 2) := by omega
      _ ≤ Q * (T + 2) := Nat.mul_le_mul_right (T + 2) (by omega)
  have hsmall : 2 * (T + 2) * Q ^ 2 ≤ b ^ 4 := by
    calc
      2 * (T + 2) * Q ^ 2 ≤ 2 * b * b ^ 2 := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 hTb)
          (Nat.pow_le_pow_left hQb 2)
      _ ≤ b ^ 2 * b ^ 2 := by
        have htwoB : 2 * b ≤ b ^ 2 := by
          calc
            2 * b ≤ b * b := Nat.mul_le_mul_right b hb
            _ = b ^ 2 := by ring
        exact Nat.mul_le_mul_right (b ^ 2) htwoB
      _ = b ^ 4 := by ring
  have hcast : (b : ℝ) = (Q : ℝ) * ((T : ℝ) + 2) := by
    dsimp [b]
    push_cast
    ring
  rw [← hcast]
  exact hsmall.trans hpow

end

end Erdos48
