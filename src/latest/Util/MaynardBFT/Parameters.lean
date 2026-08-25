import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A family of dimensions and decay parameters

The dimension grows exponentially in the requested run length, while the
decay parameter grows linearly.  The two logarithmic bounds are the inputs
to the product-density first-moment and short-fiber estimates.
-/

namespace MaynardBFT

noncomputable section

def dimension (s : ℕ) : ℕ := 2 ^ (512 * s)

def decay (s : ℕ) : ℝ := 1024 * s

theorem dimension_pos (s : ℕ) : 0 < dimension s :=
  pow_pos (by norm_num) _

theorem dimension_ge_two {s : ℕ} (hs : 0 < s) : 2 ≤ dimension s := by
  apply le_trans (show 2 = 2 ^ 1 by norm_num).le
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem decay_pos {s : ℕ} (hs : 0 < s) : 0 < decay s := by
  exact mul_pos (by norm_num) (Nat.cast_pos.mpr hs)

theorem decay_ge_1024 {s : ℕ} (hs : 0 < s) : 1024 ≤ decay s := by
  have : (1 : ℝ) ≤ s := Nat.one_le_cast.mpr hs
  dsimp [decay]
  linarith

theorem decay_le_power (s : ℕ) :
    decay s ≤ (2 : ℝ) ^ (10 * s) := by
  have hnat : 1024 * s ≤ 1024 ^ s := Nat.mul_le_pow (by norm_num) s
  have hcast : (1024 : ℝ) * s ≤ (1024 : ℝ) ^ s := by exact_mod_cast hnat
  simpa only [decay, pow_mul, show (2 : ℝ) ^ 10 = 1024 by norm_num] using hcast

theorem log_dimension (s : ℕ) :
    Real.log (dimension s : ℝ) = 512 * s * Real.log 2 := by
  simp only [dimension, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]

theorem decay_mul_dimension_gt_one {s : ℕ} (hs : 0 < s) :
    1 < decay s * dimension s := by
  have hA := decay_ge_1024 hs
  have hK : (2 : ℝ) ≤ dimension s := by exact_mod_cast dimension_ge_two hs
  nlinarith

theorem log_one_add_decay_dimension_lt {s : ℕ} (hs : 0 < s) :
    Real.log (1 + decay s * dimension s) < 3 * decay s / 8 := by
  have hAK : 0 < decay s * dimension s :=
    mul_pos (decay_pos hs) (Nat.cast_pos.mpr (dimension_pos s))
  have hAKone := decay_mul_dimension_gt_one hs
  have hpow : decay s * dimension s ≤ (2 : ℝ) ^ (522 * s) := by
    calc
      decay s * dimension s ≤ (2 : ℝ) ^ (10 * s) * (2 : ℝ) ^ (512 * s) := by
        simpa only [dimension, Nat.cast_pow, Nat.cast_ofNat] using
          mul_le_mul_of_nonneg_right (decay_le_power s)
            (Nat.cast_nonneg (dimension s))
      _ = (2 : ℝ) ^ (522 * s) := by rw [← pow_add]; congr 1; omega
  have harg : 1 + decay s * dimension s ≤ (2 : ℝ) ^ (523 * s) := by
    calc
      1 + decay s * dimension s ≤ 2 * (decay s * dimension s) := by linarith
      _ ≤ 2 * (2 : ℝ) ^ (522 * s) := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (2 : ℝ) ^ (522 * s + 1) := by rw [pow_succ, mul_comm]
      _ ≤ (2 : ℝ) ^ (523 * s) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlog := Real.log_le_log (by positivity : 0 < 1 + decay s * dimension s) harg
  rw [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] at hlog
  have htwo : Real.log 2 < (7 : ℝ) / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hmul := mul_lt_mul_of_pos_left htwo hsR
  dsimp [decay] at hlog ⊢
  nlinarith

theorem log_short_fiber_gt {s : ℕ} (hs : 0 < s) :
    decay s / 3 < Real.log (1 + decay s * dimension s * (1 / 8 : ℝ)) := by
  have hK : (0 : ℝ) < dimension s := Nat.cast_pos.mpr (dimension_pos s)
  have hA := decay_ge_1024 hs
  have harg : (dimension s : ℝ) <
      1 + decay s * dimension s * (1 / 8 : ℝ) := by nlinarith
  have hlog := Real.log_lt_log hK harg
  rw [log_dimension] at hlog
  have htwo : (2 : ℝ) / 3 < Real.log 2 :=
    (by norm_num : (2 : ℝ) / 3 < 0.6931471803).trans Real.log_two_gt_d9
  have hmul := mul_lt_mul_of_pos_left htwo (Nat.cast_pos.mpr hs : (0 : ℝ) < s)
  dsimp [decay] at hlog ⊢
  nlinarith

end

end MaynardBFT
