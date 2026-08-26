import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # The logarithmic observation window and its exponential estimates -/

namespace Erdos1148.DukeArithmetic

noncomputable def packetObservationTime (D : ℝ) : ℕ := ⌊Real.log D / 2⌋₊

lemma packetObservationTime_le {D : ℝ} (hD : 1 ≤ D) :
    (packetObservationTime D : ℝ) ≤ Real.log D / 2 :=
  Nat.floor_le (div_nonneg (Real.log_nonneg hD) (by norm_num))

lemma log_div_two_sub_one_le_packetObservationTime (D : ℝ) :
    Real.log D / 2 - 1 ≤ (packetObservationTime D : ℝ) := by
  have h := Nat.lt_floor_add_one (Real.log D / 2)
  change Real.log D / 2 - 1 ≤ (⌊Real.log D / 2⌋₊ : ℝ)
  linarith

theorem exp_neg_packetObservationTime_le {D : ℝ} (hD : 1 ≤ D) :
    Real.exp (-(packetObservationTime D : ℝ)) ≤ Real.exp 1 * D ^ (-(1 / 2 : ℝ)) := by
  have hDpos : 0 < D := by linarith
  calc
    _ ≤ Real.exp (1 - Real.log D / 2) :=
      Real.exp_le_exp.mpr (by linarith [log_div_two_sub_one_le_packetObservationTime D])
    _ = _ := by
      rw [Real.rpow_def_of_pos hDpos, ← Real.exp_add]
      congr 1
      ring

theorem exp_mul_packetObservationTime_le {D a : ℝ} (hD : 1 ≤ D) (ha : 0 ≤ a) :
    Real.exp (a * (packetObservationTime D : ℝ)) ≤ D ^ (a / 2) := by
  have hDpos : 0 < D := by linarith
  rw [Real.rpow_def_of_pos hDpos]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (packetObservationTime_le hD) ha]

theorem packetObservationTime_pos {D : ℝ} (hD : Real.exp 2 ≤ D) : 0 < packetObservationTime D := by
  have hlog : 2 ≤ Real.log D := by
    have h := Real.log_le_log (Real.exp_pos 2) hD
    simpa only [Real.log_exp] using h
  have hfloor : 1 ≤ ⌊Real.log D / 2⌋₊ := Nat.le_floor (by norm_num; linarith)
  exact hfloor

theorem power_height_eleven_bound {D β : ℝ} (hD : 1 ≤ D) (hβ : 0 ≤ β) :
    (D ^ β + 1) ^ 11 ≤ 2 ^ 11 * D ^ (11 * β) := by
  have hDpos : 0 < D := by linarith
  have hheight : 1 ≤ D ^ β := Real.one_le_rpow hD hβ
  calc
    _ ≤ (2 * D ^ β) ^ 11 := pow_le_pow_left₀ (by positivity) (by linarith) 11
    _ = 2 ^ 11 * D ^ (β * 11) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hDpos.le]
      norm_num
    _ = _ := by rw [mul_comm β 11]

end Erdos1148.DukeArithmetic
