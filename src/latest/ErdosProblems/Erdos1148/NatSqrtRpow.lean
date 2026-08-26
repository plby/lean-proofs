import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-! # Comparing power errors at integer square-root cutoffs -/

namespace Erdos1148.DukeArithmetic

lemma rpow_neg_le_of_le_twice {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≤ 2 * y) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    y ^ (-t) ≤ 2 * x ^ (-t) := by
  have hp : x ^ t ≤ 2 * y ^ t := by
    calc
      _ ≤ (2 * y) ^ t := Real.rpow_le_rpow hx.le hxy ht
      _ = (2 : ℝ) ^ t * y ^ t := Real.mul_rpow (by norm_num) hy.le
      _ ≤ 2 * y ^ t := mul_le_mul_of_nonneg_right
        (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ht1) (by positivity)
  rw [Real.rpow_neg hy.le, Real.rpow_neg hx.le, ← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hy _) (Real.rpow_pos_of_pos hx _)).mpr
    (by simpa only [one_mul] using hp)

lemma nat_floor_rpow_error_le {x : ℝ} (hx : 1 ≤ x) {s : ℝ}
    (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    (⌊x⌋₊ : ℝ) ^ (1 / 2 - s) ≤ 2 * x ^ (1 / 2 - s) := by
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  have hfloorR : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hfloor
  have hxy : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one x]
  rw [show 1 / 2 - s = -(s - 1 / 2) by ring]
  exact rpow_neg_le_of_le_twice (zero_lt_one.trans_le hx) (zero_lt_one.trans_le hfloorR)
    hxy (by linarith) (by linarith)

lemma nat_sqrt_rpow_error_le {X : ℕ} (hX : 0 < X) {s : ℝ}
    (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) :
    (X.sqrt : ℝ) ^ (1 - 2 * s) ≤ 2 * (X : ℝ) ^ (1 / 2 - s) := by
  have hM : 0 < X.sqrt := Nat.sqrt_pos.mpr hX
  have hM0 : (0 : ℝ) < X.sqrt := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ X.sqrt := by exact_mod_cast hM
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hupper : (X : ℝ) ≤ 4 * (X.sqrt : ℝ) ^ 2 := by
    have h := Nat.lt_succ_sqrt X
    have hR : (X : ℝ) < ((X.sqrt : ℝ) + 1) * ((X.sqrt : ℝ) + 1) := by exact_mod_cast h
    nlinarith
  have hfour : (4 : ℝ) ^ (s - 1 / 2) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (by linarith : s - 1 / 2 ≤ 1 / 2)
    norm_num [← Real.sqrt_eq_rpow] at h
    exact h
  have hp : (X : ℝ) ^ (s - 1 / 2) ≤ 2 * (X.sqrt : ℝ) ^ (2 * s - 1) := by
    calc
      _ ≤ (4 * (X.sqrt : ℝ) ^ 2) ^ (s - 1 / 2) :=
        Real.rpow_le_rpow hX0.le hupper (by linarith)
      _ = (4 : ℝ) ^ (s - 1 / 2) * ((X.sqrt : ℝ) ^ 2) ^ (s - 1 / 2) :=
        Real.mul_rpow (by norm_num) (sq_nonneg _)
      _ ≤ 2 * ((X.sqrt : ℝ) ^ 2) ^ (s - 1 / 2) :=
        mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast_mul hM0.le]
        norm_num only [Nat.cast_ofNat]
        congr 2
        ring
  rw [show 1 - 2 * s = -(2 * s - 1) by ring,
    show 1 / 2 - s = -(s - 1 / 2) by ring, Real.rpow_neg hM0.le, Real.rpow_neg hX0.le]
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hM0 _) (Real.rpow_pos_of_pos hX0 _)).mpr
    (by simpa only [one_mul] using hp)

end Erdos1148.DukeArithmetic
