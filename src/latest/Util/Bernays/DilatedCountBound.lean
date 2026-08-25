import Util.Bernays.LogCountBound

/-!
# A summable majorant for all fixed-factor counting slices
-/

namespace Bernays

theorem sqrt_log_mul_bound {m k x : ℝ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hx : 0 < x) (hupper : x ≤ 2 * m * k) :
    Real.sqrt (Real.log x) ≤ 2 * Real.sqrt m * (1 + Real.sqrt (Real.log k)) := by
  have hm₀ : 0 < m := zero_lt_one.trans_le hm
  have hk₀ : 0 < k := zero_lt_one.trans_le hk
  have hlog := Real.log_le_log hx hupper
  rw [Real.log_mul (mul_pos (by norm_num) hm₀).ne' hk₀.ne',
    Real.log_mul (by norm_num) hm₀.ne'] at hlog
  have hlogtwo : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hlogm := Real.log_le_self hm₀.le
  have hlogk := Real.log_nonneg hk
  have hsm := Real.sq_sqrt hm₀.le
  have hsk := Real.sq_sqrt hlogk
  have hsm₁ : 1 ≤ Real.sqrt m := (Real.le_sqrt (by norm_num) hm₀.le).mpr (by simpa using hm)
  have hsum : Real.sqrt (Real.log x) ≤ 1 + Real.sqrt m + Real.sqrt (Real.log k) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sqrt_nonneg m, Real.sqrt_nonneg (Real.log k)]
  apply hsum.trans
  have hprod := mul_nonneg (sub_nonneg.mpr hsm₁) (Real.sqrt_nonneg (Real.log k))
  nlinarith [Real.sqrt_nonneg (Real.log k)]

theorem count_dilation_scale_bound {A : ℕ → ℝ} (hA₀ : A 0 = 0) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ N : ℕ, A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))))
    {m : ℕ} (hm : 0 < m) (N : ℕ) :
    A (N / m) / scale N ≤ 2 * C / Real.sqrt (m : ℝ) := by
  by_cases hN : N < 2
  · interval_cases N <;> simp only [scale, Nat.cast_zero, Nat.cast_one, Real.log_zero,
      Real.log_one, Real.sqrt_zero, div_zero] <;> positivity
  by_cases hk : N / m = 0
  · rw [hk, hA₀, zero_div]
    positivity
  let k := N / m
  have hk₀ : 0 < k := Nat.pos_of_ne_zero hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk₀
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hmk : (m : ℝ) * k ≤ N := by exact_mod_cast Nat.mul_div_le N m
  have hNk : (N : ℝ) ≤ 2 * m * k := by
    have h := Nat.lt_mul_div_succ N hm
    have h' : N < m * (k + 1) := h
    have h'' : N ≤ 2 * m * k := by nlinarith
    exact_mod_cast h''
  have hlog := sqrt_log_mul_bound (show (1 : ℝ) ≤ m by exact_mod_cast hm)
    (show (1 : ℝ) ≤ k by exact_mod_cast hk₀) (zero_lt_one.trans hNR) hNk
  have hden : 0 < 1 + Real.sqrt (Real.log (k : ℝ)) := by positivity
  have hslog : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hmain : A k * Real.sqrt (Real.log (N : ℝ)) / N ≤
      (C * k / (1 + Real.sqrt (Real.log (k : ℝ)))) * Real.sqrt (Real.log (N : ℝ)) /
        ((m : ℝ) * k) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hcount k) hslog)
      (Nat.cast_nonneg N)).trans
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hmR hkR) hmk
  have hcancel : (C * k / (1 + Real.sqrt (Real.log (k : ℝ)))) * Real.sqrt (Real.log (N : ℝ)) /
      ((m : ℝ) * k) = C * Real.sqrt (Real.log (N : ℝ)) /
        ((m : ℝ) * (1 + Real.sqrt (Real.log (k : ℝ)))) := by field_simp
  rw [hcancel] at hmain
  have hbound : C * Real.sqrt (Real.log (N : ℝ)) /
      ((m : ℝ) * (1 + Real.sqrt (Real.log (k : ℝ)))) ≤ 2 * C / Real.sqrt (m : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlog hC
    apply (div_le_iff₀ (mul_pos hmR hden)).mpr
    have hid : (2 * C / Real.sqrt (m : ℝ)) *
        ((m : ℝ) * (1 + Real.sqrt (Real.log (k : ℝ)))) =
        C * (2 * Real.sqrt (m : ℝ) * (1 + Real.sqrt (Real.log (k : ℝ)))) := by
      have hsquare := Real.sq_sqrt hmR.le
      field_simp
      nlinarith
    rw [hid]
    exact hmul
  have heq : A (N / m) / scale N = A k * Real.sqrt (Real.log (N : ℝ)) / N := by
    dsimp only [scale, k]
    rw [div_div_eq_mul_div]
  rw [heq]
  exact hmain.trans hbound

end Bernays
