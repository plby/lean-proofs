import ErdosProblems.Erdos19.GraphOutliers

/-! # Numerical margins for handling a small exceptional set -/

namespace Erdos19

theorem outlier_quota_div_bound (x m : ℕ) : 8 * ((x * m) / (8 * x + 1)) ≤ m := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hx
    have hdiv := Nat.mul_div_le (x * m) (8 * x + 1)
    have hmul : x * (8 * ((x * m) / (8 * x + 1))) ≤ x * m := by
      nlinarith only [hdiv]
    exact Nat.le_of_mul_le_mul_left hmul hxpos

theorem outlier_integer_margins (n s x t m : ℕ) (hs : 100 ≤ s) (hn : 100 ≤ n)
    (hx : x ≤ n / s) (ht : n ≤ 8 * t) (hm : 100 * m ≤ 52 * t)
    (hmn : 4 * m ≤ 3 * n) :
    m < n ∧ 8 * m ≤ 7 * (n - x) ∧ m + n / s + 2 * x ≤ t ∧
      2 * x + n / s + (x * m) / (8 * x + 1) < n - m - 1 := by
  have hscale : 100 * (n / s) ≤ n :=
    (Nat.mul_le_mul_right _ hs).trans (Nat.mul_div_le n s)
  have hxn : x ≤ n := by omega
  have hsplit : n - x + x = n := Nat.sub_add_cancel hxn
  have hm_lt : m < n := by omega
  have hD : n - m - 1 + m + 1 = n := by omega
  have hquota := outlier_quota_div_bound x m
  refine ⟨hm_lt, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

theorem outlier_real_margins (delta : ℝ) (hd : 0 < delta) (n s x : ℕ)
    (hs : 100 ≤ s) (hn : s ≤ n) (hx : x ≤ n / s) (hds : 100 ≤ delta * s) :
    ((n / s + x + 1 : ℕ) : ℝ) ≤ delta * (n - x) ∧
      ((n / s + (8 * x + 1) + 1 : ℕ) : ℝ) ≤ delta * (n - x) := by
  have hspos : 0 < s := by omega
  have ha : 1 ≤ n / s := (Nat.le_div_iff_mul_le hspos).mpr (by simpa using hn)
  have hprod := Nat.mul_div_le n s
  have hxn : x ≤ n := hx.trans (Nat.div_le_self n s)
  have hsplit : n - x + x = n := Nat.sub_add_cancel hxn
  have hsm : s = (s - 1) + 1 := by omega
  have hba : (s - 1) * (n / s) ≤ n - x := by nlinarith only [hprod, hsplit, hx, hsm]
  have hbaR : ((s : ℝ) - 1) * (n / s : ℕ) ≤ (n - x : ℕ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hba
    simpa only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ s by omega), Nat.cast_one] using h
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast (show 2 ≤ s by omega)
  have hfactor : (50 : ℝ) ≤ delta * ((s : ℝ) - 1) := by
    have h := mul_nonneg hd.le (sub_nonneg.mpr hsR)
    nlinarith only [h, hds]
  have hmul := mul_le_mul_of_nonneg_left hbaR hd.le
  rw [Nat.cast_sub hxn] at hmul
  have hmul' := mul_le_mul_of_nonneg_right hfactor (show (0 : ℝ) ≤ (n / s : ℕ) by positivity)
  have hxR : (x : ℝ) ≤ (n / s : ℕ) := by exact_mod_cast hx
  have haR : (1 : ℝ) ≤ (n / s : ℕ) := by exact_mod_cast ha
  constructor <;> push_cast <;> nlinarith only [hmul, hmul', hxR, haR]

#print axioms outlier_integer_margins
#print axioms outlier_real_margins

end Erdos19
