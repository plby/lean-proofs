import ErdosProblems.Erdos745.MeanBounds

/-!
# The critical binomial path-height recurrence

These are finite analytic inequalities, uniform in the graph order.
-/

namespace Erdos745

noncomputable section

/-- Survival-height upper bound for an `n`-ary Bernoulli branching tree. -/
def pathHeightBound (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | h + 1 => 1 - (1 - pathHeightBound n h / n) ^ n

theorem pathHeightBound_mem {n : ℕ} (hn : 2 ≤ n) (h : ℕ) :
    0 ≤ pathHeightBound n h ∧ pathHeightBound n h ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  induction h with
  | zero => simp [pathHeightBound]
  | succ h ih =>
    have hdiv : pathHeightBound n h / n ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact ih.2.trans hnR
    have hbase : 0 ≤ 1 - pathHeightBound n h / n := sub_nonneg.mpr hdiv
    have hbase1 : 1 - pathHeightBound n h / n ≤ 1 := by
      have hnonneg := div_nonneg ih.1 (show (0 : ℝ) ≤ n by positivity)
      linarith
    have hp := pow_le_one₀ hbase hbase1 (n := n)
    have hp0 := pow_nonneg hbase n
    rw [pathHeightBound]
    constructor <;> linarith

theorem one_sub_pow_second_lower (m : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - ((m : ℝ) + 2) * x + (((m : ℝ) + 2) * ((m : ℝ) + 1) / 2) *
      x ^ 2 * (1 - x) ^ m ≤ (1 - x) ^ (m + 2) := by
  have hq : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hq1 : 1 - x ≤ 1 := by linarith
  induction m with
  | zero => norm_num; nlinarith
  | succ m ih =>
    have hA := mul_le_mul_of_nonneg_left ih hq
    have hB := mul_le_mul_of_nonneg_left (pow_le_one₀ hq hq1 (n := m + 1))
      (show 0 ≤ ((m : ℝ) + 2) * x ^ 2 by positivity)
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ] at hA hB ⊢
    linear_combination hA + hB

theorem one_sub_pow_second_lower' {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (n : ℝ) * x + ((n : ℝ) * ((n : ℝ) - 1) / 2) *
      x ^ 2 * (1 - x) ^ (n - 2) ≤ (1 - x) ^ n := by
  have h := one_sub_pow_second_lower (n - 2) hx hx1
  rw [Nat.sub_add_cancel hn, Nat.cast_sub hn, Nat.cast_ofNat] at h
  convert h using 1 <;> ring

theorem critical_absence_power_uniform {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (-2) ≤ (1 - 1 / (n : ℝ)) ^ (n - 2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hb : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
  have hdiv : ((n - 2 : ℕ) : ℝ) / n ≤ 1 := (div_le_one (by positivity)).mpr hb
  have hdiv2 : ((n - 2 : ℕ) : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 := by
    calc
      _ ≤ (n : ℝ) / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right hb (sq_nonneg _)
      _ = 1 / (n : ℝ) := by field_simp
      _ ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  calc
    _ ≤ Real.exp (-((n - 2 : ℕ) : ℝ) / n - 2 * ((n - 2 : ℕ) : ℝ) / (n : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      linear_combination hdiv + 2 * hdiv2
    _ ≤ _ := critical_absence_power_lower hn (n - 2)

/-- A fixed positive quadratic loss in the critical height recursion. -/
def pathHeightDecay : ℝ := Real.exp (-2) / 4

theorem pathHeightDecay_pos : 0 < pathHeightDecay := by unfold pathHeightDecay; positivity

theorem pathHeightDecay_le_one : pathHeightDecay ≤ 1 := by
  have h : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  unfold pathHeightDecay
  linarith

theorem critical_binomial_quadratic {n : ℕ} (hn : 2 ≤ n) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    1 - (1 - r / n) ^ n ≤ r - pathHeightDecay * r ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hx : 0 ≤ r / n := div_nonneg hr (by positivity)
  have hx1 : r / n ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  let C := ((n : ℝ) - 1) / (2 * n)
  have hC : 1 / 4 ≤ C := by
    dsimp [C]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hpow : Real.exp (-2) ≤ (1 - r / n) ^ (n - 2) := by
    apply (critical_absence_power_uniform hn).trans
    apply pow_le_pow_left₀
    · have h : (1 : ℝ) / n ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      linarith
    · exact sub_le_sub_left (div_le_div_of_nonneg_right hr1 (by positivity)) 1
  have hcorr : pathHeightDecay * r ^ 2 ≤ C * r ^ 2 * (1 - r / n) ^ (n - 2) := by
    have hmul := mul_le_mul (mul_le_mul_of_nonneg_right hC (sq_nonneg r)) hpow
      (Real.exp_pos _).le (mul_nonneg (by linarith : 0 ≤ C) (sq_nonneg r))
    unfold pathHeightDecay
    linear_combination hmul
  have hbin := one_sub_pow_second_lower' hn hx hx1
  have heq : 1 - (n : ℝ) * (r / n) + ((n : ℝ) * ((n : ℝ) - 1) / 2) *
      (r / n) ^ 2 * (1 - r / n) ^ (n - 2) =
      1 - r + C * r ^ 2 * (1 - r / n) ^ (n - 2) := by
    dsimp [C]
    field_simp
  rw [heq] at hbin
  linarith

theorem pathHeightBound_quadratic {n : ℕ} (hn : 2 ≤ n) (h : ℕ) :
    pathHeightBound n (h + 1) ≤ pathHeightBound n h - pathHeightDecay * pathHeightBound n h ^ 2 :=
  critical_binomial_quadratic hn (pathHeightBound_mem hn h).1 (pathHeightBound_mem hn h).2

theorem pathHeightBound_le_reciprocal {n : ℕ} (hn : 2 ≤ n) (h : ℕ) :
    pathHeightBound n h ≤ 1 / (1 + pathHeightDecay * h) := by
  have ha := pathHeightDecay_pos
  induction h with
  | zero => simp [pathHeightBound]
  | succ h ih =>
    let q := pathHeightBound n h
    let r := pathHeightBound n (h + 1)
    have hq : 0 ≤ q := (pathHeightBound_mem hn h).1
    have hr : 0 ≤ r := (pathHeightBound_mem hn (h + 1)).1
    have hqr : r ≤ q - pathHeightDecay * q ^ 2 := pathHeightBound_quadratic hn h
    have hrq : r ≤ q := by nlinarith [mul_nonneg ha.le (sq_nonneg q)]
    have hden : 0 < 1 + pathHeightDecay * (h : ℝ) := by positivity
    by_cases hr0 : r = 0
    · change r ≤ _
      rw [hr0]
      positivity
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hqpos : 0 < q := hrpos.trans_le hrq
      have hinv : 1 / q + pathHeightDecay ≤ 1 / r := by
        apply (le_div_iff₀ hrpos).mpr
        apply (mul_le_mul_iff_left₀ hqpos).mp
        have hcancel : ((1 / q + pathHeightDecay) * r) * q =
            r + pathHeightDecay * r * q := by field_simp
        rw [hcancel, one_mul]
        have hprod := mul_le_mul_of_nonneg_left hrq
          (mul_nonneg ha.le hq)
        nlinarith
      have hprev : 1 + pathHeightDecay * (h : ℝ) ≤ 1 / q := by
        apply (le_div_iff₀ hqpos).mpr
        have hi := (le_div_iff₀ hden).mp ih
        change q * (1 + pathHeightDecay * (h : ℝ)) ≤ 1 at hi
        simpa only [mul_comm] using hi
      change r ≤ _
      apply (le_div_iff₀ (by positivity : 0 < 1 + pathHeightDecay * ((h + 1 : ℕ) : ℝ))).mpr
      have hstep : 1 + pathHeightDecay * ((h + 1 : ℕ) : ℝ) ≤ 1 / r := by
        push_cast
        linarith
      have := (le_div_iff₀ hrpos).mp hstep
      simpa only [mul_comm] using this

/-- Uniform inverse-height decay, with an explicit absolute constant. -/
theorem pathHeightBound_le {n : ℕ} (hn : 2 ≤ n) (h : ℕ) :
    pathHeightBound n h ≤ (1 / pathHeightDecay) / ((h : ℝ) + 1) := by
  apply (pathHeightBound_le_reciprocal hn h).trans
  have ha := pathHeightDecay_pos
  have ha1 := pathHeightDecay_le_one
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

end

end Erdos745
