import ErdosProblems.Erdos49.ScaleBounds

/-!
# Real-variable decay estimates

Only three elementary domination statements are needed in the final
bookkeeping.  They are kept separate so all later number-theoretic estimates
reduce to algebraic substitutions.
-/

open Filter Set Topology

namespace Erdos49

noncomputable section

lemma tendsto_pow_mul_exp_neg_scaled (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ ↦ t ^ k * Real.exp (-a * t)) atTop (nhds 0) := by
  simpa [Real.rpow_natCast] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) a ha

lemma tendsto_quartic_scaled_decay :
    Tendsto (fun t : ℝ ↦ (4 * t ^ 4 + 21 * t) * Real.exp (-t / 20))
      atTop (nhds 0) := by
  have h4 := (tendsto_pow_mul_exp_neg_scaled 4 (by norm_num : (0 : ℝ) < 1 / 20)).const_mul 4
  have h1 := (tendsto_pow_mul_exp_neg_scaled 1 (by norm_num : (0 : ℝ) < 1 / 20)).const_mul 21
  convert h4.add h1 using 1 <;> norm_num <;> ring

/-- The medium-PNT decay beats the full primary-cell exponential. -/
lemma eventually_medium_cell_decay {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ t : ℝ in atTop,
      C * Real.exp (4 * t ^ 4 + 21 * t - c * Real.exp (t / 20)) ≤ 1 := by
  have hsmall : ∀ᶠ t : ℝ in atTop,
      (4 * t ^ 4 + 21 * t) * Real.exp (-t / 20) ≤ c / 2 := by
    have hlim := tendsto_quartic_scaled_decay
    have hnorm := NormedAddGroup.tendsto_nhds_zero.mp hlim (c / 2) (by positivity)
    filter_upwards [hnorm, eventually_ge_atTop 0] with t ht htnonneg
    rw [Real.norm_of_nonneg] at ht
    · exact ht.le
    · exact mul_nonneg (by positivity) (Real.exp_pos _).le
  have hmain : ∀ᶠ t : ℝ in atTop,
      4 * t ^ 4 + 21 * t ≤ (c / 2) * Real.exp (t / 20) := by
    filter_upwards [hsmall] with t ht
    have he : 0 < Real.exp (t / 20) := Real.exp_pos _
    have := mul_le_mul_of_nonneg_right ht he.le
    have hcancel : Real.exp (-t / 20) * Real.exp (t / 20) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    calc
      4 * t ^ 4 + 21 * t =
          (4 * t ^ 4 + 21 * t) *
            (Real.exp (-t / 20) * Real.exp (t / 20)) := by rw [hcancel, mul_one]
      _ = ((4 * t ^ 4 + 21 * t) * Real.exp (-t / 20)) *
            Real.exp (t / 20) := by ring
      _ ≤ (c / 2) * Real.exp (t / 20) := this
  have htower : Tendsto (fun t : ℝ ↦ (c / 2) * Real.exp (t / 20)) atTop atTop := by
    have he : Tendsto (fun t : ℝ ↦ Real.exp (t / 20)) atTop atTop := by
      exact Real.tendsto_exp_atTop.comp
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 20))
    exact he.const_mul_atTop (by positivity)
  have hzero : Tendsto (fun t : ℝ ↦ C * Real.exp
      (-(c / 2 * Real.exp (t / 20)))) atTop (nhds 0) :=
    by simpa only [Function.comp_apply, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp htower).const_mul C
  have hsmall2 : ∀ᶠ t : ℝ in atTop,
      C * Real.exp (-(c / 2 * Real.exp (t / 20))) ≤ 1 := by
    have hnorm := NormedAddGroup.tendsto_nhds_zero.mp hzero 1 (by norm_num)
    filter_upwards [hnorm] with t ht
    rw [Real.norm_of_nonneg] at ht
    · exact ht.le
    · positivity
  filter_upwards [hmain, hsmall2] with t hpoly hdecay
  calc
    C * Real.exp (4 * t ^ 4 + 21 * t - c * Real.exp (t / 20)) ≤
        C * Real.exp (-(c / 2 * Real.exp (t / 20))) := by
      gcongr
      nlinarith
    _ ≤ 1 := hdecay

/-- The square-root correction in `psi - theta` beats the primary-cell
exponential. -/
lemma eventually_sqrt_cell_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ t : ℝ in atTop,
      C * Real.exp (4 * t ^ 4 + 23 * t - Real.exp t / 2) ≤ 1 := by
  have hpolyLim : Tendsto
      (fun t : ℝ ↦ (4 * t ^ 4 + 23 * t) * Real.exp (-t))
      atTop (nhds 0) := by
    have h4 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul 4
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 23
    convert h4.add h1 using 1 <;> norm_num <;> ring
  have hmain : ∀ᶠ t : ℝ in atTop,
      4 * t ^ 4 + 23 * t ≤ Real.exp t / 4 := by
    have hnorm := NormedAddGroup.tendsto_nhds_zero.mp hpolyLim (1 / 4) (by norm_num)
    filter_upwards [hnorm, eventually_ge_atTop 0] with t ht ht0
    rw [Real.norm_of_nonneg] at ht
    · have hm := mul_le_mul_of_nonneg_right ht.le (Real.exp_pos t).le
      have hcancel : Real.exp (-t) * Real.exp t = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> ring
      calc
        4 * t ^ 4 + 23 * t =
            (4 * t ^ 4 + 23 * t) * (Real.exp (-t) * Real.exp t) := by
          rw [hcancel, mul_one]
        _ = ((4 * t ^ 4 + 23 * t) * Real.exp (-t)) * Real.exp t := by ring
        _ ≤ (1 / 4) * Real.exp t := hm
        _ = Real.exp t / 4 := by ring
    · exact mul_nonneg (by positivity) (Real.exp_pos _).le
  have htower : Tendsto (fun t : ℝ ↦ Real.exp t / 4) atTop atTop := by
    exact Real.tendsto_exp_atTop.atTop_div_const (by norm_num)
  have hzero : Tendsto (fun t : ℝ ↦ C * Real.exp (-(Real.exp t / 4)))
      atTop (nhds 0) :=
    by simpa only [Function.comp_apply, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp htower).const_mul C
  have hsmall : ∀ᶠ t : ℝ in atTop,
      C * Real.exp (-(Real.exp t / 4)) ≤ 1 := by
    have hn := NormedAddGroup.tendsto_nhds_zero.mp hzero 1 (by norm_num)
    filter_upwards [hn] with t ht
    rw [Real.norm_of_nonneg] at ht
    · exact ht.le
    · positivity
  filter_upwards [hmain, hsmall] with t hp hs
  calc
    C * Real.exp (4 * t ^ 4 + 23 * t - Real.exp t / 2) ≤
        C * Real.exp (-(Real.exp t / 4)) := by
      gcongr
      nlinarith
    _ ≤ 1 := hs

/-- The Rankin tail `exp (-t^3/42)` beats the two powers of `log N`
required in Tao's error term. -/
lemma eventually_cubic_tail_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ t : ℝ in atTop,
      C * t ^ 3 * Real.exp (2 * t - t ^ 3 / 42) ≤ 1 := by
  have hsmall := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul C
  have hone : ∀ᶠ t : ℝ in atTop, C * (t ^ 3 * Real.exp (-t)) ≤ 1 := by
    have hsmall' : Tendsto (fun t : ℝ ↦ C * (t ^ 3 * Real.exp (-t)))
        atTop (nhds 0) := by simpa using hsmall
    have hn := NormedAddGroup.tendsto_nhds_zero.mp hsmall' 1 (by norm_num)
    filter_upwards [hn, eventually_ge_atTop 0] with t ht ht0
    rw [Real.norm_of_nonneg] at ht
    · exact ht.le
    · positivity
  filter_upwards [hone, eventually_ge_atTop 12] with t hone ht
  have hexp : Real.exp (2 * t - t ^ 3 / 42) ≤ Real.exp (-t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (t - 12)]
  calc
    C * t ^ 3 * Real.exp (2 * t - t ^ 3 / 42) ≤
        C * t ^ 3 * Real.exp (-t) := by gcongr
    _ = C * (t ^ 3 * Real.exp (-t)) := by ring
    _ ≤ 1 := hone

end

end Erdos49
