/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSmoothParameters
import ErdosProblems.Erdos4b.FGKMTSourceScales
import ErdosProblems.Erdos4b.SmoothParameters

/-! # The complete smooth exception is negligible on the full eventual source ray -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem exists_source_smooth_count_log_bound :
    ∃ a : ℝ, 2 ≤ a ∧ ∀ c : ℝ, 0 < c → ∀ᶠ x : ℕ in atTop,
      ((Nat.smoothNumbersUpTo ⌊sourceIntervalLength c x⌋₊
        (⌊sourceSmallPrimeUpper a x⌋₊ + 1)).card : ℝ) ≤
          (x : ℝ) / Real.log (x : ℝ) ^ 8 := by
  obtain ⟨C, hC, hcheb⟩ :=
    Erdos387.PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  let B := smoothEulerLogConstant C
  have hB : 0 < B := smoothEulerLogConstant_pos hC
  let a := 2 * (B + 10) + 5
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have haB : B + 10 ≤ a / 2 := by dsimp [a]; linarith
  refine ⟨a, ha, ?_⟩
  intro c hc
  filter_upwards [eventually_sourceSmoothDelta_ranges ha,
    eventually_sourceIntervalLength_bounds hc, eventually_ge_atTop (2 : ℕ)] with x hr hy hx
  obtain ⟨hL, hℓ, hδ, hδhalf, hinv, hZ, hZpow⟩ := hr
  let L := Real.log (x : ℝ)
  let ℓ := Real.log L
  let δ := sourceSmoothDelta a x
  let Y := ⌊sourceIntervalLength c x⌋₊
  let Z := ⌊sourceSmallPrimeUpper a x⌋₊
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hLpos : 0 < L := by change 0 < Real.log (x : ℝ); linarith
  have hy0 : 0 ≤ sourceIntervalLength c x := hxpos.le.trans hy.1
  have hxY : x ≤ Y := (Nat.le_floor_iff hy0).mpr hy.1
  have hY : 0 < Y := (show 0 < x by omega).trans_le hxY
  have hYle : (Y : ℝ) ≤ (x : ℝ) * L ^ 2 := (Nat.floor_le hy0).trans hy.2.1
  have hEuler : Erdos469.smoothRankinEulerProduct δ Z ≤ Real.exp (B * ℓ) :=
    smoothRankinEulerProduct_le_exp_loglog hC hcheb hL hℓ hδ hδhalf hinv hZ hZpow
  have hcount := (Erdos469.card_smoothNumbersUpTo_rankin_le hY hδ
    (hδhalf.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))).trans
      (mul_le_mul_of_nonneg_left hEuler (Real.rpow_nonneg (Nat.cast_nonneg Y) (1 - δ)))
  have hlogY : L ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hxpos (by exact_mod_cast hxY)
  have hsave : (a / 2) * ℓ ≤ δ * Real.log (Y : ℝ) := by
    rw [← sourceSmoothDelta_mul_log hLpos.ne']
    exact mul_le_mul_of_nonneg_left hlogY hδ.le
  have hexponent : -δ * Real.log (Y : ℝ) + B * ℓ ≤ -10 * ℓ := by
    have hℓ0 : 0 ≤ ℓ := le_trans (by norm_num : (0 : ℝ) ≤ 1) hℓ
    nlinarith [mul_le_mul_of_nonneg_right haB hℓ0]
  rw [SmoothParameters.rpow_one_sub_eq_mul_exp_neg hY, mul_assoc, ← Real.exp_add] at hcount
  calc
    _ ≤ (Y : ℝ) * Real.exp (-δ * Real.log (Y : ℝ) + B * ℓ) := hcount
    _ ≤ (Y : ℝ) * Real.exp (-10 * ℓ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (Nat.cast_nonneg Y)
    _ = (Y : ℝ) / L ^ 10 := by
      rw [show -10 * ℓ = -Real.log (L ^ 10) by rw [Real.log_pow]; norm_num; rfl,
        Real.exp_neg, Real.exp_log (pow_pos hLpos 10), div_eq_mul_inv]
    _ ≤ ((x : ℝ) * L ^ 2) / L ^ 10 := div_le_div_of_nonneg_right hYle (by positivity)
    _ = (x : ℝ) / L ^ 8 := by field_simp

theorem exists_source_smooth_count_budget :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℝ, 0 < c → ∀ᶠ x : ℕ in atTop,
      ((Nat.smoothNumbersUpTo ⌊sourceIntervalLength c x⌋₊
        (⌊sourceSmallPrimeUpper a x⌋₊ + 1)).card : ℝ) ≤
          (x : ℝ) / Real.log (x : ℝ) := by
  obtain ⟨a, ha, hcount⟩ := exists_source_smooth_count_log_bound
  refine ⟨a, by linarith, ?_⟩
  intro c hc
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hcount c hc, hlog.eventually_ge_atTop 1] with x hx hL
  change 1 ≤ Real.log (x : ℝ) at hL
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  apply hx.trans
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg x) hLpos
  exact le_self_pow₀ hL (by norm_num : (8 : ℕ) ≠ 0)

end

end Erdos4b.FGKMT
