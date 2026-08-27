import ErdosProblems.Erdos4.FGKMTGrowingSmoothParameters
import ErdosProblems.Erdos4.FGKMTGrowingGapLength
import ErdosProblems.Erdos4.SmoothParameters

/-! All smooth integers, uniformly at every sufficiently large FGKMT endpoint. -/

namespace Erdos4.FGKMT

open Filter

theorem eventually_growing_smooth_bound {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      ((Nat.smoothNumbersUpTo (growingGapLength c x) (growingRandomEnd x + 1)).card : ℝ) ≤
        (x : ℝ) / Real.log (x : ℝ) ^ 2 := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growing_rankin_parameters, eventually_growing_rankin_euler,
    eventually_growing_gap_length_bounds hc, eventually_growing_outer_log_budget,
    hlog.eventually (eventually_ge_atTop c), eventually_ge_atTop 2]
    with x hpar hEuler hlength hlogs hcL hx
  let Y := growingGapLength c x
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let δ := growingRankinDelta x
  obtain ⟨hY, hXY, _, _, _, _, hYupper⟩ := hlength
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hYposNat : 0 < Y := hY
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hYposNat
  have hL1 : 1 ≤ L := hlogs.1
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hδpos : 0 < δ := hpar.1
  have hδone : δ < 1 := hpar.2.1.trans_lt (by norm_num)
  have hlogY : L ≤ Real.log (Y : ℝ) := Real.log_le_log hxpos (by exact_mod_cast hXY)
  have hsave : 20 * l ≤ δ * Real.log (Y : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlogY hδpos.le
    have heq : δ * L = 20 * l := hpar.2.2.1
    rwa [heq] at hh
  have hEuler' : Erdos469.smoothRankinEulerProduct δ (growingRandomEnd x) ≤ Real.exp (10 * l) :=
    hEuler
  have hYbound : (Y : ℝ) ≤ (x : ℝ) * L ^ 2 := by
    change c ≤ L at hcL
    have hscale : growingOuterScale x ≤ L := hlogs.2.2.2.2
    calc
      _ ≤ c * x * growingOuterScale x := hYupper
      _ ≤ c * x * L := mul_le_mul_of_nonneg_left hscale (mul_nonneg hc.le hxpos.le)
      _ ≤ L * x * L := by gcongr
      _ = _ := by ring
  have hlogpow : Real.log (L ^ 10) = 10 * l := by simp [Real.log_pow, l]
  have hexp : Real.exp (-(10 * l)) = (L ^ 10)⁻¹ := by
    rw [← hlogpow, Real.exp_neg, Real.exp_log (pow_pos hLpos 10)]
  have hRankin := Erdos469.card_smoothNumbersUpTo_rankin_le
    (y := growingRandomEnd x) hYposNat hδpos hδone
  calc
    _ ≤ (Y : ℝ) ^ (1 - δ) * Erdos469.smoothRankinEulerProduct δ (growingRandomEnd x) := hRankin
    _ ≤ (Y : ℝ) ^ (1 - δ) * Real.exp (10 * l) :=
      mul_le_mul_of_nonneg_left hEuler' (Real.rpow_nonneg hYpos.le _)
    _ = (Y : ℝ) * Real.exp (10 * l - δ * Real.log (Y : ℝ)) := by
      rw [SmoothParameters.rpow_one_sub_eq_mul_exp_neg hYposNat δ, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (Y : ℝ) * Real.exp (-(10 * l)) := by
      apply mul_le_mul_of_nonneg_left _ hYpos.le
      exact Real.exp_le_exp.mpr (by linarith)
    _ = (Y : ℝ) / L ^ 10 := by rw [hexp, div_eq_mul_inv]
    _ ≤ ((x : ℝ) * L ^ 2) / L ^ 10 := div_le_div_of_nonneg_right hYbound (pow_nonneg hLpos.le _)
    _ = (x : ℝ) / L ^ 8 := by field_simp [hLpos.ne'] <;> ring
    _ ≤ (x : ℝ) / L ^ 2 := div_le_div_of_nonneg_left hxpos.le (pow_pos hLpos 2)
      (pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 8))

end Erdos4.FGKMT
