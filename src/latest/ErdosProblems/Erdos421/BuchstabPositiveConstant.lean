import ErdosProblems.Erdos421.BuchstabNumericBounds

/-! # A positive Buchstab coefficient at the intermediate exponent 39/200

This verifies the numerical coefficient in the two-term minorant. The
asymptotic connection with actual long rough-number windows is a separate
remaining obligation. The integral expression is the one in Section 4 of
Watt, Acta Arithmetica 72 (1995), after the change of prime-scale variable.
-/

namespace Erdos421

open MeasureTheory

noncomputable def buchstabMinorantCoefficient : ℝ :=
  (200 / 39 : ℝ) * (finiteBuchstab 4 (200 / 39) -
    ∫ t in (39 / 200 : ℝ)..(1 / 2 : ℝ), finiteBuchstab 4 ((1 - t) / (39 / 200)) / t)

theorem buchstab_cofactor_integral_upper :
    (∫ t in (39 / 200 : ℝ)..(1 / 2 : ℝ), finiteBuchstab 4 ((1 - t) / (39 / 200)) / t) ≤
      (23 / 40 : ℝ) * Real.log (100 / 39) := by
  have hab : (39 / 200 : ℝ) ≤ 1 / 2 := by norm_num
  have hne : ∀ t ∈ Set.Icc (39 / 200 : ℝ) (1 / 2), t ≠ 0 := by
    intro t ht
    linarith [ht.1]
  have hc : Continuous (fun t : ℝ ↦ finiteBuchstab 4 ((1 - t) / (39 / 200))) :=
    (finiteBuchstab_continuous 4).comp
      ((continuous_const.sub continuous_id).div_const (39 / 200))
  have hf : ContinuousOn (fun t : ℝ ↦ finiteBuchstab 4 ((1 - t) / (39 / 200)) / t)
      (Set.Icc (39 / 200 : ℝ) (1 / 2)) := hc.continuousOn.div continuousOn_id hne
  have hg : ContinuousOn (fun t : ℝ ↦ (23 / 40 : ℝ) / t)
      (Set.Icc (39 / 200 : ℝ) (1 / 2)) := continuousOn_const.div continuousOn_id hne
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    (ContinuousOn.intervalIntegrable_of_Icc hab hf)
    (ContinuousOn.intervalIntegrable_of_Icc hab hg) (by
      intro t ht
      apply div_le_div_of_nonneg_right _ (by linarith [ht.1])
      apply finiteBuchstab_upper 4
      norm_num
      linarith [ht.2])
  apply hm.trans_eq
  calc
    _ = ∫ t in (39 / 200 : ℝ)..(1 / 2 : ℝ), (23 / 40 : ℝ) * (1 / t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        integral_one_div_of_pos (by norm_num : (0 : ℝ) < 39 / 200)
          (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num

theorem buchstabMinorantCoefficient_lower : (1 / 52 : ℝ) ≤ buchstabMinorantCoefficient := by
  have hl := finiteBuchstab_lower 3 (u := 200 / 39) (by norm_num [Set.mem_Icc])
  have hu := buchstab_cofactor_integral_upper
  have hlog := log_hundred_over_thirty_nine_le
  unfold buchstabMinorantCoefficient
  nlinarith

theorem buchstabMinorantCoefficient_pos : 0 < buchstabMinorantCoefficient :=
  (by norm_num : (0 : ℝ) < 1 / 52).trans_le buchstabMinorantCoefficient_lower

end Erdos421
