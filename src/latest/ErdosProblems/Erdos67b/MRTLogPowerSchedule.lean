import ErdosProblems.Erdos67b.MRTLogPowerParameters

/-! # Eventual feasibility of the logarithmic MRT schedule -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrtEventually_logPower_geometry :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧ 1 ≤ Real.log L ∧
      L / 2 ≤ mrtLogPowerUpper L ∧ mrtLogPowerUpper L ≤ L ∧
      2 ≤ mrtLogPowerLower L ∧ 2 * mrtLogPowerLower L ≤ mrtLogPowerUpper L ∧
      Real.exp 1 ≤ mrtLogPowerUpper L ∧ 1 ≤ Real.log (mrtLogPowerUpper L) ∧
      4096 * Real.log (mrtLogPowerUpper L) ≤ (1 / 12) * mrtLogPowerLower L := by
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [eventually_ge_atTop (2 * Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000000))]
    with L hL hlog hsmall
  have hL0 : 0 < L := (by positivity : 0 < 2 * Real.exp 1).trans_le hL
  have hscale : 1000000 * Real.log L ≤ L := by
    have hh := (div_lt_iff₀ hL0).1 hsmall
    nlinarith
  have hhalf : L / 2 ≤ mrtLogPowerUpper L := by unfold mrtLogPowerUpper; linarith
  have hupper : mrtLogPowerUpper L ≤ L := by unfold mrtLogPowerUpper; linarith
  have hq : Real.exp 1 ≤ mrtLogPowerUpper L := by linarith
  have hq0 : 0 < mrtLogPowerUpper L := (Real.exp_pos 1).trans_le hq
  have hlogq : 1 ≤ Real.log (mrtLogPowerUpper L) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hq
    simpa only [Real.log_exp] using hh
  have hlogqL := Real.log_le_log hq0 hupper
  refine ⟨?_, hlog, hhalf, hupper, ?_, ?_, hq, hlogq, ?_⟩
  · have hh := Real.add_one_le_exp (1 : ℝ)
    linarith
  · unfold mrtLogPowerLower
    linarith
  · unfold mrtLogPowerLower mrtLogPowerUpper
    linarith
  · unfold mrtLogPowerLower
    linarith

theorem mrtTendsto_logPower_ratio :
    Tendsto (fun L : ℝ ↦ mrtLogPowerLower L / mrtLogPowerUpper L) atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hnum : Tendsto (fun L : ℝ ↦ 204800 * (Real.log L / L)) atTop (𝓝 0) := by
    simpa only [mul_zero, id_eq] using hlog.const_mul 204800
  have hden : Tendsto (fun L : ℝ ↦ 1 - 3072 * (Real.log L / L)) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero, id_eq] using tendsto_const_nhds.sub (hlog.const_mul 3072)
  have hh : Tendsto (fun L : ℝ ↦ (204800 * (Real.log L / L)) /
      (1 - 3072 * (Real.log L / L))) atTop (𝓝 0) := by
    have hdiv := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    rw [zero_div] at hdiv
    exact hdiv
  apply hh.congr'
  filter_upwards [mrtEventually_logPower_geometry] with L hL
  have hL0 : L ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hL.1)
  have hq0 : mrtLogPowerUpper L ≠ 0 :=
    ne_of_gt ((Real.exp_pos 1).trans_le hL.2.2.2.2.2.2.1)
  unfold mrtLogPowerLower mrtLogPowerUpper at hq0 ⊢
  field_simp [hL0, hq0]

theorem mrtTendsto_logPower_cutoff : Tendsto mrtLogPowerCutoff atTop (𝓝 0) := by
  have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 10240 1 (by norm_num : (0 : ℝ) < 1)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [Real.rpow_def_of_pos hL, ← Real.exp_add]
  unfold mrtLogPowerCutoff
  congr 1
  ring

theorem mrtTendsto_logPower_window : Tendsto mrtLogPowerWindow atTop atTop := by
  exact Real.tendsto_exp_atTop.comp
    (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1024))

/-- Every source condition and every prescribed positive ratio ceiling hold eventually. -/
theorem mrtEventually_logPower_source {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧ 2 ≤ mrtLogPowerWindow L ∧
      2 ≤ mrtLogPowerLower L ∧ Real.exp 1 ≤ mrtLogPowerUpper L ∧
      2 * mrtLogPowerLower L ≤ mrtLogPowerUpper L ∧
      1 ≤ Real.log (mrtLogPowerUpper L) ∧
      4096 * Real.log (mrtLogPowerUpper L) ≤ (1 / 12) * mrtLogPowerLower L ∧
      Real.log 2 + 2 * PrimeEstimates.mertensBound ≤
        Real.log (mrtLogPowerUpper L) - Real.log (mrtLogPowerLower L) ∧
      mrtLogPowerLower L / mrtLogPowerUpper L ≤ rho ∧
      0 < mrtLogPowerCutoff L ∧ mrtLogPowerCutoff L ≤ 1 / 2 := by
  let G := Real.log 2 + 2 * PrimeEstimates.mertensBound
  have hsmall : 0 < min rho (Real.exp (-G)) := lt_min hrho (Real.exp_pos _)
  filter_upwards [mrtEventually_logPower_geometry,
    mrtTendsto_logPower_ratio.eventually (gt_mem_nhds hsmall),
    mrtTendsto_logPower_cutoff.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    mrtTendsto_logPower_window.eventually (eventually_ge_atTop 2)]
    with L hgeometry hratio hcut hW
  obtain ⟨hL, _, _, _, hp, hpq, hq, hlogq, hbudget⟩ := hgeometry
  have hp0 : 0 < mrtLogPowerLower L := by linarith
  have hq0 : 0 < mrtLogPowerUpper L := (Real.exp_pos 1).trans_le hq
  have hgap : G ≤ Real.log (mrtLogPowerUpper L) - Real.log (mrtLogPowerLower L) := by
    have hh := Real.log_le_log (div_pos hp0 hq0)
      (hratio.le.trans (min_le_right _ _))
    rw [Real.log_div hp0.ne' hq0.ne', Real.log_exp] at hh
    linarith
  exact ⟨hL, hW, hp, hq, hpq, hlogq, hbudget, hgap,
    hratio.le.trans (min_le_left _ _), mrtLogPowerCutoff_pos L, hcut.le⟩

end

end Erdos67b
