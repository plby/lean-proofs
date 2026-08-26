import ErdosProblems.Erdos1038.HighKTerminalPlatform
import ErdosProblems.Erdos1038.RationalInterval
import ErdosProblems.Erdos1038.KernelDecision

/-!
# Analytic range facts for the terminal high-ratio parametrization

The terminal numerical charts use `q` as their parameter.  This file
separates the elementary analytic facts about the resulting ratio from the
finite interval certificates for the scalar circle base.
-/

set_option warningAsError false
set_option maxRecDepth 100000

open Filter Set
open scoped Topology

namespace Erdos1038

noncomputable section

/-- The logarithmic denominator in the terminal ratio is positive throughout
the genuine one-cut terminal range. -/
theorem scaledD_pos_of_pos_lt_qSoft
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < scaledD q := by
  rw [scaledD]
  apply Real.log_pos
  have hqBound : q < 1 / 7 :=
    hqs.trans qSoft_mem_Ioo_one_ninth_one_seventh.2
  have hden : 0 < (1 + q) ^ 2 := sq_pos_of_pos (by linarith)
  rw [one_lt_div hden]
  nlinarith

/-- Closed logarithmic formula for the terminal platform ratio. -/
theorem terminalPlatformRatio_eq_neg_log_div_scaledD_sub_one
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    terminalPlatformRatio q = -Real.log q / scaledD q - 1 := by
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hlogq : Real.log q ≠ 0 := log_q_ne_zero hq hq1
  have hD : scaledD q ≠ 0 := (scaledD_pos_of_pos_lt_qSoft hq hqs).ne'
  have hAeq : A q = 1 + scaledD q / Real.log q := by
    rw [A, log_H_decomposition hq, scaledD]
    field_simp [hlogq]
  rw [terminalPlatformRatio, positiveBufferRatio, hAeq]
  field_simp [hlogq, hD]
  ring

/-- The terminal ratio is continuous at every interior terminal parameter. -/
theorem continuousAt_terminalPlatformRatio
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    ContinuousAt terminalPlatformRatio q := by
  unfold terminalPlatformRatio positiveBufferRatio
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hA := (hasDerivAt_A hq hq1).continuousAt
  have hAone := (A_mem_Ioo_of_mem_Ioo
    (q_mem_Ioo_of_pos_le_qSoft hq hqs.le)).2
  exact hA.div (continuousAt_const.sub hA) (sub_ne_zero.mpr hAone.ne')

/-- The scaled logarithmic denominator has the positive limit `log 2` as
the terminal parameter approaches zero from the right. -/
theorem tendsto_scaledD_nhdsGT_zero :
    Tendsto scaledD (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2)) := by
  have hq : Tendsto (fun q : ℝ ↦ q) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hone : Tendsto (fun q : ℝ ↦ 1 + q) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using! tendsto_const_nhds.add hq
  have harg : Tendsto (fun q : ℝ ↦ 2 / (1 + q) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    simpa using! tendsto_const_nhds.div (hone.pow 2)
      (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  simpa only [scaledD] using!
    (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp harg

/-- The terminal ratio exhausts arbitrarily large ratios as `q → 0+`. -/
theorem tendsto_terminalPlatformRatio_nhdsGT_zero_atTop :
    Tendsto terminalPlatformRatio (𝓝[>] (0 : ℝ)) atTop := by
  have hnegLog : Tendsto (fun q : ℝ ↦ -Real.log q)
      (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [Function.comp_def] using!
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hDinv : Tendsto (fun q : ℝ ↦ (scaledD q)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2)⁻¹) :=
    tendsto_scaledD_nhdsGT_zero.inv₀ (Real.log_pos (by norm_num)).ne'
  have hquot : Tendsto (fun q : ℝ ↦ -Real.log q / scaledD q)
      (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [div_eq_mul_inv] using!
      hnegLog.atTop_mul_pos (inv_pos.mpr (Real.log_pos (by norm_num))) hDinv
  have hqsEventually : ∀ᶠ q : ℝ in 𝓝[>] (0 : ℝ), q < qSoft :=
    (eventually_lt_nhds qSoft_mem_Ioo.1).filter_mono inf_le_left
  have hformula : terminalPlatformRatio =ᶠ[𝓝[>] (0 : ℝ)]
      (fun q : ℝ ↦ -Real.log q / scaledD q - 1) := by
    filter_upwards [self_mem_nhdsWithin, hqsEventually] with q hq hqs
    exact terminalPlatformRatio_eq_neg_log_div_scaledD_sub_one hq hqs
  apply Tendsto.congr' hformula.symm
  simpa only [sub_eq_add_neg] using!
    tendsto_atTop_add_const_right (𝓝[>] (0 : ℝ)) (-1) hquot

private theorem terminalRatio_one_tenth_rat_certificate :
    5 * logUpperRat 80 (10 : Rat) <
      26 * logLowerRat 80 (200 / 121 : Rat) := by
  kernel_decide

/-- A simple rational point lies below the constant/terminal interface.
Together with the limit at zero, this is the finite endpoint input for the
terminal ratio range argument. -/
theorem terminalPlatformRatio_one_tenth_lt :
    terminalPlatformRatio (1 / 10 : ℝ) < 21 / 5 := by
  have hq : (0 : ℝ) < 1 / 10 := by norm_num
  have hqs : (1 / 10 : ℝ) < qSoft := by
    have hsoft := qSoft_mem_Ioo_one_ninth_one_seventh.1
    norm_num at hsoft ⊢
    linarith
  rw [terminalPlatformRatio_eq_neg_log_div_scaledD_sub_one hq hqs]
  have hD : 0 < scaledD (1 / 10 : ℝ) :=
    scaledD_pos_of_pos_lt_qSoft hq hqs
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hD]
  have hlogq : -Real.log (1 / 10 : ℝ) = Real.log 10 := by
    rw [show (1 / 10 : ℝ) = (10 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have hscaled : scaledD (1 / 10 : ℝ) = Real.log (200 / 121) := by
    norm_num [scaledD]
  rw [hlogq, hscaled]
  have hten : Real.log 10 ≤ ((logUpperRat 80 (10 : Rat) : Rat) : ℝ) :=
    log_le_logUpperRat (n := 80) (r := 10) (by norm_num)
  have hd : ((logLowerRat 80 (200 / 121 : Rat) : Rat) : ℝ) ≤
      Real.log (200 / 121 : ℝ) :=
    by
      simpa using!
        (logLowerRat_le_log (n := 80) (r := 200 / 121) (by norm_num))
  have hrat :
      (5 : ℝ) * ((logUpperRat 80 (10 : Rat) : Rat) : ℝ) <
        26 * ((logLowerRat 80 (200 / 121 : Rat) : Rat) : ℝ) := by
    exact_mod_cast terminalRatio_one_tenth_rat_certificate
  nlinarith

/-- Every ratio strictly beyond the constant-edge interface occurs at a
genuine terminal parameter.  No monotonicity is needed: the one-sided limit,
one finite endpoint, continuity, and the intermediate value theorem suffice.
-/
theorem exists_terminalPlatformRatio_eq_of_twenty_one_fifths_lt
    {k : ℝ} (hk : 21 / 5 < k) :
    ∃ q : ℝ, 0 < q ∧ q < qSoft ∧ terminalPlatformRatio q = k := by
  have hlarge : ∀ᶠ q : ℝ in 𝓝[>] (0 : ℝ),
      k < terminalPlatformRatio q :=
    tendsto_terminalPlatformRatio_nhdsGT_zero_atTop.eventually_gt_atTop k
  have hsmall : ∀ᶠ q : ℝ in 𝓝[>] (0 : ℝ), q < 1 / 10 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 10)).filter_mono
      inf_le_left
  have hpositive : ∀ᶠ q : ℝ in 𝓝[>] (0 : ℝ), 0 < q :=
    self_mem_nhdsWithin
  rcases (hlarge.and (hsmall.and hpositive)).exists with
    ⟨q₀, hkq₀, hq₀Small, hq₀Pos⟩
  have hOneTenthSoft : (1 / 10 : ℝ) < qSoft := by
    have hsoft := qSoft_mem_Ioo_one_ninth_one_seventh.1
    norm_num at hsoft ⊢
    linarith
  have hcont : ContinuousOn terminalPlatformRatio (Icc q₀ (1 / 10 : ℝ)) := by
    intro q hq
    apply (continuousAt_terminalPlatformRatio
      (hq₀Pos.trans_le hq.1) (hq.2.trans_lt hOneTenthSoft)).continuousWithinAt
  have hkBetween : k ∈ Icc
      (terminalPlatformRatio (1 / 10 : ℝ))
      (terminalPlatformRatio q₀) :=
    ⟨terminalPlatformRatio_one_tenth_lt.trans hk |>.le, hkq₀.le⟩
  obtain ⟨q, hqInterval, hratio⟩ :=
    intermediate_value_Icc' hq₀Small.le hcont hkBetween
  exact ⟨q, hq₀Pos.trans_le hqInterval.1,
    hqInterval.2.trans_lt hOneTenthSoft, hratio⟩

end

end Erdos1038
