import ErdosProblems.Erdos1038.HighKTerminalRatioAnalysis
import ErdosProblems.Erdos1038.OneCutTailCertificate
import ErdosProblems.Erdos1038.KernelDecision

/-!
# A rational cutoff for the terminal scalar chart

The terminal ratio is strictly decreasing before the soft edge.  Its value
at `41542/10^6` is already below `21/5`, so every parameter relevant to the
terminal certificate lies strictly to the left of that rational cutoff.
-/

set_option warningAsError false
set_option maxRecDepth 100000

open Set

namespace Erdos1038

noncomputable section

def terminalScalarQCapRat : Rat := 41542 / 10 ^ 6

theorem Aprime_eq_neg_softFunction_div
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Aprime q =
      -softFunction q / (q * (1 + q) * (Real.log q) ^ 2) := by
  have hq0 := hq.ne'
  have hqden : 1 + q ≠ 0 := by linarith
  have hlog := log_q_ne_zero hq hq1
  rw [Aprime, OneCutTailCertificate.Hprime_div_H_eq hq,
    log_H_decomposition hq]
  unfold softFunction
  field_simp [hq0, hqden, hlog]
  ring

theorem Aprime_neg_of_pos_lt_qSoft
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    Aprime q < 0 := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hsoft : 0 < softFunction q := by
    have hf : softFunction qSoft < softFunction q :=
      softFunction_strictAntiOn_Ioo_zero_qCeiling
        hqdom qSoft_mem_Ioo hqs
    rwa [softFunction_qSoft_eq_zero] at hf
  rw [Aprime_eq_neg_softFunction_div hq hq1]
  have hlog0 := log_q_ne_zero hq hq1
  have hden : 0 < q * (1 + q) * (Real.log q) ^ 2 :=
    mul_pos (mul_pos hq (by linarith)) (sq_pos_of_ne_zero hlog0)
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hsoft) hden

theorem hasDerivAt_terminalPlatformRatio
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    HasDerivAt terminalPlatformRatio
      (Aprime q / (1 - A q) ^ 2) q := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hA := A_mem_Ioo_of_mem_Ioo
    (q_mem_Ioo_of_pos_le_qSoft hq hqs.le)
  have hAderiv := hasDerivAt_A hq hq1
  have hden := (hasDerivAt_const q (1 : ℝ)).sub hAderiv
  have hquot := hAderiv.div hden (sub_ne_zero.mpr hA.2.ne')
  simp only [Pi.sub_apply, zero_sub] at hquot
  convert! hquot using 1
  field_simp [sub_ne_zero.mpr hA.2.ne']
  ring

theorem terminalPlatformRatio_deriv_neg
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    deriv terminalPlatformRatio q < 0 := by
  rw [(hasDerivAt_terminalPlatformRatio hq hqs).deriv]
  exact div_neg_of_neg_of_pos (Aprime_neg_of_pos_lt_qSoft hq hqs)
    (sq_pos_of_ne_zero (by
      have hA := A_mem_Ioo_of_mem_Ioo
        (q_mem_Ioo_of_pos_le_qSoft hq hqs.le)
      linarith [hA.2]))

theorem terminalPlatformRatio_continuousOn :
    ContinuousOn terminalPlatformRatio (Ioo (0 : ℝ) qSoft) := by
  intro q hq
  exact (hasDerivAt_terminalPlatformRatio hq.1 hq.2).continuousAt
    |>.continuousWithinAt

theorem terminalPlatformRatio_strictAntiOn :
    StrictAntiOn terminalPlatformRatio (Ioo (0 : ℝ) qSoft) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 qSoft)
    terminalPlatformRatio_continuousOn
  rw [interior_Ioo]
  intro q hq
  exact terminalPlatformRatio_deriv_neg hq.1 hq.2

private theorem terminalRatio_qCap_rat_certificate :
    5 * logUpperRat 120 (1 / terminalScalarQCapRat) <
      26 * logLowerRat 120
        (2 / (1 + terminalScalarQCapRat) ^ 2) := by
  kernel_decide

theorem terminalPlatformRatio_qCap_lt :
    terminalPlatformRatio (terminalScalarQCapRat : ℝ) < 21 / 5 := by
  have hq : (0 : ℝ) < (terminalScalarQCapRat : ℝ) := by
    norm_num [terminalScalarQCapRat]
  have hqs : (terminalScalarQCapRat : ℝ) < qSoft := by
    have hrat : (terminalScalarQCapRat : ℝ) <
        (qSoftLowerRat : ℝ) := by
      norm_num [terminalScalarQCapRat, qSoftLowerRat]
    exact hrat.trans qSoftLower_lt_qSoft
  rw [terminalPlatformRatio_eq_neg_log_div_scaledD_sub_one hq hqs]
  have hD := scaledD_pos_of_pos_lt_qSoft hq hqs
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hD]
  have hlogq : -Real.log (terminalScalarQCapRat : ℝ) =
      Real.log ((1 / terminalScalarQCapRat : Rat) : ℝ) := by
    rw [show (((1 / terminalScalarQCapRat : Rat) : ℝ)) =
      ((terminalScalarQCapRat : ℝ))⁻¹ by
        norm_num [terminalScalarQCapRat], Real.log_inv]
  have hscaled : scaledD (terminalScalarQCapRat : ℝ) =
      Real.log ((2 / (1 + terminalScalarQCapRat) ^ 2 : Rat) : ℝ) := by
    norm_num [scaledD, terminalScalarQCapRat]
  rw [hlogq, hscaled]
  have hnum : Real.log ((1 / terminalScalarQCapRat : Rat) : ℝ) ≤
      ((logUpperRat 120 (1 / terminalScalarQCapRat) : Rat) : ℝ) :=
    log_le_logUpperRat (n := 120) (r := 1 / terminalScalarQCapRat)
      (by norm_num [terminalScalarQCapRat])
  have hden :
      ((logLowerRat 120
        (2 / (1 + terminalScalarQCapRat) ^ 2) : Rat) : ℝ) ≤
      Real.log ((2 / (1 + terminalScalarQCapRat) ^ 2 : Rat) : ℝ) :=
    logLowerRat_le_log (n := 120)
      (r := 2 / (1 + terminalScalarQCapRat) ^ 2)
      (by norm_num [terminalScalarQCapRat])
  have hrat :
      (5 : ℝ) *
          ((logUpperRat 120 (1 / terminalScalarQCapRat) : Rat) : ℝ) <
        26 * ((logLowerRat 120
          (2 / (1 + terminalScalarQCapRat) ^ 2) : Rat) : ℝ) := by
    exact_mod_cast terminalRatio_qCap_rat_certificate
  nlinarith

theorem q_lt_terminalScalarQCap_of_ratio_gt
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    (hk : 21 / 5 < terminalPlatformRatio q) :
    q < (terminalScalarQCapRat : ℝ) := by
  have hcapPos : (0 : ℝ) < (terminalScalarQCapRat : ℝ) := by
    norm_num [terminalScalarQCapRat]
  have hcapSoft : (terminalScalarQCapRat : ℝ) < qSoft := by
    have hrat : (terminalScalarQCapRat : ℝ) <
        (qSoftLowerRat : ℝ) := by
      norm_num [terminalScalarQCapRat, qSoftLowerRat]
    exact hrat.trans qSoftLower_lt_qSoft
  by_contra hlt
  have hle : (terminalScalarQCapRat : ℝ) ≤ q := le_of_not_gt hlt
  rcases hle.eq_or_lt with heq | hstrict
  · subst q
    linarith [terminalPlatformRatio_qCap_lt]
  · have hratio := terminalPlatformRatio_strictAntiOn
        ⟨hcapPos, hcapSoft⟩ ⟨hq, hqs⟩ hstrict
    linarith [terminalPlatformRatio_qCap_lt]

end

end Erdos1038
