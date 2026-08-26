import ErdosProblems.Erdos1038.HighKTerminalPlatform
import ErdosProblems.Erdos1038.HighKPlatformFunctionalAssembly
import ErdosProblems.Erdos1038.OneCutGlobalCertificate

/-!
# Exact calibration algebra for the terminal one-cut platform

The numerical terminal charts only need to certify the positive circle
base.  The favorable effective-potential coefficient is nonpositive for
free: the one-cut crossing width is `Lambda q`, while the completed global
one-cut certificate says `L ≤ Lambda q`.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

/-- A positive terminal base scalar and a nonpositive effective coefficient
are sufficient for the complete platform-specialized terminal certificate;
all cap positivity and `≤ π` fields follow from normalized-density facts. -/
theorem platformTerminalCalibration_of_base_pos
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hCeff : Ceff ≤ 0)
    (hbase : 0 < circleRectangleBase
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus)
      (platformReferenceCircleRadiusCap k a)
      (platformAdjointCircleRadiusCap
        a xMinus xPlus sigmaMinus sigmaPlus)) :
    PlatformTerminalCalibration k a xMinus xPlus
      sigmaMinus sigmaPlus Ceff := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hapi : 0 < platformAPi k a :=
    platformAPi_pos hk0 ha ha2.le
  have hbpi : 0 < platformBPi a xMinus xPlus
      sigmaMinus sigmaPlus :=
    platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  have hmass : 0 < platformAdjointMass a xMinus xPlus
      sigmaMinus sigmaPlus :=
    platformAdjointMass_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  unfold PlatformTerminalCalibration
  refine
    { aPi_pos := hapi
      Qmax_pos := ?_
      Qmax_le_pi := ?_
      Rmax_pos := ?_
      Rmax_le_pi := ?_
      Ceff_nonpos := hCeff
      base_pos := hbase }
  · unfold platformReferenceCircleRadiusCap
    exact div_pos Real.pi_pos hapi
  · unfold platformReferenceCircleRadiusCap
    rw [div_le_iff₀ hapi]
    nlinarith [one_le_platformAPi hk0 ha ha2.le, Real.pi_pos]
  · unfold platformAdjointCircleRadiusCap
    exact div_pos (mul_pos Real.pi_pos hmass) hbpi
  · have hfull := platformAdjointCircleRadius_mem_Icc
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
      (show (0 : ℝ) ≤ 0 by rfl) Real.pi_pos.le le_rfl
    rw [platformAdjointCircleRadius,
      integral_platformNormalizedAdjointDensity hxMinus hxPlus ha2] at hfull
    simpa only [platformAdjointCircleRadiusCap] using! hfull.2

/-- Explicit negative-crossing reciprocal slope in the terminal family. -/
def terminalPlatformSigmaMinus (q : ℝ) : ℝ :=
  -1 / platformExteriorWx (terminalPlatformRatio q)
    (terminalPlatformEdge q) (terminalPlatformXMinus q)

/-- Explicit positive-crossing reciprocal slope in the terminal family. -/
def terminalPlatformSigmaPlus (q : ℝ) : ℝ :=
  1 / platformExteriorWx (terminalPlatformRatio q)
    (terminalPlatformEdge q) (terminalPlatformXPlus q)

theorem one_le_terminalPlatformEdge
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    1 ≤ terminalPlatformEdge q := by
  have hqSeven : q < 1 / 7 :=
    hqs.trans qSoft_mem_Ioo_one_ninth_one_seventh.2
  have hden : 0 < 1 + q := one_add_pos hq
  have hsLower : 3 / 4 < s q := by
    unfold s
    rw [lt_div_iff₀ hden]
    linarith
  unfold terminalPlatformEdge positiveBufferDistanceLeft
  nlinarith

theorem terminalPlatformSigmaMinus_pos
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < terminalPlatformSigmaMinus q := by
  unfold terminalPlatformSigmaMinus
  exact div_pos_of_neg_of_neg (by norm_num)
    (terminalPlatformXMinus_slope_neg hq hqs)

theorem terminalPlatformSigmaPlus_pos
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < terminalPlatformSigmaPlus q := by
  unfold terminalPlatformSigmaPlus
  exact one_div_pos.mpr (terminalPlatformXPlus_slope_pos hq hqs)

/-- The terminal effective constant is nonpositive without any interval
evaluation. -/
theorem terminalPlatform_effectiveConstant_nonpos
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformEffectiveConstant L (terminalPlatformRatio q)
      (terminalPlatformEdge q) (terminalPlatformXMinus q)
      (terminalPlatformXPlus q) (terminalPlatformSigmaMinus q)
      (terminalPlatformSigmaPlus q) ≤ 0 := by
  have hparams := terminalPlatform_parameters hq hqs
  have hbounds := terminalPlatform_crossing_bounds hq hqs
  have hmass : 0 < platformAdjointMass (terminalPlatformEdge q)
      (terminalPlatformXMinus q) (terminalPlatformXPlus q)
      (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q) :=
    platformAdjointMass_pos
      (hbounds.1.trans hparams.2.1) hbounds.2.2.2
      (terminalPlatformSigmaMinus_pos hq hqs)
      (terminalPlatformSigmaPlus_pos hq hqs) hparams.2.2.1
  have hminimum := oneCut_global_certificate.2.1
  have hLle : L ≤ Lambda q := by
    have hqmem : q ∈ Set.Ioc (0 : ℝ) qSoft := ⟨hq, hqs.le⟩
    simpa only [L] using! hminimum.2 q hqmem
  unfold platformEffectiveConstant
  rw [terminalPlatform_potentialConstant_eq_zero hq hqs,
    terminalPlatform_crossing_width q]
  simp only [zero_add]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hLle) hmass.le

/-- A terminal scalar calibration is one branch of the unified effective
calibration interface. -/
theorem terminalPlatform_effectiveCalibration_of_terminalCalibration
    {q : ℝ}
    (hcalibration : PlatformTerminalCalibration
      (terminalPlatformRatio q) (terminalPlatformEdge q)
      (terminalPlatformXMinus q) (terminalPlatformXPlus q)
      (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q)
      (platformEffectiveConstant L (terminalPlatformRatio q)
        (terminalPlatformEdge q) (terminalPlatformXMinus q)
        (terminalPlatformXPlus q) (terminalPlatformSigmaMinus q)
        (terminalPlatformSigmaPlus q))) :
    PlatformEffectiveCalibration
      (terminalPlatformRatio q) (terminalPlatformEdge q)
      (terminalPlatformXMinus q) (terminalPlatformXPlus q)
      (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q) := by
  exact Or.inr (Or.inr hcalibration)

/-- Terminal charts need certify only the displayed base scalar.  The
remaining terminal calibration fields, including `Ceff ≤ 0`, are automatic. -/
theorem terminalPlatform_effectiveCalibration_of_base_pos
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    (hk : 1 ≤ terminalPlatformRatio q)
    (hbase : 0 < circleRectangleBase
      (platformCapacity (terminalPlatformEdge q))
      (platformAPi (terminalPlatformRatio q) (terminalPlatformEdge q))
      (platformBPi (terminalPlatformEdge q)
        (terminalPlatformXMinus q) (terminalPlatformXPlus q)
        (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q))
      (platformReferenceCircleRadiusCap
        (terminalPlatformRatio q) (terminalPlatformEdge q))
      (platformAdjointCircleRadiusCap (terminalPlatformEdge q)
        (terminalPlatformXMinus q) (terminalPlatformXPlus q)
        (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q))) :
    PlatformEffectiveCalibration
      (terminalPlatformRatio q) (terminalPlatformEdge q)
      (terminalPlatformXMinus q) (terminalPlatformXPlus q)
      (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q) := by
  have hparams := terminalPlatform_parameters hq hqs
  have hbounds := terminalPlatform_crossing_bounds hq hqs
  apply terminalPlatform_effectiveCalibration_of_terminalCalibration
  apply platformTerminalCalibration_of_base_pos
    hk hparams.2.1 hparams.2.2.1
      (hbounds.1.trans hparams.2.1) hbounds.2.2.2
      (terminalPlatformSigmaMinus_pos hq hqs)
      (terminalPlatformSigmaPlus_pos hq hqs)
      (terminalPlatform_effectiveConstant_nonpos hq hqs)
  exact hbase

end

end Erdos1038
