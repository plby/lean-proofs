import ErdosProblems.Erdos1038.RecoveryPositiveLimit
import ErdosProblems.Erdos1038.PlatformExteriorPotentialIdentity
import ErdosProblems.Erdos1038.HighKPlatformCrossing
import ErdosProblems.Erdos1038.LambdaAnalysis
import ErdosProblems.Erdos1038.PlatformReferenceExteriorCrossingBridge

/-!
# The terminal one-cut family as a high-k platform

This file identifies the zero-platform one-cut family with the platform
parameters used by the high-k block argument.  In particular, it supplies
the two exterior zeroes in the platform distance coordinate.  The remaining
terminal computation is then purely the scalar circle certificate.
-/

set_option warningAsError false

open Filter MeasureTheory Set

namespace Erdos1038

noncomputable section

open HighKPlatformFormula

/-- Residual ratio of the terminal zero-platform family. -/
def terminalPlatformRatio (q : ℝ) : ℝ :=
  positiveBufferRatio (A q)

/-- Left edge of the terminal platform in distance coordinates. -/
def terminalPlatformEdge (q : ℝ) : ℝ :=
  positiveBufferDistanceLeft (s q)

/-- Far-left exterior zero in the terminal platform distance coordinate. -/
def terminalPlatformXMinus (q : ℝ) : ℝ :=
  oneCutExteriorDistance q (uMinus q)

/-- Gap-side exterior zero in the terminal platform distance coordinate. -/
def terminalPlatformXPlus (q : ℝ) : ℝ :=
  oneCutExteriorDistance q (uPlus q)

theorem terminalPlatform_parameters
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 ≤ terminalPlatformRatio q ∧
      0 < terminalPlatformEdge q ∧
      terminalPlatformEdge q < 2 ∧
      platformThreshold (terminalPlatformRatio q) ≤
        terminalPlatformEdge q := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hs := s_mem_Ioo_of_mem_Ioo hqdom
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hAs := A_le_s_of_pos_le_qSoft hq hqs.le
  exact ⟨positiveBufferRatio_nonneg hA.1.le hA.2,
    positiveBufferDistanceLeft_pos hs.1,
    positiveBufferDistanceLeft_lt_two hs.1 hs.2,
    positiveBuffer_threshold_le hs.1.le hs.2 hA.1.le hAs⟩

/-- The platform constant vanishes identically on the terminal family. -/
theorem terminalPlatform_potentialConstant_eq_zero
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformPotentialConstant (terminalPlatformRatio q)
      (terminalPlatformEdge q) = 0 := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hden : 1 - A q ≠ 0 := sub_ne_zero.mpr hA.2.ne'
  have hscale :
      (1 - A q) *
          platformPotentialConstant (terminalPlatformRatio q)
            (terminalPlatformEdge q) =
        positiveBufferPlatformValue (s q) (A q) := by
    unfold terminalPlatformRatio terminalPlatformEdge
      positiveBufferRatio platformPotentialConstant
      positiveBufferPlatformValue
    field_simp [hden]
  have hzero := positiveBufferPlatformValue_s_A_eq_zero hqdom
  have hmul : (1 - A q) *
      platformPotentialConstant (terminalPlatformRatio q)
        (terminalPlatformEdge q) = 0 := by
    rw [hscale, hzero]
  exact (mul_eq_zero.mp hmul).resolve_left hden

/-- The logarithmic correction occurring in the explicit exterior formula
is automatically positive for every genuine platform and exterior point. -/
theorem platformExteriorCorrection_pos
    {a x : ℝ} (ha : 0 < a) (ha2 : a < 2) (hx : x < a) :
    0 < 1 -
      ((Real.sqrt 2 - Real.sqrt a) /
        (Real.sqrt 2 + Real.sqrt a)) * platformRho a x := by
  have hsqrtTwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtA : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsqrtTwoSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtASq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have hsqrtLt : Real.sqrt a < Real.sqrt 2 := by
    nlinarith
  have hden : 0 < Real.sqrt 2 + Real.sqrt a := add_pos hsqrtTwo hsqrtA
  let rho0 := (Real.sqrt 2 - Real.sqrt a) /
    (Real.sqrt 2 + Real.sqrt a)
  have hrho0Pos : 0 < rho0 := by
    exact div_pos (sub_pos.mpr hsqrtLt) hden
  have hrho0Lt : rho0 < 1 := by
    exact (div_lt_one hden).2 (by linarith)
  have hrho := platformRho_mem_Ioo hx ha2
  have hmulLt : rho0 * platformRho a x < rho0 := by
    simpa only [mul_one] using!
      mul_lt_mul_of_pos_left hrho.2 hrho0Pos
  dsimp only [rho0] at hrho0Pos hrho0Lt hmulLt ⊢
  linarith

/-- The terminal probability potential is the platform exterior function,
scaled by its continuous mass.  The observation point is shifted from root
coordinates to the platform distance coordinate by `x ↦ x - 1`. -/
theorem positiveBufferPotential_terminal_eq_mul_platformExteriorW
    {q x : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    (hx : x < terminalPlatformEdge q) (hx0 : x ≠ 0) :
    positiveBufferPotential (s q) (A q) (x - 1) =
      (1 - A q) *
        platformExteriorW (terminalPlatformRatio q)
          (terminalPlatformEdge q) x := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hs := s_mem_Ioo_of_mem_Ioo hqdom
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hAs := A_le_s_of_pos_le_qSoft hq hqs.le
  obtain ⟨hk, ha, ha2, hthreshold⟩ :=
    terminalPlatform_parameters hq hqs
  have hsplit := positiveBufferPotential_eq_atom_add_continuous
    (s := s q) (alpha := A q) (x := x - 1)
    hs.1 hs.2 hA.1.le hAs
  have hangular :=
    integral_platformConstantReferenceMeasure_log_kernel_eq_angular
      hk ha ha2 hthreshold (d := x)
  change
      (∫ e : ℝ, Real.log |x - e|
        ∂(positiveBufferContinuousDistanceMeasure (s q) (A q))) =
        (1 / Real.pi) *
          ∫ theta : ℝ in 0..Real.pi,
            Real.log
                |x - platformAngularDistance (terminalPlatformEdge q) theta| *
              platformAngularDensity (terminalPlatformRatio q)
                (terminalPlatformEdge q) theta at hangular
  have hangular' :
      (∫ e : ℝ, Real.log |x - e|
        ∂(positiveBufferContinuousDistanceMeasure (s q) (A q))) =
        (1 / Real.pi) *
          ∫ theta : ℝ in 0..Real.pi,
            Real.log
                (platformAngularDistance (terminalPlatformEdge q) theta - x) *
              platformAngularDensity (terminalPlatformRatio q)
                (terminalPlatformEdge q) theta := by
    rw [hangular]
    congr 1
    apply intervalIntegral.integral_congr
    intro theta htheta
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    have hdistance :
        x < platformAngularDistance (terminalPlatformEdge q) theta :=
      hx.trans_le (platformAngularDistance_mem_Icc ha2.le htheta).1
    change
      Real.log |x - platformAngularDistance (terminalPlatformEdge q) theta| *
          platformAngularDensity (terminalPlatformRatio q)
            (terminalPlatformEdge q) theta =
        Real.log (platformAngularDistance (terminalPlatformEdge q) theta - x) *
          platformAngularDensity (terminalPlatformRatio q)
            (terminalPlatformEdge q) theta
    rw [abs_of_neg (sub_neg.mpr hdistance)]
    ring_nf
  have hW := platformExteriorW_eq_angularPotential
    ha ha2 hx hx0 (k := terminalPlatformRatio q)
  rw [hsplit]
  simp only [sub_add_cancel]
  rw [hangular', hW]
  have hratio :
      (1 - A q) * terminalPlatformRatio q = A q := by
    unfold terminalPlatformRatio positiveBufferRatio
    field_simp [sub_ne_zero.mpr hA.2.ne']
  conv_lhs =>
    lhs
    rw [← hratio]
  ring

theorem terminalPlatform_crossing_bounds
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    terminalPlatformXMinus q < 0 ∧
      0 < terminalPlatformXPlus q ∧
      terminalPlatformXMinus q < terminalPlatformXPlus q ∧
      terminalPlatformXPlus q < terminalPlatformEdge q := by
  have hcross := zeroPlatformNegativeEndpoints_order hq hqs
  unfold zeroPlatformNegativeLeftEndpoint
    zeroPlatformNegativeRightEndpoint at hcross
  unfold terminalPlatformXMinus terminalPlatformXPlus terminalPlatformEdge
  constructor
  · linarith [hcross.2.2.1]
  constructor
  · linarith [hcross.1]
  constructor
  · linarith [hcross.2.2.2]
  · linarith [hcross.2.1]

/-- The one-cut gap root is the positive exterior zero of the terminal
platform. -/
theorem terminalPlatformXPlus_zero
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
      (terminalPlatformXPlus q) = 0 := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hup := uPlus_spec hq hqs
  have hU := positiveBufferPotential_zeroPlatform_oneCut_inner
    hqdom hqs.le hup.1 hup.2.1
  have hroot := exteriorEquation_iff_exteriorFunction_eq_zero.mp hup.2.2
  rw [hroot, neg_zero] at hU
  have hbounds := terminalPlatform_crossing_bounds hq hqs
  have hbridge := positiveBufferPotential_terminal_eq_mul_platformExteriorW
    hq hqs hbounds.2.2.2 hbounds.2.1.ne'
  have hUzero :
      positiveBufferPotential (s q) (A q)
        (terminalPlatformXPlus q - 1) = 0 := by
    simpa [terminalPlatformXPlus] using! hU
  rw [hUzero] at hbridge
  have hqdomain := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hA := A_mem_Ioo_of_mem_Ioo hqdomain
  exact (mul_eq_zero.mp hbridge.symm).resolve_left
    (sub_ne_zero.mpr hA.2.ne')

/-- The one-cut far-left root is the negative exterior zero of the terminal
platform. -/
theorem terminalPlatformXMinus_zero
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
      (terminalPlatformXMinus q) = 0 := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hum := uMinus_spec hq hqs.le
  have hU := positiveBufferPotential_zeroPlatform_oneCut_outer
    hqdom hqs.le hum.1
  have hroot := exteriorEquation_iff_exteriorFunction_eq_zero.mp hum.2
  rw [hroot, neg_zero] at hU
  have hbounds := terminalPlatform_crossing_bounds hq hqs
  have hedge := (terminalPlatform_parameters hq hqs).2.1
  have hbridge := positiveBufferPotential_terminal_eq_mul_platformExteriorW
    hq hqs (hbounds.1.trans hedge) hbounds.1.ne
  have hUzero :
      positiveBufferPotential (s q) (A q)
        (terminalPlatformXMinus q - 1) = 0 := by
    simpa [terminalPlatformXMinus] using! hU
  rw [hUzero] at hbridge
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  exact (mul_eq_zero.mp hbridge.symm).resolve_left
    (sub_ne_zero.mpr hA.2.ne')

/-- Stable inner-coordinate form of the terminal platform exterior
function. -/
theorem platformExteriorW_terminal_inner
    {q u : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    (hu : 1 < u) (huq : u < q⁻¹) :
    platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
        (oneCutExteriorDistance q u) =
      -exteriorFunction q u / (1 - A q) := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hq1 := mem_Ioo_zero_qCeiling_imp_lt_one hqdom
  have hanti := oneCutExteriorDistance_strictAntiOn_Ici hq
  have hxlt : oneCutExteriorDistance q u < terminalPlatformEdge q := by
    have hstrict := hanti (show (1 : ℝ) ∈ Ici 1 by simp)
      (show u ∈ Ici 1 by exact hu.le) hu
    rw [oneCutExteriorDistance_one hq] at hstrict
    exact hstrict
  have hxpos : 0 < oneCutExteriorDistance q u := by
    have hinv1 := one_lt_inv_q hq hq1
    have hstrict := hanti (show u ∈ Ici 1 by exact hu.le)
      (show q⁻¹ ∈ Ici 1 by exact hinv1.le) huq
    rw [oneCutExteriorDistance_inv] at hstrict
    exact hstrict
  have hbridge := positiveBufferPotential_terminal_eq_mul_platformExteriorW
    hq hqs hxlt hxpos.ne'
  have hU := positiveBufferPotential_zeroPlatform_oneCut_inner
    hqdom hqs.le hu huq
  rw [hU] at hbridge
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  apply (eq_div_iff (sub_ne_zero.mpr hA.2.ne')).2
  calc
    platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
          (oneCutExteriorDistance q u) * (1 - A q) =
        (1 - A q) *
          platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
            (oneCutExteriorDistance q u) := by ring
    _ = -exteriorFunction q u := hbridge.symm

/-- Stable outer-coordinate form of the terminal platform exterior
function. -/
theorem platformExteriorW_terminal_outer
    {q u : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    (huq : q⁻¹ < u) :
    platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
        (oneCutExteriorDistance q u) =
      -exteriorFunction q u / (1 - A q) := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hq1 := mem_Ioo_zero_qCeiling_imp_lt_one hqdom
  have hinv1 := one_lt_inv_q hq hq1
  have hu : 1 < u := hinv1.trans huq
  have hanti := oneCutExteriorDistance_strictAntiOn_Ici hq
  have hxlt : oneCutExteriorDistance q u < terminalPlatformEdge q := by
    have hstrict := hanti (show (1 : ℝ) ∈ Ici 1 by simp)
      (show u ∈ Ici 1 by exact hu.le) hu
    rw [oneCutExteriorDistance_one hq] at hstrict
    exact hstrict
  have hxneg : oneCutExteriorDistance q u < 0 := by
    have hstrict := hanti (show q⁻¹ ∈ Ici 1 by exact hinv1.le)
      (show u ∈ Ici 1 by exact hu.le) huq
    rw [oneCutExteriorDistance_inv] at hstrict
    exact hstrict
  have hbridge := positiveBufferPotential_terminal_eq_mul_platformExteriorW
    hq hqs hxlt hxneg.ne
  have hU := positiveBufferPotential_zeroPlatform_oneCut_outer
    hqdom hqs.le huq
  rw [hU] at hbridge
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  apply (eq_div_iff (sub_ne_zero.mpr hA.2.ne')).2
  calc
    platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
          (oneCutExteriorDistance q u) * (1 - A q) =
        (1 - A q) *
          platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
            (oneCutExteriorDistance q u) := by ring
    _ = -exteriorFunction q u := hbridge.symm

/-- The gap-side terminal zero is crossed with positive platform slope. -/
theorem terminalPlatformXPlus_slope_pos
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < platformExteriorWx (terminalPlatformRatio q)
      (terminalPlatformEdge q) (terminalPlatformXPlus q) := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hq1 := mem_Ioo_zero_qCeiling_imp_lt_one hqdom
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hup := uPlus_spec hq hqs
  have hbounds := terminalPlatform_crossing_bounds hq hqs
  have hparams := terminalPlatform_parameters hq hqs
  have hcorr :
      1 -
          ((Real.sqrt 2 - Real.sqrt (terminalPlatformEdge q)) /
            (Real.sqrt 2 + Real.sqrt (terminalPlatformEdge q))) *
            platformRho (terminalPlatformEdge q) (terminalPlatformXPlus q) ≠ 0 :=
    (platformExteriorCorrection_pos hparams.2.1 hparams.2.2.1
      hbounds.2.2.2).ne'
  have hW := hasDerivAt_platformExteriorW_x
    (k := terminalPlatformRatio q)
    hbounds.2.2.2 hparams.2.2.1 hbounds.2.1.ne' hcorr
  have hD := hasDerivAt_oneCutExteriorDistance
    (q := q) (u := uPlus q) (by linarith [hup.1])
  have hleft := hW.comp (uPlus q) hD
  have hext := hasDerivAt_exteriorFunction_inner hq
    (by linarith [hup.1]) (hq1.trans hup.1) hup.2.1
  have hright : HasDerivAt
      (fun u : ℝ ↦ -exteriorFunction q u / (1 - A q))
      (-innerPartialU q (uPlus q) / (1 - A q)) (uPlus q) := by
    simpa [innerPartialU, innerNumerator, exteriorB] using!
      hext.neg.div_const (1 - A q)
  have hevent :
      (fun u : ℝ ↦
        platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
          (oneCutExteriorDistance q u)) =ᶠ[nhds (uPlus q)]
        (fun u : ℝ ↦ -exteriorFunction q u / (1 - A q)) := by
    filter_upwards [Ioi_mem_nhds hup.1, Iio_mem_nhds hup.2.1] with u hu1 huq
    exact platformExteriorW_terminal_inner hq hqs hu1 huq
  have hslope :
      platformExteriorWx (terminalPlatformRatio q) (terminalPlatformEdge q)
            (terminalPlatformXPlus q) *
          (H q * (-1 + ((uPlus q) ^ 2)⁻¹)) =
        -innerPartialU q (uPlus q) / (1 - A q) := by
    change
      platformExteriorWx (terminalPlatformRatio q) (terminalPlatformEdge q)
            (oneCutExteriorDistance q (uPlus q)) *
          (H q * (-1 + ((uPlus q) ^ 2)⁻¹)) =
        -innerPartialU q (uPlus q) / (1 - A q)
    exact hleft.unique (hright.congr_of_eventuallyEq hevent)
  have hinv : ((uPlus q) ^ 2)⁻¹ < 1 := by
    rw [inv_lt_one₀ (sq_pos_of_pos (by linarith [hup.1]))]
    nlinarith [hup.1]
  have hDneg : H q * (-1 + ((uPlus q) ^ 2)⁻¹) < 0 :=
    mul_neg_of_pos_of_neg (H_pos hq) (by linarith)
  have hrightNeg :
      -innerPartialU q (uPlus q) / (1 - A q) < 0 :=
    div_neg_of_neg_of_pos (neg_lt_zero.mpr (innerPartialU_uPlus_pos hq hqs))
      (sub_pos.mpr hA.2)
  by_contra hn
  have hWxNonpos :
      platformExteriorWx (terminalPlatformRatio q) (terminalPlatformEdge q)
          (terminalPlatformXPlus q) ≤ 0 := le_of_not_gt hn
  have hprodNonneg := mul_nonneg_of_nonpos_of_nonpos hWxNonpos hDneg.le
  rw [hslope] at hprodNonneg
  linarith

/-- The far-left terminal zero is crossed with negative platform slope. -/
theorem terminalPlatformXMinus_slope_neg
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformExteriorWx (terminalPlatformRatio q)
        (terminalPlatformEdge q) (terminalPlatformXMinus q) < 0 := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hq1 := mem_Ioo_zero_qCeiling_imp_lt_one hqdom
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hinv1 := one_lt_inv_q hq hq1
  have hum := uMinus_spec hq hqs.le
  have hu1 : 1 < uMinus q := hinv1.trans hum.1
  have hbounds := terminalPlatform_crossing_bounds hq hqs
  have hparams := terminalPlatform_parameters hq hqs
  have hxminusa : terminalPlatformXMinus q < terminalPlatformEdge q :=
    hbounds.1.trans hparams.2.1
  have hcorr :
      1 -
          ((Real.sqrt 2 - Real.sqrt (terminalPlatformEdge q)) /
            (Real.sqrt 2 + Real.sqrt (terminalPlatformEdge q))) *
            platformRho (terminalPlatformEdge q) (terminalPlatformXMinus q) ≠ 0 :=
    (platformExteriorCorrection_pos hparams.2.1 hparams.2.2.1
      hxminusa).ne'
  have hW := hasDerivAt_platformExteriorW_x
    (k := terminalPlatformRatio q)
    hxminusa hparams.2.2.1 hbounds.1.ne hcorr
  have hD := hasDerivAt_oneCutExteriorDistance
    (q := q) (u := uMinus q) (by linarith [hu1])
  have hleft := hW.comp (uMinus q) hD
  have hext := hasDerivAt_exteriorFunction_outer hq hq1 hum.1
  have hright : HasDerivAt
      (fun u : ℝ ↦ -exteriorFunction q u / (1 - A q))
      (-outerPartialU q (uMinus q) / (1 - A q)) (uMinus q) := by
    simpa [outerPartialU] using! hext.neg.div_const (1 - A q)
  have hevent :
      (fun u : ℝ ↦
        platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
          (oneCutExteriorDistance q u)) =ᶠ[nhds (uMinus q)]
        (fun u : ℝ ↦ -exteriorFunction q u / (1 - A q)) := by
    filter_upwards [Ioi_mem_nhds hum.1] with u huq
    exact platformExteriorW_terminal_outer hq hqs huq
  have hslope :
      platformExteriorWx (terminalPlatformRatio q) (terminalPlatformEdge q)
            (terminalPlatformXMinus q) *
          (H q * (-1 + ((uMinus q) ^ 2)⁻¹)) =
        -outerPartialU q (uMinus q) / (1 - A q) := by
    change
      platformExteriorWx (terminalPlatformRatio q) (terminalPlatformEdge q)
            (oneCutExteriorDistance q (uMinus q)) *
          (H q * (-1 + ((uMinus q) ^ 2)⁻¹)) =
        -outerPartialU q (uMinus q) / (1 - A q)
    exact hleft.unique (hright.congr_of_eventuallyEq hevent)
  have hinv : ((uMinus q) ^ 2)⁻¹ < 1 := by
    rw [inv_lt_one₀ (sq_pos_of_pos (by linarith [hu1]))]
    nlinarith [hu1]
  have hDneg : H q * (-1 + ((uMinus q) ^ 2)⁻¹) < 0 :=
    mul_neg_of_pos_of_neg (H_pos hq) (by linarith)
  have hrightPos :
      0 < -outerPartialU q (uMinus q) / (1 - A q) :=
    div_pos (neg_pos.mpr (outerPartialU_uMinus_neg hq hqs.le))
      (sub_pos.mpr hA.2)
  by_contra hn
  have hWxNonneg :
      0 ≤ platformExteriorWx (terminalPlatformRatio q) (terminalPlatformEdge q)
          (terminalPlatformXMinus q) := le_of_not_gt hn
  have hprodNonpos := mul_nonpos_of_nonneg_of_nonpos hWxNonneg hDneg.le
  rw [hslope] at hprodNonpos
  linarith

/-- The distance-coordinate gap between the two terminal platform crossings
is exactly the one-cut width `Lambda`. -/
theorem terminalPlatform_crossing_width (q : ℝ) :
    terminalPlatformXPlus q - terminalPlatformXMinus q = Lambda q := by
  have hwidth := zeroPlatformNegativeEndpoints_length q
  unfold zeroPlatformNegativeRightEndpoint
    zeroPlatformNegativeLeftEndpoint at hwidth
  unfold terminalPlatformXPlus terminalPlatformXMinus
  linarith

/-- Bundled terminal crossing data used by the final high-`k` assembly. -/
theorem terminalPlatform_crossing_data
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    terminalPlatformXMinus q < 0 ∧
      0 < terminalPlatformXPlus q ∧
      terminalPlatformXMinus q < terminalPlatformXPlus q ∧
      terminalPlatformXPlus q < terminalPlatformEdge q ∧
      platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
          (terminalPlatformXMinus q) = 0 ∧
      platformExteriorW (terminalPlatformRatio q) (terminalPlatformEdge q)
          (terminalPlatformXPlus q) = 0 ∧
      platformExteriorWx (terminalPlatformRatio q) (terminalPlatformEdge q)
          (terminalPlatformXMinus q) < 0 ∧
      0 < platformExteriorWx (terminalPlatformRatio q) (terminalPlatformEdge q)
          (terminalPlatformXPlus q) ∧
      terminalPlatformXPlus q - terminalPlatformXMinus q = Lambda q := by
  have hbounds := terminalPlatform_crossing_bounds hq hqs
  exact ⟨hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2,
    terminalPlatformXMinus_zero hq hqs,
    terminalPlatformXPlus_zero hq hqs,
    terminalPlatformXMinus_slope_neg hq hqs,
    terminalPlatformXPlus_slope_pos hq hqs,
    terminalPlatform_crossing_width q⟩

/-- The terminal one-cut roots form a checker-independent explicit crossing
certificate, ready for the canonical reference-potential bridge. -/
theorem terminalPlatform_explicitCrossingCertificate
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    PlatformExplicitExteriorCrossingCertificate
      (terminalPlatformRatio q) (terminalPlatformEdge q)
      (terminalPlatformXMinus q) (terminalPlatformXPlus q) := by
  have hdata := terminalPlatform_crossing_data hq hqs
  exact
    { xMinus_neg := hdata.1
      xPlus_pos := hdata.2.1
      xPlus_lt_platform := hdata.2.2.2.1
      xMinus_zero := hdata.2.2.2.2.1
      xPlus_zero := hdata.2.2.2.2.2.1
      xMinus_slope_neg := hdata.2.2.2.2.2.2.1
      xPlus_slope_pos := hdata.2.2.2.2.2.2.2.1 }

end

end Erdos1038
