import ErdosProblems.Erdos1038.HighKTerminalCalibrationAssembly
import ErdosProblems.Erdos1038.HighKCircleCorrectionInterval
import ErdosProblems.Erdos1038.OneCutTailQBox

/-!
# Stable algebra for the terminal platform scalar

The direct platform formulas are badly conditioned as `q → 0`: the ratio
diverges while the capacity vanishes.  This file records exact identities in
the scaled roots `z₊ = q u₊`, `z₋ = q u₋`.  The resulting formulas are
regular at the terminal end and are suitable for rational interval checking.
-/

set_option warningAsError false
set_option maxHeartbeats 4000000

open Set

namespace Erdos1038

noncomputable section

def terminalRaw (q z : ℝ) : ℝ :=
  1 - A q * (1 - q ^ 2) * z / ((1 - z) * (z - q ^ 2))

def terminalPlusWeight (q zp : ℝ) : ℝ :=
  -1 / terminalRaw q zp

def terminalMinusWeight (q zm : ℝ) : ℝ :=
  1 / terminalRaw q zm

def terminalP (q : ℝ) : ℝ :=
  (1 - A q) + 2 * q * A q / (1 + q)

def terminalScalarDenominator (q zp zm : ℝ) : ℝ :=
  2 * terminalP q *
    (terminalPlusWeight q zp + terminalMinusWeight q zm)

def terminalStableQmax (q : ℝ) : ℝ :=
  Real.pi * (1 - A q) / terminalP q

def terminalStableRratio (q zp zm : ℝ) : ℝ :=
  ((1 + q / zp) * terminalPlusWeight q zp +
      (1 + q / zm) * terminalMinusWeight q zm) /
    (2 * (terminalPlusWeight q zp + terminalMinusWeight q zm))

def terminalStableRmax (q zp zm : ℝ) : ℝ :=
  Real.pi * terminalStableRratio q zp zm

theorem four_mul_H_eq_two_sub_terminalPlatformEdge
    {q : ℝ} (hq : 0 < q) :
    4 * H q = 2 - terminalPlatformEdge q := by
  have hqneg : q ≠ -1 := by linarith
  have h := platformCapacity_positiveBufferDistanceLeft_s (q := q) hqneg
  rw [platformCapacity] at h
  change (2 - terminalPlatformEdge q) / 4 = H q at h
  linarith

theorem sqrt_terminalPlatformEdge
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Real.sqrt (terminalPlatformEdge q) = Real.sqrt 2 * s q := by
  have hs : 0 < s q := s_pos hq hq1
  rw [terminalPlatformEdge, positiveBufferDistanceLeft,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs,
    abs_of_pos hs]

theorem terminalRhoZero_eq_q
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    (Real.sqrt 2 - Real.sqrt (terminalPlatformEdge q)) /
        (Real.sqrt 2 + Real.sqrt (terminalPlatformEdge q)) = q := by
  rw [sqrt_terminalPlatformEdge hq hq1, s]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hden : 1 + q ≠ 0 := by linarith
  field_simp [hsqrt.ne', hden]
  ring

theorem platformCrossingScale_terminal
    {q u : ℝ} (hq : 0 < q) (hu : 1 < u) :
    platformCrossingScale (terminalPlatformEdge q)
        (oneCutExteriorDistance q u) = H q * (u ^ 2 - 1) / u := by
  have hq0 : q ≠ 0 := hq.ne'
  have hqneg : q ≠ -1 := by linarith
  have hu0 : u ≠ 0 := by linarith
  have hleft := positiveBufferDistanceLeft_sub_oneCutExteriorDistance
    hq0 hqneg hu0
  have hright := two_sub_oneCutExteriorDistance hq0 hqneg hu0
  have hH : 0 < H q := H_pos hq
  have hrhs : 0 < H q * (u ^ 2 - 1) / u := by
    apply div_pos
    · exact mul_pos hH (by nlinarith)
    · linarith
  rw [platformCrossingScale, terminalPlatformEdge, hleft, hright]
  rw [show
      (H q * (u - 1) ^ 2 / u) * (H q * (u + 1) ^ 2 / u) =
        (H q * (u ^ 2 - 1) / u) ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hrhs]

theorem platformRho_terminal
    {q u : ℝ} (hq : 0 < q) (hu : 1 < u) :
    platformRho (terminalPlatformEdge q) (oneCutExteriorDistance q u) =
      1 / u := by
  have hq0 : q ≠ 0 := hq.ne'
  have hqneg : q ≠ -1 := by linarith
  have hu0 : u ≠ 0 := by linarith
  have hleft := positiveBufferDistanceLeft_sub_oneCutExteriorDistance
    hq0 hqneg hu0
  have hright := two_sub_oneCutExteriorDistance hq0 hqneg hu0
  have hscale := platformCrossingScale_terminal hq hu
  have hH0 : H q ≠ 0 := (H_pos hq).ne'
  have hcenter :
      platformCenter (terminalPlatformEdge q) - oneCutExteriorDistance q u =
        H q * (u ^ 2 + 1) / u := by
    calc
      platformCenter (terminalPlatformEdge q) - oneCutExteriorDistance q u =
          ((positiveBufferDistanceLeft (s q) -
              oneCutExteriorDistance q u) +
            (2 - oneCutExteriorDistance q u)) / 2 := by
              unfold platformCenter terminalPlatformEdge
              ring
      _ = H q * (u ^ 2 + 1) / u := by
        rw [hleft, hright]
        ring
  have hradius : platformRadius (terminalPlatformEdge q) = 2 * H q := by
    unfold platformRadius
    nlinarith [four_mul_H_eq_two_sub_terminalPlatformEdge hq]
  rw [platformRho, hradius, hcenter, hscale]
  field_simp [hH0, hu0]
  ring

def terminalRawU (q u : ℝ) : ℝ :=
  1 - A q * (1 - q ^ 2) * u / ((1 - q * u) * (u - q))

theorem terminalRaw_mul (q u : ℝ) (hq : q ≠ 0) :
    terminalRaw q (q * u) = terminalRawU q u := by
  unfold terminalRaw terminalRawU
  field_simp [hq]

/-- Cancellation-free normalized slope identity on either terminal branch. -/
theorem platformExteriorWx_terminal
    {q u : ℝ} (hq : 0 < q) (hqs : q < qSoft) (hu : 1 < u)
    (huinv : u ≠ q⁻¹) :
    platformExteriorWx (terminalPlatformRatio q) (terminalPlatformEdge q)
        (oneCutExteriorDistance q u) =
      -terminalRawU q u /
        ((1 - A q) *
          platformCrossingScale (terminalPlatformEdge q)
            (oneCutExteriorDistance q u)) := by
  have hqdom : q ∈ Ioo (0 : ℝ) qCeiling :=
    q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hq1 : q < 1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hA := A_mem_Ioo_of_mem_Ioo hqdom
  have hq0 : q ≠ 0 := hq.ne'
  have hqneg : q ≠ -1 := by linarith
  have hu0 : u ≠ 0 := by linarith
  have huq : u - q ≠ 0 := by linarith
  have hqu : 1 - q * u ≠ 0 := by
    intro hzero
    apply huinv
    rw [← one_div]
    apply (eq_div_iff hq0).2
    have hmul : q * u = 1 := by linarith
    simpa [mul_comm] using! hmul
  have hxFactor := oneCutExteriorDistance_factor hq0 hqneg hu0
  have hx0 : oneCutExteriorDistance q u ≠ 0 := by
    rw [hxFactor]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (H_pos hq).ne' huq) hqu)
      (mul_ne_zero hq0 hu0)
  have hscale := platformCrossingScale_terminal hq hu
  have hscale0 :
      platformCrossingScale (terminalPlatformEdge q)
        (oneCutExteriorDistance q u) ≠ 0 := by
    rw [hscale]
    exact div_ne_zero (mul_ne_zero (H_pos hq).ne' (by nlinarith)) hu0
  have hcorr : 1 - q * (1 / u) ≠ 0 := by
    rw [show 1 - q * (1 / u) = (u - q) / u by
      field_simp [hu0]]
    exact div_ne_zero huq hu0
  rw [platformExteriorWx_eq, terminalPlatformRatio,
    terminalRhoZero_eq_q hq hq1, platformRho_terminal hq hu]
  rw [hscale]
  unfold positiveBufferRatio terminalRawU
  field_simp [hx0, hscale0, hA.2.ne', hu0, hcorr, huq, hqu]
  rw [hxFactor]
  field_simp [hq0, hu0, huq, hqu, (H_pos hq).ne']
  have hA0 : 1 - A q ≠ 0 := by linarith [hA.2]
  have hu2 : -1 + u ^ 2 ≠ 0 := by nlinarith
  have hu2' : u ^ 2 - 1 ≠ 0 := by nlinarith
  have hcombo : -1 + (A q - A q * u ^ 2) + u ^ 2 ≠ 0 := by
    rw [show -1 + (A q - A q * u ^ 2) + u ^ 2 =
      (1 - A q) * (u ^ 2 - 1) by ring]
    exact mul_ne_zero hA0 (by nlinarith)
  field_simp [hA0, hu2, hu2', hcombo, hqu]
  ring

theorem terminalRaw_plus_ne_zero
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    terminalRaw q (zPlus q) ≠ 0 := by
  have hup := uPlus_spec hq hqs
  have hformula := platformExteriorWx_terminal hq hqs hup.1 hup.2.1.ne
  have hwx := (terminalPlatformXPlus_slope_pos hq hqs).ne'
  have hq0 := hq.ne'
  rw [zPlus, terminalRaw_mul q (uPlus q) hq0]
  intro hraw
  rw [hraw] at hformula
  simp only [neg_zero, zero_div] at hformula
  exact hwx hformula

theorem terminalRaw_minus_ne_zero
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    terminalRaw q (zMinus q) ≠ 0 := by
  have hum := uMinus_spec hq hqs.le
  have hu1 : 1 < uMinus q :=
    (one_lt_inv_q hq (q_lt_one_of_pos_le_qSoft hq hqs.le)).trans hum.1
  have hformula := platformExteriorWx_terminal hq hqs hu1 hum.1.ne'
  have hwx := (terminalPlatformXMinus_slope_neg hq hqs).ne
  have hq0 := hq.ne'
  rw [zMinus, terminalRaw_mul q (uMinus q) hq0]
  intro hraw
  rw [hraw] at hformula
  simp only [neg_zero, zero_div] at hformula
  exact hwx hformula

theorem terminalPlatformSigmaPlus_eq_weight
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    terminalPlatformSigmaPlus q =
      (1 - A q) *
        platformCrossingScale (terminalPlatformEdge q)
          (terminalPlatformXPlus q) * terminalPlusWeight q (zPlus q) := by
  have hup := uPlus_spec hq hqs
  have hformula := platformExteriorWx_terminal hq hqs hup.1 hup.2.1.ne
  have hq0 := hq.ne'
  change 1 / platformExteriorWx (terminalPlatformRatio q)
      (terminalPlatformEdge q) (oneCutExteriorDistance q (uPlus q)) = _
  rw [hformula, ← terminalRaw_mul q (uPlus q) hq0]
  rw [show zPlus q = q * uPlus q by rfl]
  simp only [terminalPlatformXPlus]
  unfold terminalPlusWeight
  field_simp [terminalRaw_plus_ne_zero hq hqs]

theorem terminalPlatformSigmaMinus_eq_weight
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    terminalPlatformSigmaMinus q =
      (1 - A q) *
        platformCrossingScale (terminalPlatformEdge q)
          (terminalPlatformXMinus q) * terminalMinusWeight q (zMinus q) := by
  have hum := uMinus_spec hq hqs.le
  have hu1 : 1 < uMinus q :=
    (one_lt_inv_q hq (q_lt_one_of_pos_le_qSoft hq hqs.le)).trans hum.1
  have hformula := platformExteriorWx_terminal hq hqs hu1 hum.1.ne'
  have hq0 := hq.ne'
  change -1 / platformExteriorWx (terminalPlatformRatio q)
      (terminalPlatformEdge q) (oneCutExteriorDistance q (uMinus q)) = _
  rw [hformula, ← terminalRaw_mul q (uMinus q) hq0]
  rw [show zMinus q = q * uMinus q by rfl]
  simp only [terminalPlatformXMinus]
  unfold terminalMinusWeight
  field_simp [terminalRaw_minus_ne_zero hq hqs]

theorem sqrt_two_mul_terminalPlatformEdge
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    Real.sqrt (2 * terminalPlatformEdge q) = 2 * s q := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hs := s_pos hq hq1
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    sqrt_terminalPlatformEdge hq hq1]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]

theorem platformAPi_terminal_eq
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformAPi (terminalPlatformRatio q) (terminalPlatformEdge q) =
      terminalP q / (1 - A q) := by
  have hA := A_mem_Ioo_of_mem_Ioo
    (q_mem_Ioo_of_pos_le_qSoft hq hqs.le)
  have hA0 : 1 - A q ≠ 0 := by linarith [hA.2]
  have hqden : 1 + q ≠ 0 := by linarith
  rw [platformAPi, platformAngularDensity, platformAngularDistance_pi,
    platformDensityCoefficient, sqrt_two_mul_terminalPlatformEdge hq hqs]
  unfold terminalPlatformRatio positiveBufferRatio terminalP s
  field_simp [hA0, hqden]
  ring

private theorem crossingScale_sq_div_left
    {a x : ℝ} (hx : x < a) (ha2 : a < 2) :
    platformCrossingScale a x ^ 2 / (a - x) = 2 - x := by
  rw [platformCrossingScale_sq hx ha2]
  field_simp [(sub_pos.mpr hx).ne']

private theorem crossingScale_sq_div_right
    {a x : ℝ} (hx : x < a) (ha2 : a < 2) :
    platformCrossingScale a x ^ 2 / (2 - x) = a - x := by
  rw [platformCrossingScale_sq hx ha2]
  field_simp [(sub_pos.mpr (hx.trans ha2)).ne']

theorem terminal_two_sub_x_sub_scale
    {q u : ℝ} (hq : 0 < q) (hu : 1 < u) :
    2 - oneCutExteriorDistance q u -
        platformCrossingScale (terminalPlatformEdge q)
          (oneCutExteriorDistance q u) =
      2 * H q * (1 + 1 / u) := by
  have hq0 : q ≠ 0 := hq.ne'
  have hqneg : q ≠ -1 := by linarith
  have hu0 : u ≠ 0 := by linarith
  rw [two_sub_oneCutExteriorDistance hq0 hqneg hu0,
    platformCrossingScale_terminal hq hu]
  field_simp [hu0]
  ring

theorem platformBPi_terminal_eq
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformBPi (terminalPlatformEdge q)
        (terminalPlatformXMinus q) (terminalPlatformXPlus q)
        (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q) =
      4 * H q * (1 - A q) *
        (terminalPlusWeight q (zPlus q) +
          terminalMinusWeight q (zMinus q)) := by
  have hp := terminalPlatform_parameters hq hqs
  have hb := terminalPlatform_crossing_bounds hq hqs
  have hxm : terminalPlatformXMinus q < terminalPlatformEdge q :=
    hb.1.trans hp.2.1
  have hxp : terminalPlatformXPlus q < terminalPlatformEdge q := hb.2.2.2
  have ha2 : terminalPlatformEdge q < 2 := hp.2.2.1
  have hmLeft :
      (1 - A q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXMinus q) *
            terminalMinusWeight q (zMinus q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXMinus q) /
          (terminalPlatformEdge q - terminalPlatformXMinus q) =
        (1 - A q) * terminalMinusWeight q (zMinus q) *
          (2 - terminalPlatformXMinus q) := by
    calc
      _ = (1 - A q) * terminalMinusWeight q (zMinus q) *
          (platformCrossingScale (terminalPlatformEdge q)
            (terminalPlatformXMinus q) ^ 2 /
              (terminalPlatformEdge q - terminalPlatformXMinus q)) := by ring
      _ = _ := by rw [crossingScale_sq_div_left hxm ha2]
  have hpLeft :
      (1 - A q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXPlus q) *
            terminalPlusWeight q (zPlus q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXPlus q) /
          (terminalPlatformEdge q - terminalPlatformXPlus q) =
        (1 - A q) * terminalPlusWeight q (zPlus q) *
          (2 - terminalPlatformXPlus q) := by
    calc
      _ = (1 - A q) * terminalPlusWeight q (zPlus q) *
          (platformCrossingScale (terminalPlatformEdge q)
            (terminalPlatformXPlus q) ^ 2 /
              (terminalPlatformEdge q - terminalPlatformXPlus q)) := by ring
      _ = _ := by rw [crossingScale_sq_div_left hxp ha2]
  have hmRight :
      (1 - A q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXMinus q) *
            terminalMinusWeight q (zMinus q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXMinus q) /
          (2 - terminalPlatformXMinus q) =
        (1 - A q) * terminalMinusWeight q (zMinus q) *
          (terminalPlatformEdge q - terminalPlatformXMinus q) := by
    calc
      _ = (1 - A q) * terminalMinusWeight q (zMinus q) *
          (platformCrossingScale (terminalPlatformEdge q)
            (terminalPlatformXMinus q) ^ 2 /
              (2 - terminalPlatformXMinus q)) := by ring
      _ = _ := by rw [crossingScale_sq_div_right hxm ha2]
  have hpRight :
      (1 - A q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXPlus q) *
            terminalPlusWeight q (zPlus q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXPlus q) /
          (2 - terminalPlatformXPlus q) =
        (1 - A q) * terminalPlusWeight q (zPlus q) *
          (terminalPlatformEdge q - terminalPlatformXPlus q) := by
    calc
      _ = (1 - A q) * terminalPlusWeight q (zPlus q) *
          (platformCrossingScale (terminalPlatformEdge q)
            (terminalPlatformXPlus q) ^ 2 /
              (2 - terminalPlatformXPlus q)) := by ring
      _ = _ := by rw [crossingScale_sq_div_right hxp ha2]
  rw [platformBPi, platformAngularAdjointDensity,
    platformAngularDistance_pi, adjointNumerator, adjointNormalization,
    terminalPlatformSigmaMinus_eq_weight hq hqs,
    terminalPlatformSigmaPlus_eq_weight hq hqs]
  rw [hmLeft, hpLeft, hmRight, hpRight]
  rw [four_mul_H_eq_two_sub_terminalPlatformEdge hq]
  ring

theorem platformAdjointMass_terminal_eq
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformAdjointMass (terminalPlatformEdge q)
        (terminalPlatformXMinus q) (terminalPlatformXPlus q)
        (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q) =
      2 * H q * (1 - A q) *
        ((1 + q / zPlus q) * terminalPlusWeight q (zPlus q) +
          (1 + q / zMinus q) * terminalMinusWeight q (zMinus q)) := by
  have hp := terminalPlatform_parameters hq hqs
  have hb := terminalPlatform_crossing_bounds hq hqs
  have hxm : terminalPlatformXMinus q < terminalPlatformEdge q :=
    hb.1.trans hp.2.1
  have hxp : terminalPlatformXPlus q < terminalPlatformEdge q := hb.2.2.2
  have ha2 : terminalPlatformEdge q < 2 := hp.2.2.1
  have hup := uPlus_spec hq hqs
  have hum := uMinus_spec hq hqs.le
  have hu1 : 1 < uMinus q :=
    (one_lt_inv_q hq (q_lt_one_of_pos_le_qSoft hq hqs.le)).trans hum.1
  have hmLeft :
      (1 - A q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXMinus q) *
            terminalMinusWeight q (zMinus q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXMinus q) /
          (terminalPlatformEdge q - terminalPlatformXMinus q) =
        (1 - A q) * terminalMinusWeight q (zMinus q) *
          (2 - terminalPlatformXMinus q) := by
    calc
      _ = (1 - A q) * terminalMinusWeight q (zMinus q) *
          (platformCrossingScale (terminalPlatformEdge q)
            (terminalPlatformXMinus q) ^ 2 /
              (terminalPlatformEdge q - terminalPlatformXMinus q)) := by ring
      _ = _ := by rw [crossingScale_sq_div_left hxm ha2]
  have hpLeft :
      (1 - A q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXPlus q) *
            terminalPlusWeight q (zPlus q) *
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXPlus q) /
          (terminalPlatformEdge q - terminalPlatformXPlus q) =
        (1 - A q) * terminalPlusWeight q (zPlus q) *
          (2 - terminalPlatformXPlus q) := by
    calc
      _ = (1 - A q) * terminalPlusWeight q (zPlus q) *
          (platformCrossingScale (terminalPlatformEdge q)
            (terminalPlatformXPlus q) ^ 2 /
              (terminalPlatformEdge q - terminalPlatformXPlus q)) := by ring
      _ = _ := by rw [crossingScale_sq_div_left hxp ha2]
  rw [platformAdjointMass, adjointNormalization,
    terminalPlatformSigmaMinus_eq_weight hq hqs,
    terminalPlatformSigmaPlus_eq_weight hq hqs]
  rw [hmLeft, hpLeft]
  have hmDiff : 2 - terminalPlatformXMinus q -
      platformCrossingScale (terminalPlatformEdge q)
        (terminalPlatformXMinus q) =
        2 * H q * (1 + 1 / uMinus q) := by
    simpa [terminalPlatformXMinus] using!
      terminal_two_sub_x_sub_scale hq hu1
  have hpDiff : 2 - terminalPlatformXPlus q -
      platformCrossingScale (terminalPlatformEdge q)
        (terminalPlatformXPlus q) =
        2 * H q * (1 + 1 / uPlus q) := by
    simpa [terminalPlatformXPlus] using!
      terminal_two_sub_x_sub_scale hq hup.1
  have hzp : zPlus q = q * uPlus q := rfl
  have hzm : zMinus q = q * uMinus q := rfl
  calc
    _ = (1 - A q) * terminalMinusWeight q (zMinus q) *
          (2 - terminalPlatformXMinus q -
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXMinus q)) +
        (1 - A q) * terminalPlusWeight q (zPlus q) *
          (2 - terminalPlatformXPlus q -
            platformCrossingScale (terminalPlatformEdge q)
              (terminalPlatformXPlus q)) := by ring
    _ = (1 - A q) * terminalMinusWeight q (zMinus q) *
          (2 * H q * (1 + 1 / uMinus q)) +
        (1 - A q) * terminalPlusWeight q (zPlus q) *
          (2 * H q * (1 + 1 / uPlus q)) := by rw [hmDiff, hpDiff]
    _ = _ := by
      rw [hzp, hzm]
      field_simp [hq.ne', (by linarith [hup.1] : uPlus q ≠ 0),
        (by linarith [hu1] : uMinus q ≠ 0)]
      ring

theorem terminalP_pos
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < terminalP q := by
  have hA := A_mem_Ioo_of_mem_Ioo
    (q_mem_Ioo_of_pos_le_qSoft hq hqs.le)
  have hden : 0 < 1 + q := by linarith
  unfold terminalP
  have hfirst : 0 < 1 - A q := sub_pos.mpr hA.2
  have hsecond : 0 < 2 * q * A q / (1 + q) :=
    div_pos (mul_pos (mul_pos (by norm_num) hq) hA.1) hden
  linarith

theorem terminalWeightSum_pos
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < terminalPlusWeight q (zPlus q) +
      terminalMinusWeight q (zMinus q) := by
  have hp := terminalPlatform_parameters hq hqs
  have hb := terminalPlatform_crossing_bounds hq hqs
  have hbpi : 0 < platformBPi (terminalPlatformEdge q)
      (terminalPlatformXMinus q) (terminalPlatformXPlus q)
      (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q) :=
    platformBPi_pos (hb.1.trans hp.2.1) hb.2.2.2
      (terminalPlatformSigmaMinus_pos hq hqs)
      (terminalPlatformSigmaPlus_pos hq hqs) hp.2.2.1
  rw [platformBPi_terminal_eq hq hqs] at hbpi
  have hA := A_mem_Ioo_of_mem_Ioo
    (q_mem_Ioo_of_pos_le_qSoft hq hqs.le)
  have hcoef : 0 < 4 * H q * (1 - A q) :=
    mul_pos (mul_pos (by norm_num) (H_pos hq)) (sub_pos.mpr hA.2)
  rcases mul_pos_iff.mp hbpi with hpos | hneg
  · exact hpos.2
  · exact (lt_asymm hcoef hneg.1).elim

theorem terminalScalarDenominator_pos
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    0 < terminalScalarDenominator q (zPlus q) (zMinus q) := by
  unfold terminalScalarDenominator
  positivity [terminalP_pos hq hqs, terminalWeightSum_pos hq hqs]

theorem platformReferenceCircleRadiusCap_terminal_eq
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformReferenceCircleRadiusCap
        (terminalPlatformRatio q) (terminalPlatformEdge q) =
      terminalStableQmax q := by
  have hA := A_mem_Ioo_of_mem_Ioo
    (q_mem_Ioo_of_pos_le_qSoft hq hqs.le)
  have hA0 : 1 - A q ≠ 0 := by linarith [hA.2]
  have hP0 := (terminalP_pos hq hqs).ne'
  unfold platformReferenceCircleRadiusCap terminalStableQmax
  rw [platformAPi_terminal_eq hq hqs]
  field_simp [hA0, hP0]

theorem platformAdjointCircleRadiusCap_terminal_eq
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    platformAdjointCircleRadiusCap (terminalPlatformEdge q)
        (terminalPlatformXMinus q) (terminalPlatformXPlus q)
        (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q) =
      terminalStableRmax q (zPlus q) (zMinus q) := by
  have hA := A_mem_Ioo_of_mem_Ioo
    (q_mem_Ioo_of_pos_le_qSoft hq hqs.le)
  have hA0 : 1 - A q ≠ 0 := by linarith [hA.2]
  have hH0 := (H_pos hq).ne'
  have hsum0 := (terminalWeightSum_pos hq hqs).ne'
  unfold platformAdjointCircleRadiusCap terminalStableRmax
    terminalStableRratio
  rw [platformAdjointMass_terminal_eq hq hqs,
    platformBPi_terminal_eq hq hqs]
  field_simp [hA0, hH0, hsum0]
  ring

theorem terminalPrefactorArgument_eq_inv
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    2 * platformCapacity (terminalPlatformEdge q) /
        (platformAPi (terminalPlatformRatio q) (terminalPlatformEdge q) *
          platformBPi (terminalPlatformEdge q)
            (terminalPlatformXMinus q) (terminalPlatformXPlus q)
            (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q)) =
      (terminalScalarDenominator q (zPlus q) (zMinus q))⁻¹ := by
  have hqneg : q ≠ -1 := by linarith
  have hA := A_mem_Ioo_of_mem_Ioo
    (q_mem_Ioo_of_pos_le_qSoft hq hqs.le)
  have hA0 : 1 - A q ≠ 0 := by linarith [hA.2]
  have hH0 := (H_pos hq).ne'
  have hP0 := (terminalP_pos hq hqs).ne'
  have hsum0 := (terminalWeightSum_pos hq hqs).ne'
  have hcap : platformCapacity (terminalPlatformEdge q) = H q := by
    simpa [terminalPlatformEdge] using!
      platformCapacity_positiveBufferDistanceLeft_s hqneg
  rw [hcap, platformAPi_terminal_eq hq hqs,
    platformBPi_terminal_eq hq hqs]
  unfold terminalScalarDenominator
  field_simp [hA0, hH0, hP0, hsum0]
  ring

theorem terminalPrefactor_eq
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    Real.log
        (2 * platformCapacity (terminalPlatformEdge q) /
          (platformAPi (terminalPlatformRatio q) (terminalPlatformEdge q) *
            platformBPi (terminalPlatformEdge q)
              (terminalPlatformXMinus q) (terminalPlatformXPlus q)
              (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q))) =
      -Real.log (terminalScalarDenominator q (zPlus q) (zMinus q)) := by
  rw [terminalPrefactorArgument_eq_inv hq hqs, Real.log_inv]

theorem terminalCircleRectangleBase_eq
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    circleRectangleBase
        (platformCapacity (terminalPlatformEdge q))
        (platformAPi (terminalPlatformRatio q) (terminalPlatformEdge q))
        (platformBPi (terminalPlatformEdge q)
          (terminalPlatformXMinus q) (terminalPlatformXPlus q)
          (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q))
        (platformReferenceCircleRadiusCap
          (terminalPlatformRatio q) (terminalPlatformEdge q))
        (platformAdjointCircleRadiusCap (terminalPlatformEdge q)
          (terminalPlatformXMinus q) (terminalPlatformXPlus q)
          (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q)) =
      -Real.log (terminalScalarDenominator q (zPlus q) (zMinus q)) +
        circleCorrection (terminalStableQmax q) +
        circleCorrection (terminalStableRmax q (zPlus q) (zMinus q)) := by
  unfold circleRectangleBase
  rw [terminalPrefactor_eq hq hqs,
    platformReferenceCircleRadiusCap_terminal_eq hq hqs,
    platformAdjointCircleRadiusCap_terminal_eq hq hqs]

theorem terminalStableQmax_mem_Ioc
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    terminalStableQmax q ∈ Ioc 0 Real.pi := by
  have hp := terminalPlatform_parameters hq hqs
  have hapi : 0 < platformAPi
      (terminalPlatformRatio q) (terminalPlatformEdge q) :=
    platformAPi_pos hp.1 hp.2.1 hp.2.2.1.le
  rw [← platformReferenceCircleRadiusCap_terminal_eq hq hqs]
  constructor
  · unfold platformReferenceCircleRadiusCap
    exact div_pos Real.pi_pos hapi
  · unfold platformReferenceCircleRadiusCap
    rw [div_le_iff₀ hapi]
    nlinarith [one_le_platformAPi hp.1 hp.2.1 hp.2.2.1.le,
      Real.pi_pos]

theorem terminalStableRmax_mem_Ioc
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) :
    terminalStableRmax q (zPlus q) (zMinus q) ∈ Ioc 0 Real.pi := by
  have hp := terminalPlatform_parameters hq hqs
  have hb := terminalPlatform_crossing_bounds hq hqs
  have hxm : terminalPlatformXMinus q < terminalPlatformEdge q :=
    hb.1.trans hp.2.1
  have hxp : terminalPlatformXPlus q < terminalPlatformEdge q := hb.2.2.2
  have hsm := terminalPlatformSigmaMinus_pos hq hqs
  have hsp := terminalPlatformSigmaPlus_pos hq hqs
  have hbpi : 0 < platformBPi (terminalPlatformEdge q)
      (terminalPlatformXMinus q) (terminalPlatformXPlus q)
      (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q) :=
    platformBPi_pos hxm hxp hsm hsp hp.2.2.1
  have hmass : 0 < platformAdjointMass (terminalPlatformEdge q)
      (terminalPlatformXMinus q) (terminalPlatformXPlus q)
      (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q) :=
    platformAdjointMass_pos hxm hxp hsm hsp hp.2.2.1
  rw [← platformAdjointCircleRadiusCap_terminal_eq hq hqs]
  constructor
  · unfold platformAdjointCircleRadiusCap
    exact div_pos (mul_pos Real.pi_pos hmass) hbpi
  · have hfull := platformAdjointCircleRadius_mem_Icc
      hxm hxp hsm hsp hp.2.2.1
      (show (0 : ℝ) ≤ 0 by rfl) Real.pi_pos.le le_rfl
    rw [platformAdjointCircleRadius,
      integral_platformNormalizedAdjointDensity hxm hxp hp.2.2.1] at hfull
    simpa only [platformAdjointCircleRadiusCap] using! hfull.2

theorem terminalCircleRectangleBase_pos_of_denominator_lt_one
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    (hD : terminalScalarDenominator q (zPlus q) (zMinus q) < 1) :
    0 < circleRectangleBase
        (platformCapacity (terminalPlatformEdge q))
        (platformAPi (terminalPlatformRatio q) (terminalPlatformEdge q))
        (platformBPi (terminalPlatformEdge q)
          (terminalPlatformXMinus q) (terminalPlatformXPlus q)
          (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q))
        (platformReferenceCircleRadiusCap
          (terminalPlatformRatio q) (terminalPlatformEdge q))
        (platformAdjointCircleRadiusCap (terminalPlatformEdge q)
          (terminalPlatformXMinus q) (terminalPlatformXPlus q)
          (terminalPlatformSigmaMinus q) (terminalPlatformSigmaPlus q)) := by
  rw [terminalCircleRectangleBase_eq hq hqs]
  have hlog : Real.log
      (terminalScalarDenominator q (zPlus q) (zMinus q)) < 0 :=
    Real.log_neg (terminalScalarDenominator_pos hq hqs) hD
  have hqmax := terminalStableQmax_mem_Ioc hq hqs
  have hrmax := terminalStableRmax_mem_Ioc hq hqs
  have hqcorrection := circleCorrection_nonneg hqmax.1 hqmax.2
  have hrcorrection := circleCorrection_nonneg hrmax.1 hrmax.2
  linarith

end


end Erdos1038
