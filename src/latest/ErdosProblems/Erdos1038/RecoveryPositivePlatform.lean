import ErdosProblems.Erdos1038.PlatformPotential
import ErdosProblems.Erdos1038.WeakPotentialL1
import ErdosProblems.Erdos1038.OneCutElementary

/-!
# Positive-platform recovery measures

This file packages the positive-buffer family from Section 9 of the
manuscript in terms of the constant-platform probability already constructed
in `ConstantPlatformMeasure`.  The distance coordinate is `d = t + 1`.
For a fixed `s` and endpoint mass `alpha`, its parameters are

* left distance endpoint `2 s^2`, and
* platform ratio `alpha / (1 - alpha)`.

The elementary identities below verify both the nonnegativity threshold and
the normalization.  We then translate the continuous probability from the
distance interval to the root interval and add the endpoint atom at `-1`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace Erdos1038

noncomputable section

/-- Left endpoint of the continuous support in the distance coordinate
`d = t + 1`. -/
def positiveBufferDistanceLeft (s : ℝ) : ℝ := 2 * s ^ 2

/-- Ratio between the endpoint atom and the continuous mass. -/
def positiveBufferRatio (alpha : ℝ) : ℝ := alpha / (1 - alpha)

lemma positiveBufferDistanceLeft_pos {s : ℝ} (hs : 0 < s) :
    0 < positiveBufferDistanceLeft s := by
  simp only [positiveBufferDistanceLeft]
  positivity

lemma positiveBufferDistanceLeft_lt_two {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) : positiveBufferDistanceLeft s < 2 := by
  simp only [positiveBufferDistanceLeft]
  have hprod : 0 < (1 - s) * (1 + s) :=
    mul_pos (sub_pos.mpr hs1) (by linarith)
  nlinarith

lemma positiveBufferRatio_nonneg {alpha : ℝ} (halpha : 0 ≤ alpha)
    (halpha1 : alpha < 1) : 0 ≤ positiveBufferRatio alpha := by
  exact div_nonneg halpha (sub_nonneg.mpr halpha1.le)

lemma positiveBufferRatio_add_one {alpha : ℝ} (halpha1 : alpha < 1) :
    positiveBufferRatio alpha + 1 = 1 / (1 - alpha) := by
  unfold positiveBufferRatio
  field_simp [(sub_pos.mpr halpha1).ne']
  ring

lemma positiveBufferRatio_div_add_one {alpha : ℝ} (halpha1 : alpha < 1) :
    positiveBufferRatio alpha / (positiveBufferRatio alpha + 1) = alpha := by
  rw [positiveBufferRatio_add_one halpha1]
  unfold positiveBufferRatio
  field_simp [(sub_pos.mpr halpha1).ne']

lemma platformThreshold_positiveBufferRatio {alpha : ℝ} (halpha1 : alpha < 1) :
    platformThreshold (positiveBufferRatio alpha) = 2 * alpha ^ 2 := by
  rw [platformThreshold, positiveBufferRatio_div_add_one halpha1]

lemma positiveBuffer_threshold_le {s alpha : ℝ} (hs : 0 ≤ s)
    (hs1 : s < 1) (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    platformThreshold (positiveBufferRatio alpha) ≤
      positiveBufferDistanceLeft s := by
  have halpha1 : alpha < 1 := halphas.trans_lt hs1
  rw [platformThreshold_positiveBufferRatio halpha1]
  simp only [positiveBufferDistanceLeft]
  nlinarith [(sq_le_sq₀ halpha hs).2 halphas]

lemma one_sub_mul_positiveBufferRatio {alpha : ℝ} (halpha1 : alpha < 1) :
    (1 - alpha) * positiveBufferRatio alpha = alpha := by
  unfold positiveBufferRatio
  field_simp [(sub_pos.mpr halpha1).ne']

lemma platformCapacity_positiveBufferDistanceLeft (s : ℝ) :
    platformCapacity (positiveBufferDistanceLeft s) = (1 - s ^ 2) / 2 := by
  simp only [platformCapacity, positiveBufferDistanceLeft]
  ring

lemma platformD0_positiveBufferDistanceLeft {s : ℝ} (hs : 0 ≤ s) :
    platformD0 (positiveBufferDistanceLeft s) = (1 + s) ^ 2 / 2 := by
  have hsqrt : Real.sqrt (2 * positiveBufferDistanceLeft s) = 2 * s := by
    rw [positiveBufferDistanceLeft]
    have : 2 * (2 * s ^ 2) = (2 * s) ^ 2 := by ring
    rw [this, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * s)]
  rw [platformD0, hsqrt]
  simp only [positiveBufferDistanceLeft]
  ring

lemma platformCapacity_positiveBufferDistanceLeft_s
    {q : ℝ} (hq : q ≠ -1) :
    platformCapacity (positiveBufferDistanceLeft (s q)) = H q := by
  rw [platformCapacity_positiveBufferDistanceLeft,
    H_eq_half_one_sub_s_sq q hq]

lemma platformD0_positiveBufferDistanceLeft_s
    {q : ℝ} (hq : 0 < q) (hqOne : q < 1) :
    platformD0 (positiveBufferDistanceLeft (s q)) = H q / q := by
  have hq1 : q ≠ -1 := by linarith
  have hsnonneg : 0 ≤ s q := by
    rw [s]
    exact div_nonneg (by linarith) (by linarith)
  rw [platformD0_positiveBufferDistanceLeft hsnonneg, one_add_s q hq1, H]
  field_simp [hq.ne', (by linarith : (1 + q) ≠ 0)]

/-- The continuous positive-buffer probability in the distance coordinate. -/
def positiveBufferContinuousDistanceMeasure (s alpha : ℝ) : Measure ℝ :=
  platformConstantReferenceMeasure (positiveBufferRatio alpha)
    (positiveBufferDistanceLeft s)

theorem isProbabilityMeasure_positiveBufferContinuousDistanceMeasure
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    IsProbabilityMeasure (positiveBufferContinuousDistanceMeasure s alpha) := by
  apply isProbabilityMeasure_platformConstantReferenceMeasure
  · exact positiveBufferRatio_nonneg halpha (halphas.trans_lt hs1)
  · exact positiveBufferDistanceLeft_pos hs
  · exact (positiveBufferDistanceLeft_lt_two hs hs1).le
  · exact positiveBuffer_threshold_le hs.le hs1 halpha halphas

/-- Translation from distance coordinates back to root coordinates. -/
def positiveBufferRootCoordinate (d : ℝ) : ℝ := d - 1

/-- The translated continuous part, normalized to have mass one. -/
def positiveBufferContinuousRootMeasure (s alpha : ℝ) : Measure ℝ :=
  Measure.map positiveBufferRootCoordinate
    (positiveBufferContinuousDistanceMeasure s alpha)

theorem isProbabilityMeasure_positiveBufferContinuousRootMeasure
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    IsProbabilityMeasure (positiveBufferContinuousRootMeasure s alpha) := by
  letI : IsProbabilityMeasure (positiveBufferContinuousDistanceMeasure s alpha) :=
    isProbabilityMeasure_positiveBufferContinuousDistanceMeasure hs hs1 halpha halphas
  exact Measure.isProbabilityMeasure_map (by
    unfold positiveBufferRootCoordinate
    fun_prop)

theorem positiveBufferContinuousRootMeasure_compl_support
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    positiveBufferContinuousRootMeasure s alpha
        (Icc (positiveBufferDistanceLeft s - 1) 1)ᶜ = 0 := by
  have hmap : Measurable positiveBufferRootCoordinate := by
    unfold positiveBufferRootCoordinate
    fun_prop
  rw [positiveBufferContinuousRootMeasure,
    Measure.map_apply hmap measurableSet_Icc.compl]
  have hpreimage :
      positiveBufferRootCoordinate ⁻¹'
          (Icc (positiveBufferDistanceLeft s - 1) 1)ᶜ =
        (Icc (positiveBufferDistanceLeft s) 2)ᶜ := by
    ext d
    simp only [mem_preimage, mem_compl_iff, mem_Icc,
      positiveBufferRootCoordinate]
    constructor <;> intro h hIcc
    · apply h
      constructor <;> linarith [hIcc.1, hIcc.2]
    · apply h
      constructor <;> linarith [hIcc.1, hIcc.2]
  rw [hpreimage]
  exact platformConstantReferenceMeasure_compl_Icc
    (positiveBufferRatio alpha) (positiveBufferDistanceLeft_lt_two hs hs1).le

/-- The logarithmic kernel is integrable against every nonnegative
constant-platform reference measure.  This is the integrability fact needed
to split the atom and continuous part of the positive-buffer potential. -/
theorem integrable_platformConstantReferenceMeasure_log_kernel
    {k a d : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Integrable (fun e : ℝ ↦ Real.log |d - e|)
      (platformConstantReferenceMeasure k a) := by
  let G : ℝ → ℝ := fun e ↦ Real.log |d - e|
  let rho : ℝ → ℝ := fun theta ↦
    (1 / Real.pi) * platformAngularDensity k a theta
  have hDistance : Measurable (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hG : Measurable G := by
    dsimp only [G]
    fun_prop
  have hRho : Measurable (fun theta ↦ ENNReal.ofReal (rho theta)) := by
    apply Measurable.ennreal_ofReal
    dsimp only [rho, platformAngularDensity, platformDensityCoefficient,
      platformAngularDistance]
    fun_prop
  rw [platformConstantReferenceMeasure]
  rw [integrable_map_measure hG.aestronglyMeasurable hDistance.aemeasurable]
  rw [platformAngularReferenceMeasure]
  apply (integrable_withDensity_iff hRho
    (ae_of_all _ fun theta ↦ ENNReal.ofReal_lt_top)).2
  have han : AnalyticOnNhd ℝ
      (fun theta : ℝ ↦ d - platformAngularDistance a theta) Set.univ :=
    fun _ _ ↦ by
      unfold platformAngularDistance
      fun_prop
  have hmer : MeromorphicOn
      (fun theta : ℝ ↦ d - platformAngularDistance a theta)
      (Set.uIcc 0 Real.pi) :=
    fun theta _htheta ↦ han.meromorphicOn theta (Set.mem_univ theta)
  have hkernel : IntervalIntegrable
      (fun theta : ℝ ↦ Real.log |d - platformAngularDistance a theta|)
      volume 0 Real.pi := by
    simpa only [Real.norm_eq_abs] using!
      MeromorphicOn.intervalIntegrable_log_norm hmer
  have hdensity : ContinuousOn (platformAngularDensity k a)
      (Set.uIcc 0 Real.pi) := by
    have hdistance : ContinuousOn (platformAngularDistance a)
        (Set.uIcc 0 Real.pi) := by
      unfold platformAngularDistance
      fun_prop
    have hdistanceNe : ∀ theta ∈ Set.uIcc (0 : ℝ) Real.pi,
        platformAngularDistance a theta ≠ 0 := by
      intro theta htheta
      rw [uIcc_of_le Real.pi_pos.le] at htheta
      exact (platformAngularDistance_pos ha ha2.le htheta).ne'
    unfold platformAngularDensity platformDensityCoefficient
    exact continuousOn_const.add continuousOn_const |>.sub
      (continuousOn_const.div hdistance hdistanceNe)
  have hrhoContinuous : ContinuousOn rho (Set.uIcc 0 Real.pi) := by
    exact continuousOn_const.mul hdensity
  have hweighted : IntervalIntegrable
      (fun theta : ℝ ↦ rho theta *
        G (platformAngularDistance a theta)) volume 0 Real.pi := by
    have h := hkernel.continuousOn_mul hrhoContinuous
    simpa only [G, rho, mul_comm] using! h
  apply hweighted.1.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with theta htheta
  have hthetaIcc : theta ∈ Icc (0 : ℝ) Real.pi :=
    ⟨htheta.1.le, htheta.2⟩
  have hrhoNonneg : 0 ≤ rho theta :=
    mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le)
      (platformAngularDensity_nonneg hk ha ha2.le hthreshold hthetaIcc)
  rw [ENNReal.toReal_ofReal hrhoNonneg]
  simp only [Function.comp_apply]
  ring

theorem integrable_positiveBufferContinuousRootMeasure_log_kernel
    {s alpha x : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s)
    (hx : x ∈ Icc (positiveBufferDistanceLeft s - 1) 1) :
    Integrable (fun y : ℝ ↦ Real.log |x - y|)
      (positiveBufferContinuousRootMeasure s alpha) := by
  let G : ℝ → ℝ := fun y ↦ Real.log |x - y|
  have hG : Measurable G := by
    dsimp only [G]
    fun_prop
  have hshift : Measurable positiveBufferRootCoordinate := by
    unfold positiveBufferRootCoordinate
    fun_prop
  rw [positiveBufferContinuousRootMeasure]
  rw [integrable_map_measure hG.aestronglyMeasurable hshift.aemeasurable]
  have hd : x + 1 ∈ Icc (positiveBufferDistanceLeft s) 2 := by
    constructor <;> linarith [hx.1, hx.2]
  have hbase := integrable_platformConstantReferenceMeasure_log_kernel
    (positiveBufferRatio_nonneg halpha (halphas.trans_lt hs1))
    (positiveBufferDistanceLeft_pos hs)
    (positiveBufferDistanceLeft_lt_two hs hs1)
    (positiveBuffer_threshold_le hs.le hs1 halpha halphas)
    (d := x + 1)
  apply hbase.congr
  filter_upwards with e
  simp only [Function.comp_apply, G, positiveBufferRootCoordinate]
  congr 2
  ring

/-- The full positive-buffer measure: an atom of mass `alpha` at `-1`
plus the translated continuous probability with mass `1 - alpha`. -/
def positiveBufferMeasure (s alpha : ℝ) : Measure ℝ :=
  ENNReal.ofReal alpha • Measure.dirac (-1 : ℝ) +
    ENNReal.ofReal (1 - alpha) • positiveBufferContinuousRootMeasure s alpha

/-- Translating the continuous reference simply replaces `x - t` by the
distance-coordinate difference `(x + 1) - d`. -/
theorem integral_positiveBufferContinuousRootMeasure_log_kernel
    {s alpha x : ℝ} :
    (∫ y : ℝ, Real.log |x - y|
        ∂(positiveBufferContinuousRootMeasure s alpha)) =
      ∫ e : ℝ, Real.log |(x + 1) - e|
        ∂(positiveBufferContinuousDistanceMeasure s alpha) := by
  have hshift : Measurable positiveBufferRootCoordinate := by
    unfold positiveBufferRootCoordinate
    fun_prop
  have hkernel : Measurable (fun y : ℝ ↦ Real.log |x - y|) := by
    fun_prop
  rw [positiveBufferContinuousRootMeasure,
    integral_map hshift.aemeasurable hkernel.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with e
  simp only [positiveBufferRootCoordinate]
  congr 2
  ring

/-- Logarithmic potential of the full positive-buffer measure. -/
def positiveBufferPotential (s alpha x : ℝ) : ℝ :=
  ∫ y : ℝ, Real.log |x - y| ∂(positiveBufferMeasure s alpha)

/-- Constant value of the positive-buffer potential on its continuous
support. -/
def positiveBufferPlatformValue (s alpha : ℝ) : ℝ :=
  (1 - alpha) * Real.log (platformCapacity (positiveBufferDistanceLeft s)) +
    alpha * Real.log (platformD0 (positiveBufferDistanceLeft s))

/-- At the zero-platform endpoint mass `A(q)`, the platform value vanishes
exactly. -/
theorem positiveBufferPlatformValue_s_A_eq_zero
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling) :
    positiveBufferPlatformValue (s q) (A q) = 0 := by
  have hqOne : q < 1 := mem_Ioo_zero_qCeiling_imp_lt_one hq
  have hH : 0 < H q := H_pos hq.1
  have hlogq : Real.log q ≠ 0 := log_q_ne_zero hq.1 hqOne
  rw [positiveBufferPlatformValue,
    platformCapacity_positiveBufferDistanceLeft_s
      (ne_of_gt (by linarith [hq.1] : (-1 : ℝ) < q)),
    platformD0_positiveBufferDistanceLeft_s hq.1 hqOne,
    Real.log_div hH.ne' hq.1.ne', A]
  field_simp [hlogq]
  ring

/-- The positive-buffer potential is constant on its continuous support.
This is the measure-theoretic form of manuscript equation `(9.3)`, before
specializing `s` and `alpha` to the one-cut parameters. -/
theorem positiveBufferPotential_eq_platformValue
    {s alpha x : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s)
    (hx : x ∈ Icc (positiveBufferDistanceLeft s - 1) 1) :
    positiveBufferPotential s alpha x =
      (1 - alpha) *
          Real.log (platformCapacity (positiveBufferDistanceLeft s)) +
        alpha * Real.log (platformD0 (positiveBufferDistanceLeft s)) := by
  let kernel : ℝ → ℝ := fun y ↦ Real.log |x - y|
  have halpha1 : alpha < 1 := halphas.trans_lt hs1
  have hcontinuous : Integrable kernel
      (positiveBufferContinuousRootMeasure s alpha) := by
    exact integrable_positiveBufferContinuousRootMeasure_log_kernel
      hs hs1 halpha halphas hx
  have hatomScaled : Integrable kernel
      (ENNReal.ofReal alpha • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  have hcontinuousScaled : Integrable kernel
      (ENNReal.ofReal (1 - alpha) •
        positiveBufferContinuousRootMeasure s alpha) :=
    hcontinuous.smul_measure (by simp)
  have hdistance : 0 < x + 1 := by
    have hd0 := positiveBufferDistanceLeft_pos hs
    linarith [hx.1]
  have hd : x + 1 ∈ Icc (positiveBufferDistanceLeft s) 2 := by
    constructor <;> linarith [hx.1, hx.2]
  have hplatform :=
    integral_platformConstantReferenceMeasure_log_potential
      (positiveBufferRatio_nonneg halpha halpha1)
      (positiveBufferDistanceLeft_pos hs)
      (positiveBufferDistanceLeft_lt_two hs hs1)
      (positiveBuffer_threshold_le hs.le hs1 halpha halphas)
      hd
  change positiveBufferRatio alpha * Real.log (x + 1) +
      (∫ e : ℝ, Real.log |(x + 1) - e|
        ∂(positiveBufferContinuousDistanceMeasure s alpha)) =
      Real.log (platformCapacity (positiveBufferDistanceLeft s)) +
        positiveBufferRatio alpha *
          Real.log (platformD0 (positiveBufferDistanceLeft s)) at hplatform
  rw [positiveBufferPotential, positiveBufferMeasure,
    integral_add_measure hatomScaled hcontinuousScaled,
    integral_smul_measure, integral_dirac, integral_smul_measure,
    ENNReal.toReal_ofReal halpha,
    ENNReal.toReal_ofReal (sub_nonneg.mpr halpha1.le)]
  simp only [kernel, smul_eq_mul]
  rw [show x - (-1 : ℝ) = x + 1 by ring, abs_of_pos hdistance,
    integral_positiveBufferContinuousRootMeasure_log_kernel]
  calc
    alpha * Real.log (x + 1) +
          (1 - alpha) *
            (∫ e : ℝ, Real.log |(x + 1) - e|
              ∂(positiveBufferContinuousDistanceMeasure s alpha)) =
        (1 - alpha) *
          (positiveBufferRatio alpha * Real.log (x + 1) +
            ∫ e : ℝ, Real.log |(x + 1) - e|
              ∂(positiveBufferContinuousDistanceMeasure s alpha)) := by
      have hterm :
          alpha * Real.log (x + 1) =
            ((1 - alpha) * positiveBufferRatio alpha) *
              Real.log (x + 1) := by
        rw [one_sub_mul_positiveBufferRatio halpha1]
      rw [hterm]
      ring
    _ = (1 - alpha) *
        (Real.log (platformCapacity (positiveBufferDistanceLeft s)) +
          positiveBufferRatio alpha *
            Real.log (platformD0 (positiveBufferDistanceLeft s))) := by
      rw [hplatform]
    _ = (1 - alpha) *
          Real.log (platformCapacity (positiveBufferDistanceLeft s)) +
        alpha * Real.log (platformD0 (positiveBufferDistanceLeft s)) := by
      have hterm :
          alpha * Real.log (platformD0 (positiveBufferDistanceLeft s)) =
            ((1 - alpha) * positiveBufferRatio alpha) *
              Real.log (platformD0 (positiveBufferDistanceLeft s)) := by
        rw [one_sub_mul_positiveBufferRatio halpha1]
      rw [hterm]
      ring

theorem positiveBufferPotential_eq_value
    {s alpha x : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s)
    (hx : x ∈ Icc (positiveBufferDistanceLeft s - 1) 1) :
    positiveBufferPotential s alpha x =
      positiveBufferPlatformValue s alpha := by
  simpa only [positiveBufferPlatformValue] using!
    positiveBufferPotential_eq_platformValue hs hs1 halpha halphas hx

/-- For fixed `s ∈ (0,1)`, increasing the endpoint mass strictly increases
the constant platform value. -/
theorem positiveBufferPlatformValue_strictMono
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    StrictMono (positiveBufferPlatformValue s) := by
  have hcapPos : 0 < platformCapacity (positiveBufferDistanceLeft s) :=
    platformCapacity_pos (positiveBufferDistanceLeft_lt_two hs hs1)
  have hDPos : 0 < platformD0 (positiveBufferDistanceLeft s) := by
    rw [platformD0_positiveBufferDistanceLeft hs.le]
    positivity
  have hcapD :
      platformCapacity (positiveBufferDistanceLeft s) <
        platformD0 (positiveBufferDistanceLeft s) := by
    rw [platformCapacity_positiveBufferDistanceLeft,
      platformD0_positiveBufferDistanceLeft hs.le]
    nlinarith [sq_pos_of_pos hs]
  have hlog :
      Real.log (platformCapacity (positiveBufferDistanceLeft s)) <
        Real.log (platformD0 (positiveBufferDistanceLeft s)) :=
    Real.strictMonoOn_log hcapPos hDPos hcapD
  intro alpha beta halphaBeta
  have hslope : 0 <
      Real.log (platformD0 (positiveBufferDistanceLeft s)) -
        Real.log (platformCapacity (positiveBufferDistanceLeft s)) :=
    sub_pos.mpr hlog
  calc
    positiveBufferPlatformValue s alpha =
        Real.log (platformCapacity (positiveBufferDistanceLeft s)) +
          alpha *
            (Real.log (platformD0 (positiveBufferDistanceLeft s)) -
              Real.log (platformCapacity (positiveBufferDistanceLeft s))) := by
      unfold positiveBufferPlatformValue
      ring
    _ < Real.log (platformCapacity (positiveBufferDistanceLeft s)) +
          beta *
            (Real.log (platformD0 (positiveBufferDistanceLeft s)) -
              Real.log (platformCapacity (positiveBufferDistanceLeft s))) :=
      by
        simpa only [add_comm] using!
          add_lt_add_left (mul_lt_mul_of_pos_right halphaBeta hslope)
            (Real.log (platformCapacity (positiveBufferDistanceLeft s)))
    _ = positiveBufferPlatformValue s beta := by
      unfold positiveBufferPlatformValue
      ring

theorem positiveBufferPotential_pos_of_reference_zero
    {s alphaZero alpha x : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s)
    (hzero : positiveBufferPlatformValue s alphaZero = 0)
    (halphaGreater : alphaZero < alpha)
    (hx : x ∈ Icc (positiveBufferDistanceLeft s - 1) 1) :
    0 < positiveBufferPotential s alpha x := by
  rw [positiveBufferPotential_eq_value hs hs1 halpha halphas hx]
  have hlt := positiveBufferPlatformValue_strictMono hs hs1 halphaGreater
  simpa only [hzero] using! hlt

theorem positiveBufferPotential_s_pos_of_A_lt
    {q alpha x : ℝ} (hq : q ∈ Ioo (0 : ℝ) qCeiling)
    (halpha : 0 ≤ alpha) (hAalpha : A q < alpha)
    (halphas : alpha ≤ s q)
    (hx : x ∈ Icc (positiveBufferDistanceLeft (s q) - 1) 1) :
    0 < positiveBufferPotential (s q) alpha x := by
  have hs := s_mem_Ioo_of_mem_Ioo hq
  exact positiveBufferPotential_pos_of_reference_zero
    hs.1 hs.2 halpha halphas
    (positiveBufferPlatformValue_s_A_eq_zero hq) hAalpha hx

theorem positiveBufferMeasure_apply_univ
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    positiveBufferMeasure s alpha Set.univ = 1 := by
  letI : IsProbabilityMeasure (positiveBufferContinuousRootMeasure s alpha) :=
    isProbabilityMeasure_positiveBufferContinuousRootMeasure hs hs1 halpha halphas
  rw [positiveBufferMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  simp only [measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add halpha (sub_nonneg.mpr (halphas.trans_lt hs1).le)]
  norm_num

theorem isProbabilityMeasure_positiveBufferMeasure
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    IsProbabilityMeasure (positiveBufferMeasure s alpha) :=
  ⟨positiveBufferMeasure_apply_univ hs hs1 halpha halphas⟩

/-- The positive-buffer measure bundled as a probability measure. -/
def positiveBufferProbability
    (s alpha : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) : ProbabilityMeasure ℝ :=
  ⟨positiveBufferMeasure s alpha,
    isProbabilityMeasure_positiveBufferMeasure hs hs1 halpha halphas⟩

theorem positiveBufferMeasure_compl_rootInterval
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    positiveBufferMeasure s alpha (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have hcontinuous :
      positiveBufferContinuousRootMeasure s alpha (Icc (-1 : ℝ) 1)ᶜ = 0 := by
    apply le_antisymm
    · calc
        positiveBufferContinuousRootMeasure s alpha (Icc (-1 : ℝ) 1)ᶜ ≤
            positiveBufferContinuousRootMeasure s alpha
              (Icc (positiveBufferDistanceLeft s - 1) 1)ᶜ := by
          apply measure_mono
          intro x hx hxsupport
          apply hx
          constructor
          · have hd0 : 0 ≤ positiveBufferDistanceLeft s :=
              (positiveBufferDistanceLeft_pos hs).le
            linarith [hxsupport.1]
          · exact hxsupport.2
        _ = 0 := positiveBufferContinuousRootMeasure_compl_support hs hs1
    · exact bot_le
  rw [positiveBufferMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, hcontinuous]
  have hminus : (-1 : ℝ) ∉ (Icc (-1 : ℝ) 1)ᶜ := by simp
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
  simp [hminus]

theorem positiveBufferProbability_supported
    {s alpha : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (halpha : 0 ≤ alpha) (halphas : alpha ≤ s) :
    IsRootIntervalSupported
      (positiveBufferProbability s alpha hs hs1 halpha halphas) := by
  apply (prob_compl_eq_zero_iff measurableSet_Icc).1
  exact positiveBufferMeasure_compl_rootInterval hs hs1

end

end Erdos1038
