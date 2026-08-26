import ErdosProblems.Erdos1038.PlatformPotential
import ErdosProblems.Erdos1038.PlatformNormalizedDensities
import ErdosProblems.Erdos1038.CircleBlock
import ErdosProblems.Erdos1038.PlatformCircleDensity

/-!
# Constant-platform data for the circle block inequality

This file connects three previously separate parts of the high-`k` lower
argument:

* the exact platform potential constant from equation `(4.6)`;
* the normalized reference and adjoint angular masses from `(5.1)`;
* the centered-arc logarithmic deficit and the algebraic block inequality.

The remaining analytic input is isolated as the normalized mixed-energy
bound used by `circleBlock_energy_bound_of_margin_nonneg`.
-/

set_option warningAsError false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1038

noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The normalized reference mass `Q` of an angular interval.  It is also
the radius of the centered arc with the same circle mass. -/
def platformReferenceCircleRadius (k a left right : ℝ) : ℝ :=
  ∫ theta : ℝ in left..right,
    platformNormalizedReferenceDensity k a theta

/-- The normalized adjoint mass `R` of an angular interval. -/
def platformAdjointCircleRadius
    (a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ) : ℝ :=
  ∫ theta : ℝ in left..right,
    platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus theta

/-- Physical reference mass `q` of an angular interval. -/
def platformReferenceIntervalMass (k a left right : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ theta : ℝ in left..right, platformAngularDensity k a theta

/-- Physical adjoint mass `r` of an angular interval. -/
def platformAdjointIntervalMass
    (a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ theta : ℝ in left..right,
      platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta

/-- The constant `C(k,a)` supplied by the platform potential identity. -/
def platformPotentialConstant (k a : ℝ) : ℝ :=
  Real.log (platformCapacity a) + k * Real.log (platformD0 a)

theorem platformReferenceCircleRadius_mem_Icc
    {k a left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    platformReferenceCircleRadius k a left right ∈ Icc 0 Real.pi := by
  have hsubset : Set.uIcc left right ⊆ Set.uIcc 0 Real.pi := by
    rw [uIcc_of_le hle, uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc hleft hright
  have hIntegrable : IntervalIntegrable
      (platformNormalizedReferenceDensity k a) volume left right :=
    (intervalIntegrable_platformNormalizedReferenceDensity k ha ha2.le).mono_set
      hsubset
  have hbounds : ∀ theta ∈ Icc left right,
      platformNormalizedReferenceDensity k a theta ∈ Icc 0 1 := by
    intro theta htheta
    apply platformNormalizedReferenceDensity_mem_Icc
      hk ha ha2.le hthreshold
    exact ⟨hleft.trans htheta.1, htheta.2.trans hright⟩
  constructor
  · unfold platformReferenceCircleRadius
    exact intervalIntegral.integral_nonneg hle fun theta htheta ↦
      (hbounds theta htheta).1
  · unfold platformReferenceCircleRadius
    calc
      (∫ theta : ℝ in left..right,
          platformNormalizedReferenceDensity k a theta) ≤
          ∫ _theta : ℝ in left..right, (1 : ℝ) := by
        exact intervalIntegral.integral_mono_on hle hIntegrable
          intervalIntegrable_const fun theta htheta ↦
            (hbounds theta htheta).2
      _ = right - left := by simp
      _ ≤ Real.pi := by linarith

theorem platformAdjointCircleRadius_mem_Icc
    {a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right ∈ Icc 0 Real.pi := by
  have hsubset : Set.uIcc left right ⊆ Set.uIcc 0 Real.pi := by
    rw [uIcc_of_le hle, uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc hleft hright
  have hIntegrable : IntervalIntegrable
      (platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus) volume left right :=
    (intervalIntegrable_platformNormalizedAdjointDensity
      hxMinus hxPlus ha2).mono_set hsubset
  have hbounds : ∀ theta ∈ Icc left right,
      platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta ∈ Icc 0 1 := by
    intro theta htheta
    apply platformNormalizedAdjointDensity_mem_Icc
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
    exact ⟨hleft.trans htheta.1, htheta.2.trans hright⟩
  constructor
  · unfold platformAdjointCircleRadius
    exact intervalIntegral.integral_nonneg hle fun theta htheta ↦
      (hbounds theta htheta).1
  · unfold platformAdjointCircleRadius
    calc
      (∫ theta : ℝ in left..right,
          platformNormalizedAdjointDensity
            a xMinus xPlus sigmaMinus sigmaPlus theta) ≤
          ∫ _theta : ℝ in left..right, (1 : ℝ) := by
        exact intervalIntegral.integral_mono_on hle hIntegrable
          intervalIntegrable_const fun theta htheta ↦
            (hbounds theta htheta).2
      _ = right - left := by simp
      _ ≤ Real.pi := by linarith

theorem platformReferenceCircleRadius_pos
    {k a left right : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    0 < platformReferenceCircleRadius k a left right := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  have hright0 : 0 < right := hleft.trans_lt hlt
  have hrightMem : right ∈ Icc (0 : ℝ) Real.pi :=
    ⟨hright0.le, hright⟩
  have hdlt : a < platformAngularDistance a right := by
    have hmono := platformAngularDistance_strictMonoOn ha2
      (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
      hrightMem hright0
    simpa using! hmono
  have hs : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  have hdiv : Real.sqrt (2 * a) / platformAngularDistance a right <
      Real.sqrt (2 * a) / a :=
    div_lt_div_of_pos_left hs ha hdlt
  have hmul : k * Real.sqrt (2 * a) / platformAngularDistance a right <
      k * Real.sqrt (2 * a) / a := by
    calc
      k * Real.sqrt (2 * a) / platformAngularDistance a right =
          k * (Real.sqrt (2 * a) /
            platformAngularDistance a right) := by ring
      _ < k * (Real.sqrt (2 * a) / a) :=
        mul_lt_mul_of_pos_left hdiv (lt_of_lt_of_le (by norm_num) hk)
      _ = k * Real.sqrt (2 * a) / a := by ring
  have hleftDensity : 0 ≤ platformDensityCoefficient k a a :=
    (platformDensityCoefficient_at_left_nonneg_iff hk0 ha).2 hthreshold
  unfold platformDensityCoefficient at hleftDensity
  have hrightDensity : 0 < platformAngularDensity k a right := by
    unfold platformAngularDensity platformDensityCoefficient
    linarith
  have hrightNormalized :
      0 < platformNormalizedReferenceDensity k a right := by
    exact div_pos hrightDensity (platformAPi_pos hk0 ha ha2.le)
  have hcont : ContinuousOn (platformNormalizedReferenceDensity k a)
      (Icc left right) := by
    have hden : ContinuousOn (platformAngularDistance a)
        (Icc left right) := by
      unfold platformAngularDistance
      fun_prop
    have hdenne : ∀ theta ∈ Icc left right,
        platformAngularDistance a theta ≠ 0 := by
      intro theta htheta
      exact (platformAngularDistance_pos ha ha2.le
        ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).ne'
    unfold platformNormalizedReferenceDensity platformAngularDensity
      platformDensityCoefficient
    exact (continuousOn_const.sub
      (continuousOn_const.div hden hdenne)).div_const _
  unfold platformReferenceCircleRadius
  apply intervalIntegral.integral_pos hlt hcont
  · intro theta htheta
    exact (platformNormalizedReferenceDensity_mem_Icc hk0 ha ha2.le
      hthreshold ⟨hleft.trans htheta.1.le, htheta.2.trans hright⟩).1
  · exact ⟨right, ⟨hlt.le, le_rfl⟩, hrightNormalized⟩

theorem platformAdjointCircleRadius_pos
    {a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hleft : 0 ≤ left) (hlt : left < right)
    (hright : right ≤ Real.pi) :
    0 < platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right := by
  have hright0 : 0 < right := hleft.trans_lt hlt
  have hrightDensity : 0 < platformAngularAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus right :=
    platformAngularAdjointDensity_pos hxMinus hxPlus
      hsigmaMinus hsigmaPlus ha2 ⟨hright0, hright⟩
  have hrightNormalized : 0 < platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus right :=
    div_pos hrightDensity
      (platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2)
  have hcont : ContinuousOn
      (platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus) (Icc left right) := by
    have hd : ContinuousOn (platformAngularDistance a)
        (Icc left right) := by
      unfold platformAngularDistance
      fun_prop
    have hdm : ContinuousOn
        (fun theta ↦ platformAngularDistance a theta - xMinus)
        (Icc left right) := hd.sub continuousOn_const
    have hdp : ContinuousOn
        (fun theta ↦ platformAngularDistance a theta - xPlus)
        (Icc left right) := hd.sub continuousOn_const
    have hdmne : ∀ theta ∈ Icc left right,
        platformAngularDistance a theta - xMinus ≠ 0 := by
      intro theta htheta
      exact sub_ne_zero.mpr (ne_of_gt (hxMinus.trans_le
        (platformAngularDistance_mem_Icc ha2.le
          ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).1))
    have hdpne : ∀ theta ∈ Icc left right,
        platformAngularDistance a theta - xPlus ≠ 0 := by
      intro theta htheta
      exact sub_ne_zero.mpr (ne_of_gt (hxPlus.trans_le
        (platformAngularDistance_mem_Icc ha2.le
          ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).1))
    unfold platformNormalizedAdjointDensity platformAngularAdjointDensity
      adjointNumerator
    exact ((continuousOn_const.sub
      (continuousOn_const.div hdm hdmne)).sub
        (continuousOn_const.div hdp hdpne)).div_const _
  unfold platformAdjointCircleRadius
  apply intervalIntegral.integral_pos hlt hcont
  · intro theta htheta
    exact (platformNormalizedAdjointDensity_mem_Icc
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
      ⟨hleft.trans htheta.1.le, htheta.2.trans hright⟩).1
  · exact ⟨right, ⟨hlt.le, le_rfl⟩, hrightNormalized⟩

/-- Exact conversion `q = a_π Q / π` from equation `(5.1)`. -/
theorem platformReferenceIntervalMass_eq_endpoint_mul_radius
    {k a left right : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2) :
    platformReferenceIntervalMass k a left right =
      platformAPi k a * platformReferenceCircleRadius k a left right /
        Real.pi := by
  have hAPi : platformAPi k a ≠ 0 :=
    (platformAPi_pos hk ha ha2).ne'
  unfold platformReferenceIntervalMass platformReferenceCircleRadius
    platformNormalizedReferenceDensity
  rw [intervalIntegral.integral_div]
  field_simp [hAPi, Real.pi_ne_zero]

/-- Exact conversion `r = b_π R / π` from equation `(5.1)`. -/
theorem platformAdjointIntervalMass_eq_endpoint_mul_radius
    {a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) :
    platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus left right =
      platformBPi a xMinus xPlus sigmaMinus sigmaPlus *
          platformAdjointCircleRadius
            a xMinus xPlus sigmaMinus sigmaPlus left right /
        Real.pi := by
  have hBPi : platformBPi
      a xMinus xPlus sigmaMinus sigmaPlus ≠ 0 :=
    (platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2).ne'
  unfold platformAdjointIntervalMass platformAdjointCircleRadius
    platformNormalizedAdjointDensity
  rw [intervalIntegral.integral_div]
  field_simp [hBPi, Real.pi_ne_zero]

/-- The centered decreasing platform densities are dominated by the two
centered arc indicators with radii equal to their interval masses. -/
theorem platformCenteredDensity_logDeficit_le_twoArcEnergy
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    circleDensityLogDeficit
        (platformReferenceCenteredCircleDensity k a left right)
        (platformAdjointCenteredCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) ≤
      circleLogTwoArcEnergy
        (platformReferenceCircleRadius k a left right)
        (platformAdjointCircleRadius
          a xMinus xPlus sigmaMinus sigmaPlus left right) 0 := by
  let Q : ℝ := platformReferenceCircleRadius k a left right
  let R : ℝ := platformAdjointCircleRadius
    a xMinus xPlus sigmaMinus sigmaPlus left right
  have hQ : Q ∈ Icc (0 : ℝ) Real.pi :=
    platformReferenceCircleRadius_mem_Icc
      hk ha ha2 hthreshold hleft hle hright
  have hR : R ∈ Icc (0 : ℝ) Real.pi :=
    platformAdjointCircleRadius_mem_Icc
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hle hright
  have hfBounds := platformReferenceCenteredCircleDensity_mem_Icc
    hk ha ha2.le hthreshold hleft hright
  have hgBounds := platformAdjointCenteredCircleDensity_mem_Icc
    hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hright
  have hmassF :
      (∫⁻ z : AddCircle (2 * Real.pi), ENNReal.ofReal
        (platformReferenceCenteredCircleDensity k a left right z)) =
        volume (Metric.closedBall (0 : AddCircle (2 * Real.pi)) Q) := by
    calc
      (∫⁻ z : AddCircle (2 * Real.pi), ENNReal.ofReal
          (platformReferenceCenteredCircleDensity k a left right z)) =
          ENNReal.ofReal (2 * Q) := by
        simpa only [Q, platformReferenceCircleRadius] using!
          lintegral_platformReferenceCenteredCircleDensity
            hk ha ha2.le hthreshold hleft hle hright
      _ = volume (Metric.closedBall (0 : AddCircle (2 * Real.pi)) Q) := by
        rw [AddCircle.volume_closedBall]
        congr 1
        exact (min_eq_right (by linarith [hQ.2])).symm
  have hmassG :
      (∫⁻ z : AddCircle (2 * Real.pi), ENNReal.ofReal
        (platformAdjointCenteredCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right z)) =
        volume (Metric.closedBall (0 : AddCircle (2 * Real.pi)) R) := by
    calc
      (∫⁻ z : AddCircle (2 * Real.pi), ENNReal.ofReal
          (platformAdjointCenteredCircleDensity
            a xMinus xPlus sigmaMinus sigmaPlus left right z)) =
          ENNReal.ofReal (2 * R) := by
        simpa only [R, platformAdjointCircleRadius] using!
          lintegral_platformAdjointCenteredCircleDensity
            hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
            hleft hle hright
      _ = volume (Metric.closedBall (0 : AddCircle (2 * Real.pi)) R) := by
        rw [AddCircle.volume_closedBall]
        congr 1
        exact (min_eq_right (by linarith [hR.2])).symm
  let radiusG : ℝ → ℝ := fun s ↦
    right - platformAdjointSuperlevelLower
      a xMinus xPlus sigmaMinus sigmaPlus left right s
  have hradiusG0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ radiusG s := by
    intro s _hs
    dsimp only [radiusG]
    linarith [
      (platformAdjointSuperlevelLower_mem_Icc
        a xMinus xPlus sigmaMinus sigmaPlus (t := s) hle).2]
  have hradiusGPi : ∀ s ∈ Ioi (0 : ℝ), radiusG s ≤ Real.pi := by
    intro s _hs
    dsimp only [radiusG]
    have hcut := platformAdjointSuperlevelLower_mem_Icc
      a xMinus xPlus sigmaMinus sigmaPlus (t := s) hle
    linarith [hleft.trans hcut.1]
  apply circleDensityLogDeficit_le_twoArcEnergy_of_centeredSuperlevels
    (measurable_platformReferenceCenteredCircleDensity k a left right)
    (measurable_platformAdjointCenteredCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right)
    (fun z ↦ (hfBounds z).1) (fun z ↦ (hfBounds z).2)
    (fun z ↦ (hgBounds z).1) (fun z ↦ (hgBounds z).2)
    hQ hR hmassF hmassG radiusG hradiusG0 hradiusGPi
  intro s hs
  exact platformAdjointCenteredCircleDensity_superlevel_ae_eq_closedBall
    hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
    hleft hle hright hs

/-- Unconditional platform rearrangement all the way to the single pair of
fixed-mass centered arcs. -/
theorem platformCircleDensity_logDeficit_le_twoArcEnergy
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    circleDensityLogDeficit
        (platformReferenceCircleDensity k a left right)
        (platformAdjointCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) ≤
      circleLogTwoArcEnergy
        (platformReferenceCircleRadius k a left right)
        (platformAdjointCircleRadius
          a xMinus xPlus sigmaMinus sigmaPlus left right) 0 := by
  calc
    circleDensityLogDeficit
        (platformReferenceCircleDensity k a left right)
        (platformAdjointCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) ≤
        centeredTerminalShellLayerCakeDeficit
          (platformReferenceSuperlevelLower k a left right)
          (platformAdjointSuperlevelLower
            a xMinus xPlus sigmaMinus sigmaPlus left right) right :=
      platformCircleDensity_logDeficit_le_centeredCanonicalLayerCake_unconditional
        hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hleft hle hright
    _ = circleDensityLogDeficit
        (platformReferenceCenteredCircleDensity k a left right)
        (platformAdjointCenteredCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) :=
      platformCenteredCanonicalLayerCakeDeficit_eq_centeredDensityLogDeficit
        hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hleft hle hright
    _ ≤ circleLogTwoArcEnergy
        (platformReferenceCircleRadius k a left right)
        (platformAdjointCircleRadius
          a xMinus xPlus sigmaMinus sigmaPlus left right) 0 :=
      platformCenteredDensity_logDeficit_le_twoArcEnergy
        hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hleft hle hright

theorem platformCircleTwoArcEnergy_ne_top
    (k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ) :
    circleLogTwoArcEnergy
        (platformReferenceCircleRadius k a left right)
        (platformAdjointCircleRadius
          a xMinus xPlus sigmaMinus sigmaPlus left right) 0 ≠ ∞ :=
  circleLogTwoArcEnergy_ne_top _ _ _

/-- The centered two-arc deficit is maximal for the radii obtained from any
platform quantile interval.  This is the direct `CircleLogLayerCake`
instantiation needed after the bathtub step. -/
theorem platformInterval_twoArcDeficit_le_centered
    {k a xMinus xPlus sigmaMinus sigmaPlus left right distance : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) (hdistance : distance ∈ Icc 0 Real.pi) :
    circleLogTwoArcEnergy
        (platformReferenceCircleRadius k a left right)
        (platformAdjointCircleRadius
          a xMinus xPlus sigmaMinus sigmaPlus left right)
        distance ≤
      circleLogTwoArcEnergy
        (platformReferenceCircleRadius k a left right)
        (platformAdjointCircleRadius
          a xMinus xPlus sigmaMinus sigmaPlus left right)
        0 := by
  have hQ := platformReferenceCircleRadius_mem_Icc
    hk ha ha2 hthreshold hleft hle hright
  have hR := platformAdjointCircleRadius_mem_Icc
    hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hle hright
  exact circleLogTwoArcEnergy_antitoneOn
    hQ.1 hQ.2 hR.1 hR.2
    ⟨le_rfl, Real.pi_pos.le⟩ hdistance hdistance.1

/-- Platform-specialized form of the target block inequality `(4.32)`.
All factors of `π`, `a_π`, and `b_π` are discharged here.  The two remaining
hypotheses are precisely the circle mixed-energy lower bound and the scalar
calibration margin. -/
theorem platformCircleBlock_energy_bound_of_margin_nonneg
    {k a xMinus xPlus sigmaMinus sigmaPlus left right Ceff E : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hQ : 0 < platformReferenceCircleRadius k a left right)
    (hR : 0 < platformAdjointCircleRadius
      a xMinus xPlus sigmaMinus sigmaPlus left right)
    (henergy :
      Real.log (platformCapacity a) +
          circleSelfEnergy (platformReferenceCircleRadius k a left right) +
          circleSelfEnergy (platformAdjointCircleRadius
            a xMinus xPlus sigmaMinus sigmaPlus left right) +
          circleSincSquareGap
            (platformReferenceCircleRadius k a left right)
            (platformAdjointCircleRadius
              a xMinus xPlus sigmaMinus sigmaPlus left right) ≤
        E /
          (platformReferenceIntervalMass k a left right *
            platformAdjointIntervalMass
              a xMinus xPlus sigmaMinus sigmaPlus left right))
    (hmargin : 0 ≤ circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a left right)
      (platformAdjointCircleRadius
        a xMinus xPlus sigmaMinus sigmaPlus left right)) :
    platformReferenceIntervalMass k a left right *
          platformAdjointIntervalMass
            a xMinus xPlus sigmaMinus sigmaPlus left right *
          Real.log
            (platformReferenceIntervalMass k a left right *
                platformAdjointIntervalMass
                  a xMinus xPlus sigmaMinus sigmaPlus left right /
              2) +
        Ceff * platformAdjointIntervalMass
          a xMinus xPlus sigmaMinus sigmaPlus left right ≤ E := by
  apply circleBlock_energy_bound_of_margin_nonneg
    (platformCapacity_pos ha2)
    (platformAPi_pos hk ha ha2.le)
    (platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2)
    hQ hR
  · exact platformReferenceIntervalMass_eq_endpoint_mul_radius hk ha ha2.le
  · exact platformAdjointIntervalMass_eq_endpoint_mul_radius
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  · exact henergy
  · exact hmargin

/-- Equation `(4.6)` supplies exactly the platform constant used by the
block reduction. -/
theorem platformConstantReference_potential_eq_platformPotentialConstant
    {k a d : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (hd : d ∈ Icc a 2) :
    k * Real.log d +
        (∫ e : ℝ, Real.log (abs (d - e))
          ∂(platformConstantReferenceMeasure k a)) =
      platformPotentialConstant k a := by
  exact integral_platformConstantReferenceMeasure_log_potential
    hk ha ha2 hthreshold hd

/-- Finite-partition assembly of `(4.29)`--`(4.33)`, conditional only on
the normalized circle-energy bound and scalar margin on each block.  The
platform potential theorem fixes `C`, while the normalized density lemmas
discharge positivity and every mass conversion. -/
theorem finite_platformCircleBlock_reduction
    {ι : Type*} [Fintype ι]
    (left right energy targetRadius : ι → ℝ)
    {k a xMinus xPlus sigmaMinus sigmaPlus Ceff M0 L R0 : ℝ}
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : ∀ i, 0 ≤ left i) (hlr : ∀ i, left i < right i)
    (hright : ∀ i, right i ≤ Real.pi)
    (hTargetRadius : ∀ i, 0 < targetRadius i)
    (hAdjointMassSum :
      ∑ i, platformAdjointIntervalMass
        a xMinus xPlus sigmaMinus sigmaPlus (left i) (right i) = R0)
    (henergy : ∀ i,
      Real.log (platformCapacity a) +
          circleSelfEnergy
            (platformReferenceCircleRadius k a (left i) (right i)) +
          circleSelfEnergy
            (platformAdjointCircleRadius a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)) +
          circleSincSquareGap
            (platformReferenceCircleRadius k a (left i) (right i))
            (platformAdjointCircleRadius a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)) ≤
        energy i /
          (platformReferenceIntervalMass k a (left i) (right i) *
            platformAdjointIntervalMass a xMinus xPlus
              sigmaMinus sigmaPlus (left i) (right i)))
    (hmargin : ∀ i, 0 ≤ circleBlockMargin
      (platformCapacity a) (platformAPi k a)
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus) Ceff
      (platformReferenceCircleRadius k a (left i) (right i))
      (platformAdjointCircleRadius a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i)))
    (hcalibration :
      M0 + (Ceff - platformPotentialConstant k a) * R0 = L) :
    L ≤ M0 + ∑ i, blockRadiusExpression
      (platformReferenceIntervalMass k a (left i) (right i))
      (platformAdjointIntervalMass a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i))
      (platformPotentialConstant k a) (energy i) (targetRadius i) := by
  have hk0 : 0 ≤ k := le_trans (by norm_num) hk
  let q : ι → ℝ := fun i ↦
    platformReferenceIntervalMass k a (left i) (right i)
  let r : ι → ℝ := fun i ↦
    platformAdjointIntervalMass a xMinus xPlus
      sigmaMinus sigmaPlus (left i) (right i)
  have hQ : ∀ i, 0 <
      platformReferenceCircleRadius k a (left i) (right i) := by
    intro i
    exact platformReferenceCircleRadius_pos hk ha ha2 hthreshold
      (hleft i) (hlr i) (hright i)
  have hR : ∀ i, 0 <
      platformAdjointCircleRadius a xMinus xPlus
        sigmaMinus sigmaPlus (left i) (right i) := by
    intro i
    exact platformAdjointCircleRadius_pos
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
      (hleft i) (hlr i) (hright i)
  have hq : ∀ i, 0 < q i := by
    intro i
    dsimp only [q]
    rw [platformReferenceIntervalMass_eq_endpoint_mul_radius hk0 ha ha2.le]
    exact div_pos
      (mul_pos (platformAPi_pos hk0 ha ha2.le) (hQ i)) Real.pi_pos
  have hr : ∀ i, 0 < r i := by
    intro i
    dsimp only [r]
    rw [platformAdjointIntervalMass_eq_endpoint_mul_radius
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2]
    exact div_pos
      (mul_pos
        (platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2)
        (hR i)) Real.pi_pos
  have hblock : ∀ i,
      q i * r i * Real.log (q i * r i / 2) + Ceff * r i ≤ energy i := by
    intro i
    dsimp only [q, r]
    exact platformCircleBlock_energy_bound_of_margin_nonneg
      hk0 ha ha2 hxMinus hxPlus hsigmaMinus hsigmaPlus
      (hQ i) (hR i) (henergy i) (hmargin i)
  apply finite_block_reduction q r energy targetRadius
    hq hr hTargetRadius
  · simpa only [r] using! hAdjointMassSum
  · exact hblock
  · exact hcalibration

end

end Erdos1038
