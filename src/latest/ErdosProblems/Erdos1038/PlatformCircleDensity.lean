import ErdosProblems.Erdos1038.CircleBathtub
import ErdosProblems.Erdos1038.PlatformNormalizedDensities

/-!
# Platform densities on the logarithmic circle

This file forms the even, interval-supported circle densities from the
normalized platform reference and adjoint angular densities.  It discharges
their measurability and `[0,1]` bounds, then specializes the double
layer-cake terminal-shell bridge to these concrete functions.
-/

set_option warningAsError false

open Metric Set MeasureTheory
open scoped ENNReal

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Even radial extension to the circle of a real density supported on the
angular interval `[left,right]`. -/
def circleIntervalRadialDensity
    (density : ℝ → ℝ) (left right : ℝ) (z : AngleCircle) : ℝ :=
  (Icc left right).indicator density (dist z 0)

/-- Centered compression of an increasing density on `[left,right]`:
the outer endpoint is moved to the origin and the radial coordinate is
reversed. -/
def circleIntervalCenteredCompressionDensity
    (density : ℝ → ℝ) (left right : ℝ) (z : AngleCircle) : ℝ :=
  circleIntervalRadialDensity (fun u ↦ density (right - u))
    0 (right - left) z

lemma measurable_circleIntervalRadialDensity
    {density : ℝ → ℝ} (hdensity : Measurable density)
    (left right : ℝ) :
    Measurable (circleIntervalRadialDensity density left right) := by
  exact (hdensity.indicator measurableSet_Icc).comp
    (measurable_dist.comp (measurable_id.prodMk measurable_const))

lemma measurable_circleIntervalCenteredCompressionDensity
    {density : ℝ → ℝ} (hdensity : Measurable density)
    (left right : ℝ) :
    Measurable
      (circleIntervalCenteredCompressionDensity density left right) := by
  apply measurable_circleIntervalRadialDensity
  exact hdensity.comp (measurable_const.sub measurable_id)

lemma circleIntervalRadialDensity_nonneg
    {density : ℝ → ℝ} {left right : ℝ}
    (hdensity : ∀ theta ∈ Icc left right, 0 ≤ density theta) :
    ∀ z, 0 ≤ circleIntervalRadialDensity density left right z := by
  intro z
  by_cases hz : dist z 0 ∈ Icc left right
  · rw [circleIntervalRadialDensity, indicator_of_mem hz]
    exact hdensity _ hz
  · rw [circleIntervalRadialDensity, indicator_of_notMem hz]

lemma circleIntervalRadialDensity_le_one
    {density : ℝ → ℝ} {left right : ℝ}
    (hdensity : ∀ theta ∈ Icc left right, density theta ≤ 1) :
    ∀ z, circleIntervalRadialDensity density left right z ≤ 1 := by
  intro z
  by_cases hz : dist z 0 ∈ Icc left right
  · rw [circleIntervalRadialDensity, indicator_of_mem hz]
    exact hdensity _ hz
  · rw [circleIntervalRadialDensity, indicator_of_notMem hz]
    norm_num

lemma circleIntervalCenteredCompressionDensity_mem_Icc
    {density : ℝ → ℝ} {left right : ℝ}
    (hdensity : ∀ theta ∈ Icc left right, density theta ∈ Icc 0 1) :
    ∀ z, circleIntervalCenteredCompressionDensity
      density left right z ∈ Icc 0 1 := by
  intro z
  constructor
  · apply circleIntervalRadialDensity_nonneg
    intro u hu
    exact (hdensity (right - u) (by constructor <;> linarith [hu.1, hu.2])).1
  · apply circleIntervalRadialDensity_le_one
    intro u hu
    exact (hdensity (right - u) (by constructor <;> linarith [hu.1, hu.2])).2

lemma circleIntervalRadialDensity_superlevel_iff
    {density : ℝ → ℝ} {left right t : ℝ} (ht : 0 < t)
    (z : AngleCircle) :
    t < circleIntervalRadialDensity density left right z ↔
      dist z 0 ∈ Icc left right ∧ t < density (dist z 0) := by
  by_cases hz : dist z 0 ∈ Icc left right
  · rw [circleIntervalRadialDensity, indicator_of_mem hz]
    exact and_iff_right hz |>.symm
  · rw [circleIntervalRadialDensity, indicator_of_notMem hz]
    simp only [not_lt_of_ge ht.le, hz, false_and]

/-- Canonical lower endpoint of a strict superlevel set on an interval.
Adjoining `right` makes the definition valid also for empty superlevels. -/
def intervalSuperlevelLower
    (density : ℝ → ℝ) (left right t : ℝ) : ℝ :=
  sInf ({theta | theta ∈ Icc left right ∧ t < density theta} ∪ {right})

lemma intervalSuperlevelLower_mem_Icc
    (density : ℝ → ℝ) {left right t : ℝ} (hle : left ≤ right) :
    intervalSuperlevelLower density left right t ∈ Icc left right := by
  let S : Set ℝ :=
    {theta | theta ∈ Icc left right ∧ t < density theta} ∪ {right}
  have hright : right ∈ S := by
    exact Or.inr (mem_singleton right)
  have hnonempty : S.Nonempty := ⟨right, hright⟩
  have hlower : ∀ theta ∈ S, left ≤ theta := by
    intro theta htheta
    rcases htheta with htheta | htheta
    · exact htheta.1.1
    · rw [mem_singleton_iff] at htheta
      subst theta
      exact hle
  have hbdd : BddBelow S := ⟨left, hlower⟩
  change sInf S ∈ Icc left right
  exact ⟨le_csInf hnonempty hlower, csInf_le hbdd hright⟩

lemma intervalSuperlevel_iff_Icc_of_ne_lower
    {density : ℝ → ℝ} {left right t theta : ℝ}
    (hle : left ≤ right)
    (hmono : MonotoneOn density (Icc left right))
    (htheta : theta ≠ intervalSuperlevelLower density left right t) :
    (theta ∈ Icc left right ∧ t < density theta) ↔
      theta ∈ Icc (intervalSuperlevelLower density left right t) right := by
  let S : Set ℝ := {x | x ∈ Icc left right ∧ t < density x}
  let T : Set ℝ := S ∪ {right}
  have hright : right ∈ T := Or.inr (mem_singleton right)
  have hnonempty : T.Nonempty := ⟨right, hright⟩
  have hlowerBound : ∀ x ∈ T, left ≤ x := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.1.1
    · rw [mem_singleton_iff] at hx
      subst x
      exact hle
  have hbdd : BddBelow T := ⟨left, hlowerBound⟩
  have hcut : intervalSuperlevelLower density left right t ∈ Icc left right :=
    intervalSuperlevelLower_mem_Icc density hle
  change (theta ∈ S) ↔ theta ∈ Icc (sInf T) right
  constructor
  · intro hthetaS
    exact ⟨csInf_le hbdd (Or.inl hthetaS), hthetaS.1.2⟩
  · intro hthetaIcc
    have hcutTheta : sInf T < theta := lt_of_le_of_ne
      hthetaIcc.1 (by
        simpa only [intervalSuperlevelLower, T, S] using! htheta.symm)
    obtain ⟨x, hxT, hxTheta⟩ := exists_lt_of_csInf_lt hnonempty hcutTheta
    rcases hxT with hxS | hxRight
    · have hthetaOriginal : theta ∈ Icc left right :=
        ⟨hcut.1.trans hthetaIcc.1, hthetaIcc.2⟩
      exact ⟨hthetaOriginal,
        hxS.2.trans_le (hmono hxS.1 hthetaOriginal hxTheta.le)⟩
    · rw [mem_singleton_iff] at hxRight
      subst x
      exact (not_lt_of_ge hthetaIcc.2 hxTheta).elim

lemma circleIntervalRadialDensity_superlevel_ae_eq_radial
    {density : ℝ → ℝ} {left right t : ℝ}
    (ht : 0 < t) (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi)
    (hmono : MonotoneOn density (Icc left right)) :
    {z : AngleCircle | t < circleIntervalRadialDensity density left right z} =ᵐ[volume]
      {z : AngleCircle |
        dist z 0 ∈ Icc (intervalSuperlevelLower density left right t) right} := by
  have hcut := intervalSuperlevelLower_mem_Icc density (t := t) hle
  have hcut0 : 0 ≤ intervalSuperlevelLower density left right t :=
    hleft.trans hcut.1
  have hcutPi : intervalSuperlevelLower density left right t ≤ Real.pi :=
    hcut.2.trans hright
  have hnull := volume_radial_level_zero hcut0 hcutPi
  have hae : ∀ᵐ z ∂(volume : Measure AngleCircle),
      z ∉ {w : AngleCircle |
        dist w 0 ∈ Icc
          (intervalSuperlevelLower density left right t)
          (intervalSuperlevelLower density left right t)} := by
    rw [ae_iff]
    simpa only [Classical.not_not] using! hnull
  filter_upwards [hae] with z hz
  apply propext
  change t < circleIntervalRadialDensity density left right z ↔
    dist z 0 ∈ Icc (intervalSuperlevelLower density left right t) right
  rw [circleIntervalRadialDensity_superlevel_iff ht]
  apply intervalSuperlevel_iff_Icc_of_ne_lower hle hmono
  intro heq
  apply hz
  simp only [mem_Icc]
  exact ⟨heq.ge, heq.le⟩

/-- Every positive superlevel of the centered compression is, up to its
null boundary, the centered arc whose radius is the length of the original
terminal superlevel interval. -/
lemma circleIntervalCenteredCompressionDensity_superlevel_ae_eq_closedBall
    {density : ℝ → ℝ} {left right t : ℝ}
    (ht : 0 < t) (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi)
    (hmono : MonotoneOn density (Icc left right)) :
    {z : AngleCircle |
        t < circleIntervalCenteredCompressionDensity density left right z} =ᵐ[volume]
      closedBall (0 : AngleCircle)
        (right - intervalSuperlevelLower density left right t) := by
  let cut : ℝ := intervalSuperlevelLower density left right t
  have hcut : cut ∈ Icc left right := by
    exact intervalSuperlevelLower_mem_Icc density (t := t) hle
  have hradius0 : 0 ≤ right - cut := by linarith [hcut.2]
  have hradiusPi : right - cut ≤ Real.pi := by
    linarith [hleft.trans hcut.1]
  have hnull := volume_radial_level_zero hradius0 hradiusPi
  have hae : ∀ᵐ z ∂(volume : Measure AngleCircle),
      z ∉ {w : AngleCircle |
        dist w 0 ∈ Icc (right - cut) (right - cut)} := by
    rw [ae_iff]
    simpa only [Classical.not_not] using! hnull
  filter_upwards [hae] with z hz
  apply propext
  have hdistNe : dist z 0 ≠ right - cut := by
    intro heq
    apply hz
    simp only [mem_Icc]
    exact ⟨heq.ge, heq.le⟩
  have hthetaNe : right - dist z 0 ≠ cut := by
    intro heq
    apply hdistNe
    linarith
  change
    (t < circleIntervalRadialDensity
        (fun u ↦ density (right - u)) 0 (right - left) z) ↔ _
  rw [circleIntervalRadialDensity_superlevel_iff ht]
  have hsupport :
      (dist z 0 ∈ Icc 0 (right - left) ∧
          t < density (right - dist z 0)) ↔
        ((right - dist z 0) ∈ Icc left right ∧
          t < density (right - dist z 0)) := by
    constructor
    · rintro ⟨hu, hdensity⟩
      exact ⟨⟨by linarith [hu.2], by linarith [hu.1]⟩, hdensity⟩
    · rintro ⟨htheta, hdensity⟩
      exact ⟨⟨dist_nonneg, by linarith [htheta.1]⟩, hdensity⟩
  rw [hsupport,
    intervalSuperlevel_iff_Icc_of_ne_lower hle hmono hthetaNe]
  change
    (intervalSuperlevelLower density left right t ≤ right - dist z 0 ∧
        right - dist z 0 ≤ right) ↔
      dist z 0 ≤ right - intervalSuperlevelLower density left right t
  constructor
  · intro h
    linarith [h.1]
  · intro h
    exact ⟨by linarith,
      by linarith [show 0 ≤ dist z 0 from dist_nonneg]⟩

/-- The mixed logarithmic deficit of two centered interval compressions is
exactly the double layer cake of their centered superlevel arcs. -/
theorem circleDensityLogDeficit_centeredCompressions_eq_twoArcLayerCake
    {f g : ℝ → ℝ} {left right : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ theta ∈ Icc left right, 0 ≤ f theta)
    (hg0 : ∀ theta ∈ Icc left right, 0 ≤ g theta)
    (hmonoF : MonotoneOn f (Icc left right))
    (hmonoG : MonotoneOn g (Icc left right))
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    circleDensityLogDeficit
        (circleIntervalCenteredCompressionDensity f left right)
        (circleIntervalCenteredCompressionDensity g left right) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        circleLogTwoArcEnergy
          (right - intervalSuperlevelLower f left right t)
          (right - intervalSuperlevelLower g left right s) 0 := by
  have hfCentered : Measurable
      (circleIntervalCenteredCompressionDensity f left right) :=
    measurable_circleIntervalCenteredCompressionDensity hf left right
  have hgCentered : Measurable
      (circleIntervalCenteredCompressionDensity g left right) :=
    measurable_circleIntervalCenteredCompressionDensity hg left right
  have hfCentered0 : ∀ z,
      0 ≤ circleIntervalCenteredCompressionDensity f left right z := by
    intro z
    change 0 ≤ circleIntervalRadialDensity
      (fun u ↦ f (right - u)) 0 (right - left) z
    apply circleIntervalRadialDensity_nonneg
    intro u hu
    exact hf0 (right - u) (by constructor <;> linarith [hu.1, hu.2])
  have hgCentered0 : ∀ z,
      0 ≤ circleIntervalCenteredCompressionDensity g left right z := by
    intro z
    change 0 ≤ circleIntervalRadialDensity
      (fun u ↦ g (right - u)) 0 (right - left) z
    apply circleIntervalRadialDensity_nonneg
    intro u hu
    exact hg0 (right - u) (by constructor <;> linarith [hu.1, hu.2])
  rw [circleDensityLogDeficit_eq_lintegral_superlevels
    hfCentered hgCentered hfCentered0 hgCentered0]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hF :=
    circleIntervalCenteredCompressionDensity_superlevel_ae_eq_closedBall
      ht hleft hle hright hmonoF
  have hG :=
    circleIntervalCenteredCompressionDensity_superlevel_ae_eq_closedBall
      hs hleft hle hright hmonoG
  change circleSetLogDeficit
      {z | t < circleIntervalCenteredCompressionDensity f left right z}
      {z | s < circleIntervalCenteredCompressionDensity g left right z} = _
  rw [circleSetLogDeficit_congr hF hG]
  simpa using! circleSetLogDeficit_closedBalls_zero
    (right - intervalSuperlevelLower f left right t)
    (right - intervalSuperlevelLower g left right s) 0

lemma volume_intervalSuperlevel_eq_cut_length
    {density : ℝ → ℝ} {left right t : ℝ}
    (hle : left ≤ right)
    (hmono : MonotoneOn density (Icc left right)) :
    volume {theta : ℝ |
        theta ∈ Icc left right ∧ t < density theta} =
      ENNReal.ofReal
        (right - intervalSuperlevelLower density left right t) := by
  let cut : ℝ := intervalSuperlevelLower density left right t
  have hae : ∀ᵐ theta ∂(volume : Measure ℝ), theta ≠ cut :=
    Measure.ae_ne (volume : Measure ℝ) cut
  have hsets :
      {theta : ℝ | theta ∈ Icc left right ∧ t < density theta} =ᵐ[volume]
        Icc cut right := by
    filter_upwards [hae] with theta htheta
    apply propext
    exact intervalSuperlevel_iff_Icc_of_ne_lower hle hmono htheta
  rw [measure_congr hsets, Real.volume_Icc]

lemma volume_circleIntervalCenteredCompressionDensity_superlevel
    {density : ℝ → ℝ} {left right t : ℝ}
    (ht : 0 < t) (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi)
    (hmono : MonotoneOn density (Icc left right)) :
    volume {z : AngleCircle |
        t < circleIntervalCenteredCompressionDensity density left right z} =
      ENNReal.ofReal
        (2 * (right - intervalSuperlevelLower density left right t)) := by
  let radius : ℝ := right - intervalSuperlevelLower density left right t
  have hcut := intervalSuperlevelLower_mem_Icc density (t := t) hle
  have hradius0 : 0 ≤ radius := by
    dsimp only [radius]
    linarith [hcut.2]
  have hradiusPi : radius ≤ Real.pi := by
    dsimp only [radius]
    linarith [hleft.trans hcut.1]
  have hsets :=
    circleIntervalCenteredCompressionDensity_superlevel_ae_eq_closedBall
      ht hleft hle hright hmono
  rw [measure_congr hsets, AddCircle.volume_closedBall]
  have hmin : min (2 * Real.pi) (2 * radius) = 2 * radius := by
    exact min_eq_right (by linarith [hradiusPi])
  simp only [radius, hmin]

/-- Centered compression preserves the interval mass, with the factor two
coming from the two sides of the circle. -/
theorem lintegral_circleIntervalCenteredCompressionDensity
    {density : ℝ → ℝ} {left right : ℝ}
    (hdensity : Measurable density)
    (hdensity0 : ∀ theta ∈ Icc left right, 0 ≤ density theta)
    (hmono : MonotoneOn density (Icc left right))
    (hinterval : IntervalIntegrable density volume left right)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    (∫⁻ z : AngleCircle,
        ENNReal.ofReal
          (circleIntervalCenteredCompressionDensity density left right z)) =
      ENNReal.ofReal (2 * ∫ theta : ℝ in left..right, density theta) := by
  let centered : AngleCircle → ℝ :=
    circleIntervalCenteredCompressionDensity density left right
  let cutRadius : ℝ → ℝ := fun t ↦
    right - intervalSuperlevelLower density left right t
  have hcenteredMeas : Measurable centered :=
    measurable_circleIntervalCenteredCompressionDensity hdensity left right
  have hcentered0 : ∀ z, 0 ≤ centered z := by
    intro z
    change 0 ≤ circleIntervalRadialDensity
      (fun u ↦ density (right - u)) 0 (right - left) z
    apply circleIntervalRadialDensity_nonneg
    intro u hu
    exact hdensity0 (right - u)
      (by constructor <;> linarith [hu.1, hu.2])
  have hcenterLayer :
      (∫⁻ z : AngleCircle, ENNReal.ofReal (centered z)) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * cutRadius t) := by
    rw [lintegral_eq_lintegral_meas_lt volume
      (Filter.Eventually.of_forall hcentered0)
      hcenteredMeas.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact volume_circleIntervalCenteredCompressionDensity_superlevel
      ht hleft hle hright hmono
  let intervalMeasure : Measure ℝ :=
    (volume : Measure ℝ).restrict (Icc left right)
  have hdensity0Ae : ∀ᵐ theta ∂intervalMeasure, 0 ≤ density theta := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with theta htheta
    exact hdensity0 theta htheta
  have hintervalLayer :
      (∫⁻ theta in Icc left right, ENNReal.ofReal (density theta)) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cutRadius t) := by
    have hlayer := lintegral_eq_lintegral_meas_lt intervalMeasure
      hdensity0Ae hdensity.aemeasurable
    rw [hlayer]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    change intervalMeasure {theta : ℝ | t < density theta} = _
    rw [Measure.restrict_apply
      (measurableSet_lt measurable_const hdensity)]
    have hset : {theta : ℝ | t < density theta} ∩ Icc left right =
        {theta : ℝ | theta ∈ Icc left right ∧ t < density theta} := by
      ext theta
      simp only [mem_inter_iff, mem_ofPred_eq]
      tauto
    rw [hset, volume_intervalSuperlevel_eq_cut_length hle hmono]
  have hIntegrableOn : Integrable density
      ((volume : Measure ℝ).restrict (Icc left right)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp hinterval
  have hintervalIntegral :
      (∫⁻ theta in Icc left right, ENNReal.ofReal (density theta)) =
        ENNReal.ofReal (∫ theta : ℝ in left..right, density theta) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      hIntegrableOn hdensity0Ae]
    congr 1
    rw [intervalIntegral.integral_of_le hle,
      setIntegral_congr_set (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  calc
    (∫⁻ z : AngleCircle, ENNReal.ofReal
        (circleIntervalCenteredCompressionDensity density left right z)) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * cutRadius t) :=
      hcenterLayer
    _ = ∫⁻ t in Ioi (0 : ℝ),
          (2 : ℝ≥0∞) * ENNReal.ofReal (cutRadius t) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      change ENNReal.ofReal (2 * cutRadius t) =
        (2 : ℝ≥0∞) * ENNReal.ofReal (cutRadius t)
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ = (2 : ℝ≥0∞) *
        (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cutRadius t)) := by
      rw [lintegral_const_mul'
        (2 : ℝ≥0∞) (fun t ↦ ENNReal.ofReal (cutRadius t)) (by norm_num)]
    _ = (2 : ℝ≥0∞) *
        (∫⁻ theta in Icc left right,
          ENNReal.ofReal (density theta)) := by rw [hintervalLayer]
    _ = ENNReal.ofReal (2 * ∫ theta : ℝ in left..right, density theta) := by
      rw [hintervalIntegral,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

lemma measurable_platformNormalizedReferenceDensity (k a : ℝ) :
    Measurable (platformNormalizedReferenceDensity k a) := by
  unfold platformNormalizedReferenceDensity platformAngularDensity
    platformDensityCoefficient platformAngularDistance
  fun_prop

lemma measurable_platformNormalizedAdjointDensity
    (a xMinus xPlus sigmaMinus sigmaPlus : ℝ) :
    Measurable (platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus) := by
  unfold platformNormalizedAdjointDensity platformAngularAdjointDensity
    adjointNumerator platformAngularDistance
  fun_prop

/-- The manuscript density
`1_J(|theta|) A(|theta|) / a_pi` on the additive circle. -/
def platformReferenceCircleDensity
    (k a left right : ℝ) : AngleCircle → ℝ :=
  circleIntervalRadialDensity
    (platformNormalizedReferenceDensity k a) left right

/-- The manuscript density
`1_J(|theta|) B(|theta|) / b_pi` on the additive circle. -/
def platformAdjointCircleDensity
    (a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ) :
    AngleCircle → ℝ :=
  circleIntervalRadialDensity
    (platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus) left right

/-- Centered decreasing rearrangement of the platform reference density on
the chosen radial interval. -/
def platformReferenceCenteredCircleDensity
    (k a left right : ℝ) : AngleCircle → ℝ :=
  circleIntervalCenteredCompressionDensity
    (platformNormalizedReferenceDensity k a) left right

/-- Centered decreasing rearrangement of the platform adjoint density on
the chosen radial interval. -/
def platformAdjointCenteredCircleDensity
    (a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ) :
    AngleCircle → ℝ :=
  circleIntervalCenteredCompressionDensity
    (platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus) left right

/-- Canonical lower endpoints for the reference-density superlevels. -/
def platformReferenceSuperlevelLower
    (k a left right t : ℝ) : ℝ :=
  intervalSuperlevelLower
    (platformNormalizedReferenceDensity k a) left right t

/-- Canonical lower endpoints for the adjoint-density superlevels. -/
def platformAdjointSuperlevelLower
    (a xMinus xPlus sigmaMinus sigmaPlus left right t : ℝ) : ℝ :=
  intervalSuperlevelLower
    (platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus) left right t

lemma platformReferenceSuperlevelLower_mem_Icc
    (k a : ℝ) {left right t : ℝ} (hle : left ≤ right) :
    platformReferenceSuperlevelLower k a left right t ∈ Icc left right :=
  intervalSuperlevelLower_mem_Icc _ hle

lemma platformAdjointSuperlevelLower_mem_Icc
    (a xMinus xPlus sigmaMinus sigmaPlus : ℝ)
    {left right t : ℝ} (hle : left ≤ right) :
    platformAdjointSuperlevelLower
      a xMinus xPlus sigmaMinus sigmaPlus left right t ∈
        Icc left right :=
  intervalSuperlevelLower_mem_Icc _ hle

lemma measurable_platformReferenceCircleDensity
    (k a left right : ℝ) :
    Measurable (platformReferenceCircleDensity k a left right) := by
  exact measurable_circleIntervalRadialDensity
    (measurable_platformNormalizedReferenceDensity k a) left right

lemma measurable_platformAdjointCircleDensity
    (a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ) :
    Measurable (platformAdjointCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right) := by
  exact measurable_circleIntervalRadialDensity
    (measurable_platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus) left right

lemma measurable_platformReferenceCenteredCircleDensity
    (k a left right : ℝ) :
    Measurable (platformReferenceCenteredCircleDensity k a left right) :=
  measurable_circleIntervalCenteredCompressionDensity
    (measurable_platformNormalizedReferenceDensity k a) left right

lemma measurable_platformAdjointCenteredCircleDensity
    (a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ) :
    Measurable (platformAdjointCenteredCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right) :=
  measurable_circleIntervalCenteredCompressionDensity
    (measurable_platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus) left right

theorem platformReferenceCenteredCircleDensity_mem_Icc
    {k a left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hthreshold : platformThreshold k ≤ a)
    (hleft : 0 ≤ left) (hright : right ≤ Real.pi) :
    ∀ z, platformReferenceCenteredCircleDensity k a left right z ∈
      Icc (0 : ℝ) 1 := by
  apply circleIntervalCenteredCompressionDensity_mem_Icc
  intro theta htheta
  exact platformNormalizedReferenceDensity_mem_Icc
    hk ha ha2 hthreshold
    ⟨hleft.trans htheta.1, htheta.2.trans hright⟩

theorem platformAdjointCenteredCircleDensity_mem_Icc
    {a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hleft : 0 ≤ left)
    (hright : right ≤ Real.pi) :
    ∀ z, platformAdjointCenteredCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right z ∈ Icc (0 : ℝ) 1 := by
  apply circleIntervalCenteredCompressionDensity_mem_Icc
  intro theta htheta
  exact platformNormalizedAdjointDensity_mem_Icc
    hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
    ⟨hleft.trans htheta.1, htheta.2.trans hright⟩

lemma platformReferenceCenteredCircleDensity_superlevel_ae_eq_closedBall
    {k a left right t : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) (ht : 0 < t) :
    {z : AngleCircle |
        t < platformReferenceCenteredCircleDensity k a left right z} =ᵐ[volume]
      closedBall (0 : AngleCircle)
        (right - platformReferenceSuperlevelLower k a left right t) := by
  have hmono : MonotoneOn (platformNormalizedReferenceDensity k a)
      (Icc left right) :=
    (platformNormalizedReferenceDensity_monoOn hk ha ha2).mono
      (Icc_subset_Icc hleft hright)
  simpa only [platformReferenceCenteredCircleDensity,
    platformReferenceSuperlevelLower] using!
      circleIntervalCenteredCompressionDensity_superlevel_ae_eq_closedBall
        ht hleft hle hright hmono

lemma platformAdjointCenteredCircleDensity_superlevel_ae_eq_closedBall
    {a xMinus xPlus sigmaMinus sigmaPlus left right t : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) (ht : 0 < t) :
    {z : AngleCircle | t < platformAdjointCenteredCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right z} =ᵐ[volume]
      closedBall (0 : AngleCircle)
        (right - platformAdjointSuperlevelLower
          a xMinus xPlus sigmaMinus sigmaPlus left right t) := by
  have hmono : MonotoneOn
      (platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus) (Icc left right) :=
    (platformNormalizedAdjointDensity_strictMonoOn
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2).monotoneOn.mono
        (Icc_subset_Icc hleft hright)
  simpa only [platformAdjointCenteredCircleDensity,
    platformAdjointSuperlevelLower] using!
      circleIntervalCenteredCompressionDensity_superlevel_ae_eq_closedBall
        ht hleft hle hright hmono

theorem lintegral_platformReferenceCenteredCircleDensity
    {k a left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hthreshold : platformThreshold k ≤ a)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    (∫⁻ z : AngleCircle,
        ENNReal.ofReal
          (platformReferenceCenteredCircleDensity k a left right z)) =
      ENNReal.ofReal (2 * ∫ theta : ℝ in left..right,
        platformNormalizedReferenceDensity k a theta) := by
  have hsubset : uIcc left right ⊆ uIcc 0 Real.pi := by
    rw [uIcc_of_le hle, uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc hleft hright
  have hinterval : IntervalIntegrable
      (platformNormalizedReferenceDensity k a) volume left right :=
    (intervalIntegrable_platformNormalizedReferenceDensity k ha ha2).mono_set
      hsubset
  have hmono : MonotoneOn (platformNormalizedReferenceDensity k a)
      (Icc left right) :=
    (platformNormalizedReferenceDensity_monoOn hk ha ha2).mono
      (Icc_subset_Icc hleft hright)
  apply lintegral_circleIntervalCenteredCompressionDensity
    (measurable_platformNormalizedReferenceDensity k a) _ hmono hinterval
    hleft hle hright
  intro theta htheta
  exact (platformNormalizedReferenceDensity_mem_Icc
    hk ha ha2 hthreshold
    ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).1

theorem lintegral_platformAdjointCenteredCircleDensity
    {a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    (∫⁻ z : AngleCircle, ENNReal.ofReal
      (platformAdjointCenteredCircleDensity
        a xMinus xPlus sigmaMinus sigmaPlus left right z)) =
      ENNReal.ofReal (2 * ∫ theta : ℝ in left..right,
        platformNormalizedAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus theta) := by
  have hsubset : uIcc left right ⊆ uIcc 0 Real.pi := by
    rw [uIcc_of_le hle, uIcc_of_le Real.pi_pos.le]
    exact Icc_subset_Icc hleft hright
  have hinterval : IntervalIntegrable
      (platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus) volume left right :=
    (intervalIntegrable_platformNormalizedAdjointDensity
      hxMinus hxPlus ha2).mono_set hsubset
  have hmono : MonotoneOn
      (platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus) (Icc left right) :=
    (platformNormalizedAdjointDensity_strictMonoOn
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2).monotoneOn.mono
        (Icc_subset_Icc hleft hright)
  apply lintegral_circleIntervalCenteredCompressionDensity
    (measurable_platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus) _ hmono hinterval
    hleft hle hright
  intro theta htheta
  exact (platformNormalizedAdjointDensity_mem_Icc
    hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
    ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).1

theorem platformReferenceCircleDensity_mem_Icc
    {k a left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hthreshold : platformThreshold k ≤ a)
    (hleft : 0 ≤ left) (hright : right ≤ Real.pi) :
    ∀ z, platformReferenceCircleDensity k a left right z ∈ Icc 0 1 := by
  intro z
  constructor
  · apply circleIntervalRadialDensity_nonneg
    intro theta htheta
    exact (platformNormalizedReferenceDensity_mem_Icc
      hk ha ha2 hthreshold
      ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).1
  · apply circleIntervalRadialDensity_le_one
    intro theta htheta
    exact (platformNormalizedReferenceDensity_mem_Icc
      hk ha ha2 hthreshold
      ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).2

theorem platformAdjointCircleDensity_mem_Icc
    {a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hleft : 0 ≤ left)
    (hright : right ≤ Real.pi) :
    ∀ z, platformAdjointCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right z ∈ Icc 0 1 := by
  intro z
  constructor
  · apply circleIntervalRadialDensity_nonneg
    intro theta htheta
    exact (platformNormalizedAdjointDensity_mem_Icc
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
      ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).1
  · apply circleIntervalRadialDensity_le_one
    intro theta htheta
    exact (platformNormalizedAdjointDensity_mem_Icc
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
      ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).2

lemma platformReferenceCircleDensity_superlevel_ae_eq_terminalShell
    {k a left right t : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) (ht : 0 < t) :
    {z : AngleCircle | t < platformReferenceCircleDensity k a left right z} =ᵐ[volume]
      terminalShellSet
        (platformReferenceSuperlevelLower k a left right t) right := by
  have hmono : MonotoneOn (platformNormalizedReferenceDensity k a)
      (Icc left right) :=
    (platformNormalizedReferenceDensity_monoOn hk ha ha2).mono
      (Icc_subset_Icc hleft hright)
  have hradial := circleIntervalRadialDensity_superlevel_ae_eq_radial
    ht hleft hle hright hmono
  have hcut := platformReferenceSuperlevelLower_mem_Icc
    k a (t := t) hle
  have hshell := terminalShellSet_ae_eq_radial
    (hleft.trans hcut.1) hright
  have hradial' :
      {z : AngleCircle | t < platformReferenceCircleDensity k a left right z} =ᵐ[volume]
        {z : AngleCircle | dist z 0 ∈ Icc
          (platformReferenceSuperlevelLower k a left right t) right} := by
    simpa only [platformReferenceCircleDensity,
      platformReferenceSuperlevelLower] using! hradial
  exact hradial'.trans hshell.symm

lemma platformAdjointCircleDensity_superlevel_ae_eq_terminalShell
    {a xMinus xPlus sigmaMinus sigmaPlus left right t : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) (ht : 0 < t) :
    {z : AngleCircle | t < platformAdjointCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right z} =ᵐ[volume]
      terminalShellSet
        (platformAdjointSuperlevelLower
          a xMinus xPlus sigmaMinus sigmaPlus left right t) right := by
  have hmono : MonotoneOn
      (platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus) (Icc left right) :=
    (platformNormalizedAdjointDensity_strictMonoOn
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2).monotoneOn.mono
        (Icc_subset_Icc hleft hright)
  have hradial := circleIntervalRadialDensity_superlevel_ae_eq_radial
    ht hleft hle hright hmono
  have hcut := platformAdjointSuperlevelLower_mem_Icc
    a xMinus xPlus sigmaMinus sigmaPlus (t := t) hle
  have hshell := terminalShellSet_ae_eq_radial
    (hleft.trans hcut.1) hright
  have hradial' :
      {z : AngleCircle | t < platformAdjointCircleDensity
        a xMinus xPlus sigmaMinus sigmaPlus left right z} =ᵐ[volume]
        {z : AngleCircle | dist z 0 ∈ Icc
          (platformAdjointSuperlevelLower
            a xMinus xPlus sigmaMinus sigmaPlus left right t) right} := by
    simpa only [platformAdjointCircleDensity,
      platformAdjointSuperlevelLower] using! hradial
  exact hradial'.trans hshell.symm

/-- The previously residual four-arc hypothesis, now discharged for the
concrete normalized platform densities. -/
theorem platformCircleSuperlevelLogDeficit_eq_terminalShellCrossDeficit
    {k a xMinus xPlus sigmaMinus sigmaPlus left right t s : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) (ht : 0 < t) (hs : 0 < s) :
    circleSuperlevelLogDeficit
        (platformReferenceCircleDensity k a left right)
        (platformAdjointCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) t s =
      terminalShellCrossDeficit
        (platformReferenceSuperlevelLower k a left right t) right
        (platformAdjointSuperlevelLower
          a xMinus xPlus sigmaMinus sigmaPlus left right s) := by
  have hF := platformReferenceCircleDensity_superlevel_ae_eq_terminalShell
    hk ha ha2.le hleft hle hright ht
  have hG := platformAdjointCircleDensity_superlevel_ae_eq_terminalShell
    hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hle hright hs
  have hcutF := platformReferenceSuperlevelLower_mem_Icc
    k a (t := t) hle
  have hcutG := platformAdjointSuperlevelLower_mem_Icc
    a xMinus xPlus sigmaMinus sigmaPlus (t := s) hle
  exact circleSuperlevelLogDeficit_eq_terminalShellCrossDeficit
    hF hG (hleft.trans hcutF.1) (hleft.trans hcutG.1)
    hcutF.2 hcutG.2 hright

/-- Concrete platform-density rearrangement.  Its only remaining analytic
hypothesis is the exact four-arc evaluation of each pair of positive
superlevel sets; all density measurability, positivity, and the subsequent
two-variable Tonelli/compression steps are discharged here. -/
theorem platformCircleDensity_logDeficit_le_centeredTerminalShellLayerCake
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hright : right ≤ Real.pi)
    (lowerF lowerG : ℝ → ℝ)
    (hlowerF0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ lowerF t)
    (hlowerG0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ lowerG s)
    (hlowerFRight : ∀ t ∈ Ioi (0 : ℝ), lowerF t ≤ right)
    (hlowerGRight : ∀ s ∈ Ioi (0 : ℝ), lowerG s ≤ right)
    (hsuperlevel : ∀ t ∈ Ioi (0 : ℝ), ∀ s ∈ Ioi (0 : ℝ),
      circleSuperlevelLogDeficit
          (platformReferenceCircleDensity k a left right)
          (platformAdjointCircleDensity
            a xMinus xPlus sigmaMinus sigmaPlus left right) t s =
        terminalShellCrossDeficit (lowerF t) right (lowerG s)) :
    circleDensityLogDeficit
        (platformReferenceCircleDensity k a left right)
        (platformAdjointCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) ≤
      centeredTerminalShellLayerCakeDeficit lowerF lowerG right := by
  have hfBounds := platformReferenceCircleDensity_mem_Icc
    hk ha ha2.le hthreshold hleft hright
  have hgBounds := platformAdjointCircleDensity_mem_Icc
    hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hleft hright
  apply circleDensityLogDeficit_le_centeredTerminalShellLayerCake
    (measurable_platformReferenceCircleDensity k a left right)
    (measurable_platformAdjointCircleDensity
      a xMinus xPlus sigmaMinus sigmaPlus left right)
    (fun z ↦ (hfBounds z).1) (fun z ↦ (hgBounds z).1)
    lowerF lowerG right hlowerF0 hlowerG0
    hlowerFRight hlowerGRight hright
  intro t ht s hs
  exact (hsuperlevel t ht s hs).le

/-- Canonical-cut form of the platform rearrangement.  Compared with the
preceding theorem, all lower-endpoint choices and bound obligations have
been eliminated.  The residual hypothesis is exactly the geometric
four-arc evaluation of the concrete platform superlevels. -/
theorem platformCircleDensity_logDeficit_le_centeredCanonicalLayerCake
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi)
    (hsuperlevel : ∀ t ∈ Ioi (0 : ℝ), ∀ s ∈ Ioi (0 : ℝ),
      circleSuperlevelLogDeficit
          (platformReferenceCircleDensity k a left right)
          (platformAdjointCircleDensity
            a xMinus xPlus sigmaMinus sigmaPlus left right) t s =
        terminalShellCrossDeficit
          (platformReferenceSuperlevelLower k a left right t) right
          (platformAdjointSuperlevelLower
            a xMinus xPlus sigmaMinus sigmaPlus left right s)) :
    circleDensityLogDeficit
        (platformReferenceCircleDensity k a left right)
        (platformAdjointCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) ≤
      centeredTerminalShellLayerCakeDeficit
        (platformReferenceSuperlevelLower k a left right)
        (platformAdjointSuperlevelLower
          a xMinus xPlus sigmaMinus sigmaPlus left right) right := by
  apply platformCircleDensity_logDeficit_le_centeredTerminalShellLayerCake
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
    hleft hright
  · intro t _ht
    exact hleft.trans
      (platformReferenceSuperlevelLower_mem_Icc k a hle).1
  · intro s _hs
    exact hleft.trans
      (platformAdjointSuperlevelLower_mem_Icc
        a xMinus xPlus sigmaMinus sigmaPlus hle).1
  · intro t _ht
    exact (platformReferenceSuperlevelLower_mem_Icc k a hle).2
  · intro s _hs
    exact (platformAdjointSuperlevelLower_mem_Icc
      a xMinus xPlus sigmaMinus sigmaPlus hle).2
  · exact hsuperlevel

/-- Fully discharged terminal-shell rearrangement for the concrete
normalized platform densities. -/
theorem platformCircleDensity_logDeficit_le_centeredCanonicalLayerCake_unconditional
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
      centeredTerminalShellLayerCakeDeficit
        (platformReferenceSuperlevelLower k a left right)
        (platformAdjointSuperlevelLower
          a xMinus xPlus sigmaMinus sigmaPlus left right) right := by
  apply platformCircleDensity_logDeficit_le_centeredCanonicalLayerCake
    hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
    hleft hle hright
  intro t ht s hs
  exact platformCircleSuperlevelLogDeficit_eq_terminalShellCrossDeficit
    hk ha ha2 hxMinus hxPlus hsigmaMinus hsigmaPlus
    hleft hle hright ht hs

/-- Fully explicit centered-arc form of the platform rearrangement: each
pair of compressed superlevel sets has become one pair of full arcs centered
at the origin. -/
theorem platformCircleDensity_logDeficit_le_centeredTwoArcLayerCake
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
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        circleLogTwoArcEnergy
          (right - platformReferenceSuperlevelLower k a left right t)
          (right - platformAdjointSuperlevelLower
            a xMinus xPlus sigmaMinus sigmaPlus left right s) 0 := by
  let lowerF : ℝ → ℝ := platformReferenceSuperlevelLower k a left right
  let lowerG : ℝ → ℝ := platformAdjointSuperlevelLower
    a xMinus xPlus sigmaMinus sigmaPlus left right
  have hlowerF0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ lowerF t := by
    intro t _ht
    exact hleft.trans
      (platformReferenceSuperlevelLower_mem_Icc k a (t := t) hle).1
  have hlowerG0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ lowerG s := by
    intro s _hs
    exact hleft.trans
      (platformAdjointSuperlevelLower_mem_Icc
        a xMinus xPlus sigmaMinus sigmaPlus (t := s) hle).1
  have hlowerFRight : ∀ t ∈ Ioi (0 : ℝ), lowerF t ≤ right := by
    intro t _ht
    exact (platformReferenceSuperlevelLower_mem_Icc k a (t := t) hle).2
  have hlowerGRight : ∀ s ∈ Ioi (0 : ℝ), lowerG s ≤ right := by
    intro s _hs
    exact (platformAdjointSuperlevelLower_mem_Icc
      a xMinus xPlus sigmaMinus sigmaPlus (t := s) hle).2
  calc
    circleDensityLogDeficit
        (platformReferenceCircleDensity k a left right)
        (platformAdjointCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) ≤
        centeredTerminalShellLayerCakeDeficit lowerF lowerG right := by
      exact platformCircleDensity_logDeficit_le_centeredCanonicalLayerCake_unconditional
        hk ha ha2 hthreshold hxMinus hxPlus hsigmaMinus hsigmaPlus
        hleft hle hright
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
          circleLogTwoArcEnergy
            (right - lowerF t) (right - lowerG s) 0 :=
      centeredTerminalShellLayerCakeDeficit_eq_twoArcEnergy
        lowerF lowerG right hlowerF0 hlowerG0
        hlowerFRight hlowerGRight hright
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
          circleLogTwoArcEnergy
            (right - platformReferenceSuperlevelLower k a left right t)
            (right - platformAdjointSuperlevelLower
              a xMinus xPlus sigmaMinus sigmaPlus left right s) 0 := by
      rfl

/-- The centered canonical layer cake is the actual mixed deficit of the
two centered decreasing platform densities.  Thus the remaining comparison
with fixed-mass arcs is purely a bathtub principle. -/
theorem platformCenteredCanonicalLayerCakeDeficit_eq_centeredDensityLogDeficit
    {k a xMinus xPlus sigmaMinus sigmaPlus left right : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (hleft : 0 ≤ left) (hle : left ≤ right)
    (hright : right ≤ Real.pi) :
    centeredTerminalShellLayerCakeDeficit
        (platformReferenceSuperlevelLower k a left right)
        (platformAdjointSuperlevelLower
          a xMinus xPlus sigmaMinus sigmaPlus left right) right =
      circleDensityLogDeficit
        (platformReferenceCenteredCircleDensity k a left right)
        (platformAdjointCenteredCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) := by
  let lowerF : ℝ → ℝ := platformReferenceSuperlevelLower k a left right
  let lowerG : ℝ → ℝ := platformAdjointSuperlevelLower
    a xMinus xPlus sigmaMinus sigmaPlus left right
  have hlowerF0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ lowerF t := by
    intro t _ht
    exact hleft.trans
      (platformReferenceSuperlevelLower_mem_Icc k a (t := t) hle).1
  have hlowerG0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ lowerG s := by
    intro s _hs
    exact hleft.trans
      (platformAdjointSuperlevelLower_mem_Icc
        a xMinus xPlus sigmaMinus sigmaPlus (t := s) hle).1
  have hlowerFRight : ∀ t ∈ Ioi (0 : ℝ), lowerF t ≤ right := by
    intro t _ht
    exact (platformReferenceSuperlevelLower_mem_Icc k a (t := t) hle).2
  have hlowerGRight : ∀ s ∈ Ioi (0 : ℝ), lowerG s ≤ right := by
    intro s _hs
    exact (platformAdjointSuperlevelLower_mem_Icc
      a xMinus xPlus sigmaMinus sigmaPlus (t := s) hle).2
  have hmonoF : MonotoneOn (platformNormalizedReferenceDensity k a)
      (Icc left right) :=
    (platformNormalizedReferenceDensity_monoOn hk ha ha2.le).mono
      (Icc_subset_Icc hleft hright)
  have hmonoG : MonotoneOn
      (platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus) (Icc left right) :=
    (platformNormalizedAdjointDensity_strictMonoOn
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2).monotoneOn.mono
        (Icc_subset_Icc hleft hright)
  have hf0 : ∀ theta ∈ Icc left right,
      0 ≤ platformNormalizedReferenceDensity k a theta := by
    intro theta htheta
    exact (platformNormalizedReferenceDensity_mem_Icc
      hk ha ha2.le hthreshold
      ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).1
  have hg0 : ∀ theta ∈ Icc left right,
      0 ≤ platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus theta := by
    intro theta htheta
    exact (platformNormalizedAdjointDensity_mem_Icc
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
      ⟨hleft.trans htheta.1, htheta.2.trans hright⟩).1
  have henergy :=
    circleDensityLogDeficit_centeredCompressions_eq_twoArcLayerCake
      (measurable_platformNormalizedReferenceDensity k a)
      (measurable_platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus)
      hf0 hg0 hmonoF hmonoG hleft hle hright
  calc
    centeredTerminalShellLayerCakeDeficit
        (platformReferenceSuperlevelLower k a left right)
        (platformAdjointSuperlevelLower
          a xMinus xPlus sigmaMinus sigmaPlus left right) right =
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
          circleLogTwoArcEnergy (right - lowerF t) (right - lowerG s) 0 :=
      centeredTerminalShellLayerCakeDeficit_eq_twoArcEnergy
        lowerF lowerG right hlowerF0 hlowerG0
        hlowerFRight hlowerGRight hright
    _ = circleDensityLogDeficit
        (platformReferenceCenteredCircleDensity k a left right)
        (platformAdjointCenteredCircleDensity
          a xMinus xPlus sigmaMinus sigmaPlus left right) := by
      simpa only [lowerF, lowerG, platformReferenceSuperlevelLower,
        platformAdjointSuperlevelLower,
        platformReferenceCenteredCircleDensity,
        platformAdjointCenteredCircleDensity] using! henergy.symm

end

end Erdos1038
