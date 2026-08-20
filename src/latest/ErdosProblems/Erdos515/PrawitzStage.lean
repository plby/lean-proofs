import ErdosProblems.Erdos515.StageConstruction
import ErdosProblems.Erdos515.PrawitzProof
import ErdosProblems.Erdos515.RadialMaximal

/-!
# The concrete Prawitz stage for the Lewis--Rossi--Weitsman construction

This file packages the normalized-univalent Prawitz inequality and the exact
extended-real radial maximal theorem into the exceptional-set interface used by
`LRWPrawitzStageData`.  The logarithmic-area exceptional set is supplied by
`LogDerivative` below; keeping the two estimates separate makes it impossible
to accidentally replace an infinite radial supremum by a real number.
-/

open Metric MeasureTheory Set
open scoped ENNReal EReal Real

noncomputable section

namespace Erdos515
namespace PrawitzStage

open Prawitz Prawitz.RadialMaximal

/-- Affine normalization of a disk map at the origin. -/
def normalizedMap (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ (F z - F 0) / deriv F 0

@[simp] lemma normalizedMap_zero (F : ℂ → ℂ) : normalizedMap F 0 = 0 := by
  simp [normalizedMap]

lemma normalizedMap_analyticOnNhd {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hderiv : deriv F 0 ≠ 0) :
    AnalyticOnNhd ℂ (normalizedMap F) (ball 0 1) := by
  exact ((hF.analyticOnNhd isOpen_ball).sub analyticOnNhd_const).div
    analyticOnNhd_const (fun _ _ ↦ hderiv)

lemma normalizedMap_injOn {F : ℂ → ℂ}
    (hF : InjOn F (ball 0 1)) (hderiv : deriv F 0 ≠ 0) :
    InjOn (normalizedMap F) (ball 0 1) := by
  intro z hz w hw hzw
  apply hF hz hw
  change (F z - F 0) / deriv F 0 = (F w - F 0) / deriv F 0 at hzw
  have hsub : F z - F 0 = F w - F 0 := by
    calc
      F z - F 0 = ((F z - F 0) / deriv F 0) * deriv F 0 := by
        rw [div_mul_cancel₀ _ hderiv]
      _ = ((F w - F 0) / deriv F 0) * deriv F 0 := congrArg (fun x ↦ x * deriv F 0) hzw
      _ = F w - F 0 := div_mul_cancel₀ _ hderiv
  exact sub_left_inj.mp hsub

@[simp] lemma deriv_normalizedMap_zero {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hderiv : deriv F 0 ≠ 0) :
    deriv (normalizedMap F) 0 = 1 := by
  change deriv (fun z ↦ (F z - F 0) / deriv F 0) 0 = 1
  rw [deriv_div_const, deriv_sub_const_fun]
  exact div_self hderiv

lemma normalizedMap_differentiableOn {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hderiv : deriv F 0 ≠ 0) :
    DifferentiableOn ℂ (normalizedMap F) (ball 0 1) :=
  (normalizedMap_analyticOnNhd hF hderiv).differentiableOn

lemma original_eq_affine_normalizedMap {F : ℂ → ℂ} (hderiv : deriv F 0 ≠ 0)
    (z : ℂ) :
    F z = F 0 + deriv F 0 * normalizedMap F z := by
  unfold normalizedMap
  rw [mul_div_cancel₀ _ hderiv]
  abel

lemma shortPathRadialCurve_eq_affine_normalizedMap {F : ℂ → ℂ}
    (hderiv : deriv F 0 ≠ 0) (theta : ℝ) :
    shortPathRadialCurve F theta =
      (fun z ↦ F 0 + deriv F 0 * z) ∘
        shortPathRadialCurve (normalizedMap F) theta := by
  funext r
  exact original_eq_affine_normalizedMap hderiv _

/-- Affine normalization changes radial variation by at most the conformal-radius scale. -/
lemma eVariationOn_shortPathRadialCurve_le_normalized {F : ℂ → ℂ}
    (hderiv : deriv F 0 ≠ 0) (theta : ℝ) (s : Set ℝ) :
    eVariationOn (shortPathRadialCurve F theta) s ≤
      (‖deriv F 0‖₊ : ENNReal) *
        eVariationOn (shortPathRadialCurve (normalizedMap F) theta) s := by
  rw [shortPathRadialCurve_eq_affine_normalizedMap hderiv]
  have hLip : LipschitzWith ‖deriv F 0‖₊
      (fun z : ℂ ↦ F 0 + deriv F 0 * z) := by
    simpa [smul_eq_mul] using
      (LipschitzWith.const (F 0)).add (lipschitzWith_smul (deriv F 0))
  exact hLip.lipschitzOnWith.comp_eVariationOn_le (mapsTo_univ _ _)

/-- The fixed Hardy constant occurring in the complete radial maximal estimate. -/
def radialWeakConstant : ℝ := 49152 * hardyQuarterConstant

lemma hardyQuarterConstant_pos : 0 < hardyQuarterConstant := by
  unfold hardyQuarterConstant
  apply lt_max_of_lt_left
  positivity

lemma radialWeakConstant_pos : 0 < radialWeakConstant := by
  exact mul_pos (by norm_num) hardyQuarterConstant_pos

/-- A fixed threshold whose weak-`L¹` bound is strictly below `π/4`. -/
def radialThresholdBase : ℝ := 1 + 4 * radialWeakConstant / Real.pi

def radialThreshold : ℝ := radialThresholdBase ^ 4

lemma radialThresholdBase_pos : 0 < radialThresholdBase := by
  unfold radialThresholdBase
  have hA : 0 < radialWeakConstant := radialWeakConstant_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

lemma radialThreshold_pos : 0 < radialThreshold := by
  unfold radialThreshold
  exact pow_pos radialThresholdBase_pos 4

lemma radialThreshold_rpow_neg_quarter :
    radialThreshold ^ (-quarter) = radialThresholdBase⁻¹ := by
  rw [radialThreshold, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (le_of_lt radialThresholdBase_pos)]
  norm_num [quarter]
  rw [Real.rpow_neg_one]

lemma radialWeakConstant_mul_threshold_lt :
    radialWeakConstant * radialThreshold ^ (-quarter) < Real.pi / 4 := by
  rw [radialThreshold_rpow_neg_quarter]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < radialThresholdBase := radialThresholdBase_pos
  rw [inv_eq_one_div, mul_one_div]
  apply (div_lt_iff₀ hden).2
  have heq : Real.pi / 4 * radialThresholdBase =
      Real.pi / 4 + radialWeakConstant := by
    unfold radialThresholdBase
    field_simp [ne_of_gt hpi]
  rw [heq]
  linarith

/-- The exact radial exceptional set.  We also discard `0`, the endpoint used by Hall's
half-open angular interval; this singleton has zero measure and its periodic representative is
`2π`, the endpoint used by Prawitz's half-open interval. -/
def radialBad (G : ℂ → ℂ) : Set ℝ :=
  radialQuotientBadDirections G radialThreshold ∪ {0}

lemma volume_radialBad {G : ℂ → ℂ} :
    volume (radialBad G) =
      volume (radialQuotientBadDirections G radialThreshold) := by
  rw [radialBad, measure_union (by
    rw [disjoint_singleton_right]
    simp [radialQuotientBadDirections, angularInterval])
      (measurableSet_singleton (0 : ℝ))]
  simp

/-- Prawitz and Hardy--Littlewood give the required strict radial exceptional-set budget. -/
theorem volume_radialBad_lt_quarter {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1)
    (hHardy : HardyQuarterBound G hardyQuarterConstant) :
    volume (radialBad G) < ENNReal.ofReal (Real.pi / 4) := by
  have hle := measure_radialQuotientBadDirections_le hG.differentiableOn hG0
    (by simpa [hdG0]) hinj hHardy radialThreshold_pos
  rw [volume_radialBad]
  refine hle.trans_lt ?_
  exact ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < Real.pi / 4) |>.2
    radialWeakConstant_mul_threshold_lt

theorem volume_radialBad_lt_quarter_of_normalized_univalent {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1) :
    volume (radialBad G) < ENNReal.ofReal (Real.pi / 4) :=
  volume_radialBad_lt_quarter hG hinj hG0 hdG0
    (PrawitzProof.hardyQuarterBound_of_normalized_univalent hG hinj hG0 hdG0)

/-- Outside the exact exceptional set, every normalized radial quotient is below the fixed
threshold. -/
lemma radialQuotient_le_threshold {G : ℂ → ℂ} {theta r : ℝ}
    (htheta : theta ∈ angleDomain) (hbad : theta ∉ radialBad G)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    radialQuotient G r theta ≤ radialThreshold := by
  have htheta0 : theta ≠ 0 := by
    intro h
    apply hbad
    simp [radialBad, h]
  have hang : theta ∈ angularInterval := by
    rcases htheta with ⟨htheta0', htheta2⟩
    exact ⟨lt_of_le_of_ne htheta0' (Ne.symm htheta0), htheta2.le⟩
  have hnexist : ¬ ∃ s ∈ Ioo (0 : ℝ) 1,
      radialThreshold < radialQuotient G s theta := by
    intro hex
    apply hbad
    exact Or.inl ⟨hang, hex⟩
  exact le_of_not_gt fun h ↦ hnexist ⟨r, hr, h⟩

/-- Package a normalized radial-variation estimate together with the unconditional Prawitz
exceptional set.  The affine-normalization lemma inserts exactly the conformal-radius factor
required by `LRWPrawitzStageData`. -/
noncomputable def prawitzStageData_of_normalized_variation
    {u : ℂ → ℝ} {base : ℂ} {delta constant : ℝ}
    {a : LRWAdmissiblePoint delta u base} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hFinj : InjOn F (ball 0 1)) (hderiv : deriv F 0 ≠ 0)
    (logBadSet : Set ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hlogArea : volume logBadSet < ENNReal.ofReal (Real.pi / 4))
    (hvariation : ∀ theta ∈ angleDomain,
      theta ∉ radialBad (normalizedMap F) → theta ∉ logBadSet →
      eVariationOn (shortPathRadialCurve (normalizedMap F) theta) (Ico (0 : ℝ) 1) ≤
        ENNReal.ofReal (radialThreshold * J))
    (hconstant : 4 * radialThreshold * J ≤ constant) :
    LRWPrawitzStageData u base delta constant a F where
  radialBad := radialBad (normalizedMap F)
  logBad := logBadSet
  K := radialThreshold
  J := J
  K_nonneg := radialThreshold_pos.le
  J_nonneg := hJ
  prawitz := volume_radialBad_lt_quarter_of_normalized_univalent
    (normalizedMap_analyticOnNhd hF hderiv) (normalizedMap_injOn hFinj hderiv)
    (normalizedMap_zero F) (deriv_normalizedMap_zero hF hderiv)
  logArea := hlogArea
  variation := by
    intro theta htheta hradial hlog
    calc
      eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) ≤
          (‖deriv F 0‖₊ : ENNReal) *
            eVariationOn (shortPathRadialCurve (normalizedMap F) theta) (Ico (0 : ℝ) 1) :=
        eVariationOn_shortPathRadialCurve_le_normalized hderiv theta _
      _ ≤ (‖deriv F 0‖₊ : ENNReal) *
          ENNReal.ofReal (radialThreshold * J) :=
        mul_le_mul le_rfl (hvariation theta htheta hradial hlog) bot_le bot_le
      _ = ENNReal.ofReal (radialThreshold * ‖deriv F 0‖ * J) := by
        rw [ENNReal.coe_nnreal_eq]
        simp only [coe_nnnorm]
        rw [← ENNReal.ofReal_mul (norm_nonneg _)]
        congr 1
        ring
  constant_bound := hconstant

end PrawitzStage
end Erdos515
