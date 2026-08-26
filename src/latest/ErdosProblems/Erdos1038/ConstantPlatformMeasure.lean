import ErdosProblems.Erdos1038.ConstantPlatform


/-!
# The constant-platform reference density in angular coordinates

For `0 < a ≤ 2`, the affine cosine parametrization

`d(θ) = (a + 2) / 2 - (2 - a) / 2 * cos θ`

maps `[0, π]` onto `[a, 2]`.  This file records that parametrization and the
corresponding constant-platform density.
-/

open Set

namespace Erdos1038

noncomputable section

/-- The distance coordinate on the constant-platform interval. -/
def platformAngularDistance (a θ : ℝ) : ℝ :=
  platformCenter a - platformRadius a * Real.cos θ

/-- The constant-platform density, expressed in the angular coordinate. -/
def platformAngularDensity (k a θ : ℝ) : ℝ :=
  platformDensityCoefficient k a (platformAngularDistance a θ)

@[simp]
lemma platformAngularDistance_zero (a : ℝ) :
    platformAngularDistance a 0 = a := by
  simp [platformAngularDistance, platformCenter_sub_radius]

@[simp]
lemma platformAngularDistance_pi (a : ℝ) :
    platformAngularDistance a Real.pi = 2 := by
  simp [platformAngularDistance, platformCenter_add_radius]

lemma platformAngularDistance_mem_Icc {a θ : ℝ}
    (ha2 : a ≤ 2) (_hθ : θ ∈ Icc 0 Real.pi) :
    platformAngularDistance a θ ∈ Icc a 2 := by
  have hr : 0 ≤ platformRadius a := by
    simp [platformRadius]
    linarith
  have hcosLower : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hcosUpper : Real.cos θ ≤ 1 := Real.cos_le_one θ
  constructor
  · simp only [platformAngularDistance, platformCenter, platformRadius]
    nlinarith
  · simp only [platformAngularDistance, platformCenter, platformRadius]
    nlinarith

lemma platformAngularDistance_pos {a θ : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2) (hθ : θ ∈ Icc 0 Real.pi) :
    0 < platformAngularDistance a θ :=
  ha.trans_le (platformAngularDistance_mem_Icc ha2 hθ).1

lemma platformAngularDensity_nonneg {k a θ : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hthreshold : platformThreshold k ≤ a) (hθ : θ ∈ Icc 0 Real.pi) :
    0 ≤ platformAngularDensity k a θ := by
  apply (platformDensityCoefficient_nonneg_iff hk ha ha2).2 hthreshold
  exact platformAngularDistance_mem_Icc ha2 hθ

/-- A nonsingular primitive after centering the angular interval at the origin. -/
def platformReciprocalPrimitive (a x : ℝ) : ℝ :=
  2 / Real.sqrt (2 * a) *
    Real.arctan
      ((platformRadius a + platformCenter a * Real.tan (x / 2)) /
        Real.sqrt (2 * a))

private lemma platformCenter_sq_sub_radius_sq (a : ℝ) :
    platformCenter a ^ 2 - platformRadius a ^ 2 = 2 * a := by
  simp only [platformCenter, platformRadius]
  ring

private lemma platformReciprocalPrimitive_derivative_identity
    {a x : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (hx : x ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    2 / Real.sqrt (2 * a) *
          (1 /
              (1 +
                ((platformRadius a + platformCenter a * Real.tan (x / 2)) /
                    Real.sqrt (2 * a)) ^ 2) *
            ((platformCenter a * (1 / Real.cos (x / 2) ^ 2 * (1 / 2))) /
              Real.sqrt (2 * a))) =
      1 / (platformCenter a + platformRadius a * Real.sin x) := by
  have hs : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  have hsSq : Real.sqrt (2 * a) ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  rcases hx with ⟨hxLower, hxUpper⟩
  have hhalf : -(Real.pi / 2) < x / 2 ∧ x / 2 < Real.pi / 2 := by
    constructor <;> nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo hhalf
  have hsum :
      0 < 1 +
        ((platformRadius a + platformCenter a * Real.tan (x / 2)) /
          Real.sqrt (2 * a)) ^ 2 := by positivity
  have hr : 0 ≤ platformRadius a := by
    simp [platformRadius]
    linarith
  have hden : 0 < platformCenter a + platformRadius a * Real.sin x := by
    have hsin : -1 ≤ Real.sin x := Real.neg_one_le_sin x
    have hleft := platformCenter_sub_radius a
    nlinarith
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hs.ne', hc.ne', hsum.ne', hden.ne']
  rw [show Real.sin x =
      2 * Real.sin (x / 2) * Real.cos (x / 2) by
        rw [← Real.sin_two_mul]
        congr 2
        ring]
  have htrig := Real.sin_sq_add_cos_sq (x / 2)
  have hcr := platformCenter_sq_sub_radius_sq a
  nlinarith

lemma hasDerivAt_platformReciprocalPrimitive {a x : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2)
    (hx : x ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (platformReciprocalPrimitive a)
      (1 / (platformCenter a + platformRadius a * Real.sin x)) x := by
  have hs : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  rcases hx with ⟨hxLower, hxUpper⟩
  have hhalf : -(Real.pi / 2) < x / 2 ∧ x / 2 < Real.pi / 2 := by
    constructor <;> nlinarith [Real.pi_pos]
  have hc : Real.cos (x / 2) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo hhalf).ne'
  have ht : HasDerivAt (fun y : ℝ ↦ Real.tan (y / 2))
      (1 / Real.cos (x / 2) ^ 2 * (1 / 2)) x :=
    by
      convert! (Real.hasDerivAt_tan hc).comp x
        ((hasDerivAt_id x).div_const 2) using 1
  have hu : HasDerivAt
      (fun y : ℝ ↦
        (platformRadius a + platformCenter a * Real.tan (y / 2)) /
          Real.sqrt (2 * a))
      ((platformCenter a * (1 / Real.cos (x / 2) ^ 2 * (1 / 2))) /
        Real.sqrt (2 * a)) x := by
    convert! ((ht.const_mul (platformCenter a)).const_add (platformRadius a)).div_const
      (Real.sqrt (2 * a)) using 1
  have hfinal := hu.arctan.const_mul (2 / Real.sqrt (2 * a))
  rw [platformReciprocalPrimitive_derivative_identity ha ha2 ⟨hxLower, hxUpper⟩] at hfinal
  simpa only [platformReciprocalPrimitive] using! hfinal

private lemma platformShiftedDenominator_pos {a x : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2) :
    0 < platformCenter a + platformRadius a * Real.sin x := by
  have hr : 0 ≤ platformRadius a := by
    simp [platformRadius]
    linarith
  have hsin : -1 ≤ Real.sin x := Real.neg_one_le_sin x
  have hleft := platformCenter_sub_radius a
  nlinarith

private lemma intervalIntegrable_platformShiftedReciprocal {a : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2) :
    IntervalIntegrable
      (fun x : ℝ ↦ 1 / (platformCenter a + platformRadius a * Real.sin x))
      MeasureTheory.volume (-(Real.pi / 2)) (Real.pi / 2) := by
  apply ContinuousOn.intervalIntegrable
  exact continuousOn_const.div
    (continuousOn_const.add (continuousOn_const.mul Real.continuous_sin.continuousOn))
    (fun x _hx ↦ (platformShiftedDenominator_pos ha ha2).ne')

private lemma platformReciprocalPrimitive_endpoint_sub
    {a : ℝ} (ha : 0 < a) :
    platformReciprocalPrimitive a (Real.pi / 2) -
        platformReciprocalPrimitive a (-(Real.pi / 2)) =
      Real.pi / Real.sqrt (2 * a) := by
  have hs : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  have hsSq : Real.sqrt (2 * a) ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  have hplus : platformRadius a + platformCenter a = 2 := by
    simpa only [add_comm] using! platformCenter_add_radius a
  have hminus : platformRadius a - platformCenter a = -a := by
    linarith [platformCenter_sub_radius a]
  have hminusAdd : platformRadius a + -platformCenter a = -a := by
    simpa only [sub_eq_add_neg] using! hminus
  have hinv :
      a / Real.sqrt (2 * a) = (2 / Real.sqrt (2 * a))⁻¹ := by
    rw [inv_div]
    field_simp [hs.ne']
    nlinarith [Real.sq_sqrt (show 0 ≤ a * 2 by positivity)]
  have harctan := Real.arctan_inv_of_pos (show 0 < 2 / Real.sqrt (2 * a) by positivity)
  rw [← hinv] at harctan
  simp only [platformReciprocalPrimitive]
  rw [show (Real.pi / 2) / 2 = Real.pi / 4 by ring,
    Real.tan_pi_div_four]
  rw [show (-(Real.pi / 2)) / 2 = -(Real.pi / 4) by ring,
    Real.tan_neg, Real.tan_pi_div_four]
  simp only [mul_one, mul_neg]
  rw [hplus, hminusAdd]
  rw [neg_div, Real.arctan_neg]
  rw [harctan]
  field_simp [hs.ne']
  ring

lemma integral_platformShiftedReciprocal {a : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2) :
    (∫ x in (-(Real.pi / 2))..(Real.pi / 2),
        1 / (platformCenter a + platformRadius a * Real.sin x)) =
      Real.pi / Real.sqrt (2 * a) := by
  have horder : -(Real.pi / 2) ≤ Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hderiv : ∀ x ∈ uIcc (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (platformReciprocalPrimitive a)
        (1 / (platformCenter a + platformRadius a * Real.sin x)) x := by
    intro x hx
    rw [uIcc_of_le horder] at hx
    exact hasDerivAt_platformReciprocalPrimitive ha ha2 hx
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_platformShiftedReciprocal ha ha2)]
  exact platformReciprocalPrimitive_endpoint_sub ha

lemma intervalIntegrable_one_div_platformAngularDistance {a : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2) :
    IntervalIntegrable (fun θ : ℝ ↦ 1 / platformAngularDistance a θ)
      MeasureTheory.volume 0 Real.pi := by
  apply ContinuousOn.intervalIntegrable
  exact continuousOn_const.div
    (continuousOn_const.sub
      (continuousOn_const.mul Real.continuous_cos.continuousOn))
    (fun θ hθ ↦ by
      rw [uIcc_of_le Real.pi_pos.le] at hθ
      exact (platformAngularDistance_pos ha ha2 hθ).ne')

/-- The standard affine-cosine reciprocal integral. -/
theorem integral_one_div_platformAngularDistance {a : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2) :
    (∫ θ in 0..Real.pi, 1 / platformAngularDistance a θ) =
      Real.pi / Real.sqrt (2 * a) := by
  calc
    (∫ θ in 0..Real.pi, 1 / platformAngularDistance a θ) =
        ∫ x in (-(Real.pi / 2))..(Real.pi / 2),
          1 / platformAngularDistance a (x + Real.pi / 2) := by
      symm
      convert! intervalIntegral.integral_comp_add_right
        (a := -(Real.pi / 2)) (b := Real.pi / 2)
        (fun θ : ℝ ↦ 1 / platformAngularDistance a θ) (Real.pi / 2) using 1
      all_goals ring_nf
    _ = ∫ x in (-(Real.pi / 2))..(Real.pi / 2),
          1 / (platformCenter a + platformRadius a * Real.sin x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      simp only [platformAngularDistance, Real.cos_add, Real.cos_pi_div_two,
        mul_zero, Real.sin_pi_div_two, mul_one, zero_sub, mul_neg, sub_neg_eq_add]
    _ = Real.pi / Real.sqrt (2 * a) := integral_platformShiftedReciprocal ha ha2

lemma intervalIntegrable_platformAngularDensity (k : ℝ) {a : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2) :
    IntervalIntegrable (platformAngularDensity k a)
      MeasureTheory.volume 0 Real.pi := by
  have hrec := intervalIntegrable_one_div_platformAngularDistance ha ha2
  have hscaled := hrec.const_mul (k * Real.sqrt (2 * a))
  have hsub := (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ ↦ k + 1) MeasureTheory.volume 0 Real.pi).sub hscaled
  rw [show platformAngularDensity k a =
      fun θ : ℝ ↦ (k + 1) -
        (k * Real.sqrt (2 * a)) * (1 / platformAngularDistance a θ) by
      funext θ
      simp only [platformAngularDensity, platformDensityCoefficient, div_eq_mul_inv]
      ring]
  exact hsub

/-- The angular reference density has total mass `π`. -/
theorem integral_platformAngularDensity (k : ℝ) {a : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2) :
    (∫ θ in 0..Real.pi, platformAngularDensity k a θ) = Real.pi := by
  have hs : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  have hrec := intervalIntegrable_one_div_platformAngularDistance ha ha2
  have hscaled := hrec.const_mul (k * Real.sqrt (2 * a))
  rw [show platformAngularDensity k a =
      fun θ : ℝ ↦ (k + 1) -
        (k * Real.sqrt (2 * a)) * (1 / platformAngularDistance a θ) by
      funext θ
      simp only [platformAngularDensity, platformDensityCoefficient, div_eq_mul_inv]
      ring]
  rw [intervalIntegral.integral_sub intervalIntegrable_const hscaled,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_one_div_platformAngularDistance ha ha2]
  simp only [smul_eq_mul]
  field_simp [hs.ne']
  ring

/-- With the conventional factor `1 / π`, the angular reference density has mass one. -/
theorem normalized_integral_platformAngularDensity (k : ℝ) {a : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 2) :
    (1 / Real.pi) *
        (∫ θ in 0..Real.pi, platformAngularDensity k a θ) = 1 := by
  rw [integral_platformAngularDensity k ha ha2]
  exact one_div_mul_cancel Real.pi_ne_zero

/-- The normalized angular reference measure, before pushing it to the distance coordinate. -/
def platformAngularReferenceMeasure (k a : ℝ) : MeasureTheory.Measure ℝ :=
  (MeasureTheory.volume.restrict (Ioc 0 Real.pi)).withDensity
    (fun θ ↦ ENNReal.ofReal ((1 / Real.pi) * platformAngularDensity k a θ))

theorem platformAngularReferenceMeasure_apply_univ
    {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformAngularReferenceMeasure k a Set.univ = 1 := by
  let f : ℝ → ℝ := fun θ ↦ (1 / Real.pi) * platformAngularDensity k a θ
  have hfIntegrable :
      MeasureTheory.Integrable f
        (MeasureTheory.volume.restrict (Ioc 0 Real.pi)) := by
    exact (intervalIntegrable_platformAngularDensity k ha ha2).1.const_mul (1 / Real.pi)
  have hfNonneg :
      0 ≤ᵐ[MeasureTheory.volume.restrict (Ioc 0 Real.pi)] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le)
      (platformAngularDensity_nonneg hk ha ha2 hthreshold ⟨hθ.1.le, hθ.2⟩)
  have hfIntegral :
      (∫ θ, f θ ∂(MeasureTheory.volume.restrict (Ioc 0 Real.pi))) = 1 := by
    rw [← intervalIntegral.integral_of_le Real.pi_pos.le]
    rw [intervalIntegral.integral_const_mul,
      integral_platformAngularDensity k ha ha2]
    exact one_div_mul_cancel Real.pi_ne_zero
  rw [platformAngularReferenceMeasure, MeasureTheory.withDensity_apply _
    MeasurableSet.univ]
  simp only [MeasureTheory.Measure.restrict_univ]
  change (∫⁻ θ, ENNReal.ofReal (f θ)
    ∂(MeasureTheory.volume.restrict (Ioc 0 Real.pi))) = 1
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfIntegrable hfNonneg]
  rw [hfIntegral]
  norm_num

theorem platformAngularReferenceMeasure_compl_Ioc (k a : ℝ) :
    platformAngularReferenceMeasure k a (Ioc 0 Real.pi)ᶜ = 0 := by
  rw [platformAngularReferenceMeasure, MeasureTheory.withDensity_apply _
    measurableSet_Ioc.compl]
  simp

/-- The constant-platform reference measure in the distance coordinate. -/
def platformConstantReferenceMeasure (k a : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.map (platformAngularDistance a)
    (platformAngularReferenceMeasure k a)

theorem platformConstantReferenceMeasure_apply_univ
    {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hthreshold : platformThreshold k ≤ a) :
    platformConstantReferenceMeasure k a Set.univ = 1 := by
  have hdMeasurable : Measurable (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  rw [platformConstantReferenceMeasure, MeasureTheory.Measure.map_apply
    hdMeasurable MeasurableSet.univ, preimage_univ]
  exact platformAngularReferenceMeasure_apply_univ hk ha ha2 hthreshold

/-- The pushed reference measure is supported on the distance interval `[a, 2]`. -/
theorem platformConstantReferenceMeasure_compl_Icc
    (k : ℝ) {a : ℝ} (ha2 : a ≤ 2) :
    platformConstantReferenceMeasure k a (Icc a 2)ᶜ = 0 := by
  have hdMeasurable : Measurable (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  rw [platformConstantReferenceMeasure, MeasureTheory.Measure.map_apply
    hdMeasurable measurableSet_Icc.compl]
  apply le_antisymm
  · calc
      platformAngularReferenceMeasure k a
          (platformAngularDistance a ⁻¹' (Icc a 2)ᶜ) ≤
          platformAngularReferenceMeasure k a (Ioc 0 Real.pi)ᶜ := by
            apply MeasureTheory.measure_mono
            intro θ hθ
            change platformAngularDistance a θ ∉ Icc a 2 at hθ
            change θ ∉ Ioc 0 Real.pi
            intro hθIoc
            exact hθ (platformAngularDistance_mem_Icc ha2
              ⟨hθIoc.1.le, hθIoc.2⟩)
      _ = 0 := platformAngularReferenceMeasure_compl_Ioc k a
  · exact bot_le

theorem isProbabilityMeasure_platformConstantReferenceMeasure
    {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hthreshold : platformThreshold k ≤ a) :
    MeasureTheory.IsProbabilityMeasure (platformConstantReferenceMeasure k a) :=
  ⟨platformConstantReferenceMeasure_apply_univ hk ha ha2 hthreshold⟩

end

end Erdos1038
