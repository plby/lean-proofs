/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
import ErdosProblems.Erdos783.External.Erdos390.PoissonDickmanPerpetuity

namespace Erdos390

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

theorem poissonDickmanTotalMass_spacing_nonneg
    (e : PoissonDickmanGapSequence) :
    0 ≤
      poissonDickmanTotalMass
        (poissonDickmanSpacingConfiguration e) := by
  unfold poissonDickmanTotalMass
  exact tsum_nonneg fun n ↦
    (poissonDickmanSpacingConfiguration_mem_Ioc e n).1.le

/-- The unconditioned total mass is nonnegative almost surely. -/
theorem ae_poissonDickmanTotalMassLaw_nonneg :
    ∀ᵐ t : ℝ ∂poissonDickmanTotalMassLaw,
      0 ≤ t := by
  unfold poissonDickmanTotalMassLaw
  apply
    (ae_map_iff
      measurable_poissonDickmanTotalMass.aemeasurable
      measurableSet_Ici).2
  unfold poissonDickmanUnconditionedLaw
  apply
    (ae_map_iff
      measurable_poissonDickmanSpacingConfiguration.aemeasurable
      (measurableSet_Ici.preimage
        measurable_poissonDickmanTotalMass)).2
  exact ae_of_all _ <|
    poissonDickmanTotalMass_spacing_nonneg

/--
The total-mass law is absolutely continuous with respect to Lebesgue
measure.  This follows directly from the perpetuity representation:
conditioned on the tail total `t`, multiplication of the uniform
variable by the positive scale `1+t` preserves Lebesgue null sets.
-/
theorem poissonDickmanTotalMassLaw_absolutelyContinuous :
    poissonDickmanTotalMassLaw ≪ volume := by
  rw [poissonDickmanTotalMassLaw_perpetuity]
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hAZero
  rw [Measure.map_apply
    measurable_poissonDickmanPerpetuityMap hA]
  rw [Measure.prod_apply_symm
    (hA.preimage measurable_poissonDickmanPerpetuityMap)]
  have hsections :
      ∀ᵐ t : ℝ ∂poissonDickmanTotalMassLaw,
        poissonDickmanUnitUniformLaw
          ((fun x : ℝ ↦ (x, t)) ⁻¹'
            poissonDickmanPerpetuityMap ⁻¹' A) =
          0 := by
    filter_upwards
      [ae_poissonDickmanTotalMassLaw_nonneg] with t ht
    have hscale : 1 + t ≠ 0 := by
      positivity
    unfold poissonDickmanUnitUniformLaw
    apply le_antisymm
    · calc
        (volume.restrict (Ioc (0 : ℝ) 1))
            ((fun x : ℝ ↦ (x, t)) ⁻¹'
              poissonDickmanPerpetuityMap ⁻¹' A) ≤
            volume
              ((fun x : ℝ ↦ (x, t)) ⁻¹'
                poissonDickmanPerpetuityMap ⁻¹' A) :=
          Measure.restrict_le_self
            ((fun x : ℝ ↦ (x, t)) ⁻¹'
              poissonDickmanPerpetuityMap ⁻¹' A)
        _ = 0 := by
          unfold poissonDickmanPerpetuityMap
          change
            volume
                ((fun x : ℝ ↦ x * (1 + t)) ⁻¹' A) =
              0
          rw [Real.volume_preimage_mul_right
            hscale A, hAZero]
          simp
    · exact bot_le
  rw [lintegral_congr_ae hsections]
  simp

/--
Lebesgue density of a uniform random variable on `(0,c]`.  The
definition is globally measurable even for parameters outside the
positive range; only positive `c` is used probabilistically.
-/
def poissonDickmanScaledUniformDensity
    (c u : ℝ) : ℝ≥0∞ :=
  (Ioc (0 : ℝ) c).indicator
    (fun _ ↦ ENNReal.ofReal c⁻¹) u

theorem measurable_poissonDickmanScaledUniformDensity :
    Measurable
      (fun q : ℝ × ℝ ↦
        poissonDickmanScaledUniformDensity
          (1 + q.1) q.2) := by
  have hs :
      MeasurableSet
        {q : ℝ × ℝ |
          q.2 ∈ Ioc (0 : ℝ) (1 + q.1)} := by
    exact
      (measurableSet_lt measurable_const
        measurable_snd).inter
      (measurableSet_le measurable_snd
        (measurable_const.add measurable_fst))
  have hv :
      Measurable
        (fun q : ℝ × ℝ ↦
          ENNReal.ofReal (1 + q.1)⁻¹) := by
    exact
      Measurable.ennreal_ofReal
        ((measurable_const.add measurable_fst).inv)
  rw [show
      (fun q : ℝ × ℝ ↦
        poissonDickmanScaledUniformDensity
          (1 + q.1) q.2) =
        fun q ↦
          if q ∈
              {q : ℝ × ℝ |
                q.2 ∈ Ioc (0 : ℝ) (1 + q.1)}
          then ENNReal.ofReal (1 + q.1)⁻¹
          else 0 by
    funext q
    simp only [poissonDickmanScaledUniformDensity,
      indicator, mem_Ioc]
    rfl]
  exact hv.piecewise hs measurable_const

/--
Scaling the unit uniform law by a positive `c` gives the constant
density `1/c` on `(0,c]`.
-/
theorem map_mul_right_poissonDickmanUnitUniformLaw
    (c : ℝ) (hc : 0 < c) :
    poissonDickmanUnitUniformLaw.map
        (fun x : ℝ ↦ x * c) =
      volume.withDensity
        (poissonDickmanScaledUniformDensity c) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hpre :
      (fun x : ℝ ↦ x * c) ⁻¹'
          Ioc (0 : ℝ) c =
        Ioc 0 1 := by
    ext x
    simp only [mem_preimage, mem_Ioc]
    constructor
    · intro h
      constructor
      · exact pos_of_mul_pos_left h.1 hc.le
      · exact
          (mul_le_iff_le_one_left hc).mp h.2
    · intro h
      exact
        ⟨mul_pos h.1 hc,
          (mul_le_iff_le_one_left hc).mpr h.2⟩
  have hrestrict :=
    Measure.restrict_map
      (μ := volume)
      (f := fun x : ℝ ↦ x * c)
      (s := Ioc (0 : ℝ) c)
      (measurable_id.mul measurable_const)
      measurableSet_Ioc
  rw [hpre] at hrestrict
  calc
    poissonDickmanUnitUniformLaw.map
        (fun x : ℝ ↦ x * c) =
        (volume.map
          (fun x : ℝ ↦ x * c)).restrict
            (Ioc 0 c) := by
      unfold poissonDickmanUnitUniformLaw
      exact hrestrict.symm
    _ =
        (ENNReal.ofReal |c⁻¹| • volume).restrict
          (Ioc 0 c) := by
      rw [Real.map_volume_mul_right hc0]
    _ =
        ENNReal.ofReal c⁻¹ •
          volume.restrict (Ioc 0 c) := by
      rw [Measure.restrict_smul]
      rw [abs_of_pos (inv_pos.mpr hc)]
    _ =
        volume.withDensity
          (poissonDickmanScaledUniformDensity c) := by
      unfold poissonDickmanScaledUniformDensity
      rw [withDensity_indicator measurableSet_Ioc,
        withDensity_const]

/--
Explicit mixture density obtained from the perpetuity equation:
given tail total `t`, the new total is uniform on `(0,1+t]`.
-/
def poissonDickmanTotalDensityFormula
    (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ,
    poissonDickmanScaledUniformDensity (1 + t) u
    ∂poissonDickmanTotalMassLaw

theorem measurable_poissonDickmanTotalDensityFormula :
    Measurable poissonDickmanTotalDensityFormula := by
  unfold poissonDickmanTotalDensityFormula
  exact
    Measurable.lintegral_prod_left'
      measurable_poissonDickmanScaledUniformDensity

/--
The mixture formula is an actual everywhere-defined density for the
total-mass law.
-/
theorem withDensity_poissonDickmanTotalDensityFormula :
    volume.withDensity
        poissonDickmanTotalDensityFormula =
      poissonDickmanTotalMassLaw := by
  rw [poissonDickmanTotalMassLaw_perpetuity]
  apply Measure.ext
  intro A hA
  rw [withDensity_apply
      poissonDickmanTotalDensityFormula hA,
    Measure.map_apply
      measurable_poissonDickmanPerpetuityMap hA,
    Measure.prod_apply_symm
      (hA.preimage
        measurable_poissonDickmanPerpetuityMap)]
  let F : ℝ → ℝ → ℝ≥0∞ :=
    fun t u ↦
      A.indicator
        (fun u ↦
          poissonDickmanScaledUniformDensity
            (1 + t) u) u
  have hF :
      Measurable (Function.uncurry F) := by
    have hraw :=
      measurable_poissonDickmanScaledUniformDensity.indicator
        (hA.preimage measurable_snd)
    change
      Measurable
        ((Prod.snd ⁻¹' A).indicator
          (fun q : ℝ × ℝ ↦
            poissonDickmanScaledUniformDensity
              (1 + q.1) q.2))
    exact hraw
  calc
    (∫⁻ u : ℝ in A,
        poissonDickmanTotalDensityFormula u
        ∂volume) =
        ∫⁻ u : ℝ,
          A.indicator
            poissonDickmanTotalDensityFormula u
          ∂volume := by
      rw [lintegral_indicator hA]
    _ =
        ∫⁻ u : ℝ,
          ∫⁻ t : ℝ, F t u
            ∂poissonDickmanTotalMassLaw
          ∂volume := by
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ A
      · simp only [F, indicator_of_mem hu,
          poissonDickmanTotalDensityFormula]
      · simp only [F, indicator_of_notMem hu,
          lintegral_zero]
    _ =
        ∫⁻ t : ℝ,
          ∫⁻ u : ℝ, F t u ∂volume
          ∂poissonDickmanTotalMassLaw := by
      exact
        (lintegral_lintegral_swap
          (μ := poissonDickmanTotalMassLaw)
          (ν := volume)
          hF.aemeasurable).symm
    _ =
        ∫⁻ t : ℝ,
          poissonDickmanUnitUniformLaw
            ((fun x : ℝ ↦ (x, t)) ⁻¹'
              poissonDickmanPerpetuityMap ⁻¹' A)
          ∂poissonDickmanTotalMassLaw := by
      apply lintegral_congr_ae
      filter_upwards
        [ae_poissonDickmanTotalMassLaw_nonneg] with t ht
      have hscale : 0 < 1 + t := by
        linarith
      calc
        (∫⁻ u : ℝ, F t u ∂volume) =
            ∫⁻ u : ℝ in A,
              poissonDickmanScaledUniformDensity
                (1 + t) u ∂volume := by
          unfold F
          rw [lintegral_indicator hA]
        _ =
            (volume.withDensity
              (poissonDickmanScaledUniformDensity
                (1 + t))) A := by
          rw [withDensity_apply _ hA]
        _ =
            (poissonDickmanUnitUniformLaw.map
              (fun x : ℝ ↦ x * (1 + t))) A := by
          rw [map_mul_right_poissonDickmanUnitUniformLaw
            (1 + t) hscale]
        _ =
            poissonDickmanUnitUniformLaw
              ((fun x : ℝ ↦ (x, t)) ⁻¹'
                poissonDickmanPerpetuityMap ⁻¹' A) := by
          calc
            (poissonDickmanUnitUniformLaw.map
                (fun x : ℝ ↦ x * (1 + t))) A =
                poissonDickmanUnitUniformLaw
                  ((fun x : ℝ ↦ x * (1 + t)) ⁻¹' A) :=
              Measure.map_apply (by fun_prop) hA
            _ = _ := by
              congr 1
    _ = _ := rfl

/-- The canonical Radon--Nikodym density of the total-mass law. -/
def poissonDickmanTotalDensity (u : ℝ) : ℝ≥0∞ :=
  poissonDickmanTotalMassLaw.rnDeriv volume u

theorem measurable_poissonDickmanTotalDensity :
    Measurable poissonDickmanTotalDensity :=
  Measure.measurable_rnDeriv _ _

/-- The total-mass law is Lebesgue measure weighted by its density. -/
theorem withDensity_poissonDickmanTotalDensity :
    volume.withDensity poissonDickmanTotalDensity =
      poissonDickmanTotalMassLaw := by
  exact
    Measure.withDensity_rnDeriv_eq
      poissonDickmanTotalMassLaw volume
      poissonDickmanTotalMassLaw_absolutelyContinuous

theorem ae_poissonDickmanTotalDensity_eq_formula :
    poissonDickmanTotalDensity =ᵐ[volume]
      poissonDickmanTotalDensityFormula := by
  have hfinite :
      (∫⁻ u : ℝ,
        poissonDickmanTotalDensity u ∂volume) ≠ ∞ := by
    rw [show
        (∫⁻ u : ℝ,
          poissonDickmanTotalDensity u ∂volume) =
          (volume.withDensity
            poissonDickmanTotalDensity) univ by
      rw [withDensity_apply
        poissonDickmanTotalDensity MeasurableSet.univ]
      simp]
    rw [withDensity_poissonDickmanTotalDensity,
      measure_univ]
    simp
  apply
    (withDensity_eq_iff
      measurable_poissonDickmanTotalDensity.aemeasurable
      measurable_poissonDickmanTotalDensityFormula.aemeasurable
      hfinite).1
  rw [withDensity_poissonDickmanTotalDensity,
    withDensity_poissonDickmanTotalDensityFormula]

/--
For positive `u`, the explicit density is the tail integral over
`t ≥ u-1` of the reciprocal scale `1/(1+t)`.
-/
theorem poissonDickmanTotalDensityFormula_eq_tail
    {u : ℝ} (hu : 0 < u) :
    poissonDickmanTotalDensityFormula u =
      ∫⁻ t : ℝ in Ici (u - 1),
        ENNReal.ofReal (1 + t)⁻¹
        ∂poissonDickmanTotalMassLaw := by
  unfold poissonDickmanTotalDensityFormula
  rw [← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro t
  unfold poissonDickmanScaledUniformDensity
  simp only [indicator, mem_Ioc, mem_Ici]
  by_cases htu : u ≤ 1 + t
  · rw [if_pos ⟨hu, htu⟩,
      if_pos (by linarith)]
  · rw [if_neg (by exact fun h ↦ htu h.2),
      if_neg (by linarith)]

/--
Renewal equation written entirely in terms of the explicit density.
-/
theorem poissonDickmanTotalDensityFormula_eq_densityTail
    {u : ℝ} (hu : 0 < u) :
    poissonDickmanTotalDensityFormula u =
      ∫⁻ t : ℝ in Ici (u - 1),
        poissonDickmanTotalDensityFormula t *
          ENNReal.ofReal (1 + t)⁻¹
        ∂volume := by
  rw [poissonDickmanTotalDensityFormula_eq_tail hu]
  rw [← withDensity_poissonDickmanTotalDensityFormula]
  rw [restrict_withDensity measurableSet_Ici]
  rw [lintegral_withDensity_eq_lintegral_mul
    (volume.restrict (Ici (u - 1)))
    measurable_poissonDickmanTotalDensityFormula
    (by fun_prop)]
  rfl

theorem poissonDickmanTotalDensityFormula_of_nonpos
    {u : ℝ} (hu : u ≤ 0) :
    poissonDickmanTotalDensityFormula u = 0 := by
  unfold poissonDickmanTotalDensityFormula
  rw [show
      (fun t : ℝ ↦
        poissonDickmanScaledUniformDensity
          (1 + t) u) = 0 by
    funext t
    unfold poissonDickmanScaledUniformDensity
    simp only [indicator, mem_Ioc, Pi.zero_apply]
    rw [if_neg]
    exact fun h ↦ (not_lt_of_ge hu) h.1]
  exact lintegral_zero

/-- The explicit density integrates to one. -/
theorem lintegral_poissonDickmanTotalDensityFormula :
    ∫⁻ u : ℝ,
      poissonDickmanTotalDensityFormula u ∂volume =
      1 := by
  have h :=
    congrArg
      (fun μ : Measure ℝ ↦ μ univ)
      withDensity_poissonDickmanTotalDensityFormula
  rw [withDensity_apply
    poissonDickmanTotalDensityFormula
    MeasurableSet.univ] at h
  simp only [Measure.restrict_univ] at h
  simpa only [measure_univ] using h

theorem ae_poissonDickmanTotalDensityFormula_lt_top :
    ∀ᵐ u : ℝ ∂volume,
      poissonDickmanTotalDensityFormula u < ∞ := by
  apply ae_lt_top
    measurable_poissonDickmanTotalDensityFormula
  rw [lintegral_poissonDickmanTotalDensityFormula]
  simp

/-- The constant value of the total density on `(0,1]`. -/
def poissonDickmanDensityNormalizer : ℝ≥0∞ :=
  ∫⁻ t : ℝ,
    ENNReal.ofReal (1 + t)⁻¹
    ∂poissonDickmanTotalMassLaw

theorem poissonDickmanTotalDensityFormula_of_mem_unit
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    poissonDickmanTotalDensityFormula u =
      poissonDickmanDensityNormalizer := by
  unfold poissonDickmanTotalDensityFormula
  unfold poissonDickmanDensityNormalizer
  apply lintegral_congr_ae
  filter_upwards
    [ae_poissonDickmanTotalMassLaw_nonneg] with t ht
  unfold poissonDickmanScaledUniformDensity
  rw [indicator_of_mem]
  exact ⟨hu0, hu1.trans (by linarith)⟩

theorem poissonDickmanDensityNormalizer_le_one :
    poissonDickmanDensityNormalizer ≤ 1 := by
  unfold poissonDickmanDensityNormalizer
  calc
    (∫⁻ t : ℝ,
        ENNReal.ofReal (1 + t)⁻¹
        ∂poissonDickmanTotalMassLaw) ≤
        ∫⁻ _t : ℝ, 1
          ∂poissonDickmanTotalMassLaw := by
      apply lintegral_mono_ae
      filter_upwards
        [ae_poissonDickmanTotalMassLaw_nonneg] with t ht
      apply ENNReal.ofReal_le_one.mpr
      exact
        (inv_le_one₀ (by linarith : 0 < 1 + t)).2
          (by linarith)
    _ = 1 := by simp

theorem poissonDickmanDensityNormalizer_lt_top :
    poissonDickmanDensityNormalizer < ∞ :=
  poissonDickmanDensityNormalizer_le_one.trans_lt
    ENNReal.one_lt_top

theorem poissonDickmanDensityNormalizer_pos :
    0 < poissonDickmanDensityNormalizer := by
  unfold poissonDickmanDensityNormalizer
  let f : ℝ → ℝ≥0∞ :=
    fun t ↦ ENNReal.ofReal (1 + t)⁻¹
  have hf : Measurable f := by
    unfold f
    fun_prop
  rw [lintegral_pos_iff_support hf]
  have hsupp :
      Function.support f =ᵐ[poissonDickmanTotalMassLaw]
        (Set.univ : Set ℝ) := by
    filter_upwards
      [ae_poissonDickmanTotalMassLaw_nonneg] with t ht
    apply propext
    change ENNReal.ofReal (1 + t)⁻¹ ≠ 0 ↔ True
    rw [iff_true, ENNReal.ofReal_ne_zero_iff]
    exact inv_pos.mpr (by linarith)
  rw [measure_congr hsupp, measure_univ]
  exact zero_lt_one

theorem poissonDickmanTotalDensityFormula_pos_of_mem_unit
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    0 < poissonDickmanTotalDensityFormula u := by
  rw [poissonDickmanTotalDensityFormula_of_mem_unit
    hu0 hu1]
  exact poissonDickmanDensityNormalizer_pos

theorem poissonDickmanTotalDensityFormula_antitoneOn_pos
    {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) :
    poissonDickmanTotalDensityFormula u ≤
      poissonDickmanTotalDensityFormula v := by
  have hu : 0 < u := hv.trans_le hvu
  rw [poissonDickmanTotalDensityFormula_eq_tail hu,
    poissonDickmanTotalDensityFormula_eq_tail hv]
  apply lintegral_mono'
    (Measure.restrict_mono
      (show Ici (u - 1) ⊆ Ici (v - 1) by
        intro t ht
        exact mem_Ici.mpr <| by
          linarith [mem_Ici.mp ht])
      le_rfl)
    le_rfl

theorem poissonDickmanTotalDensityFormula_le_normalizer
    {u : ℝ} (hu : 0 < u) :
    poissonDickmanTotalDensityFormula u ≤
      poissonDickmanDensityNormalizer := by
  let v := min u 1
  have hv0 : 0 < v := by
    exact lt_min hu zero_lt_one
  have hv1 : v ≤ 1 := min_le_right _ _
  calc
    poissonDickmanTotalDensityFormula u ≤
        poissonDickmanTotalDensityFormula v :=
      poissonDickmanTotalDensityFormula_antitoneOn_pos
        hv0 (min_le_left _ _)
    _ = poissonDickmanDensityNormalizer :=
      poissonDickmanTotalDensityFormula_of_mem_unit
        hv0 hv1

theorem poissonDickmanTotalDensityFormula_lt_top
    {u : ℝ} (hu : 0 < u) :
    poissonDickmanTotalDensityFormula u < ∞ :=
  (poissonDickmanTotalDensityFormula_le_normalizer hu).trans_lt
    poissonDickmanDensityNormalizer_lt_top

end

end Erdos390
