import ErdosProblems.Erdos1002.NaturalCutoffComparisonAsymptotic
import ErdosProblems.Erdos1002.ReconstructionEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set Finset
open scoped ENNReal Topology ComplexConjugate BigOperators Real

namespace Erdos1002

noncomputable section

/-- Pullback from the unit additive circle to the real fundamental interval. -/
def unitCircleL2Pullback (f : UnitCircleL2) (alpha : ℝ) : ℂ :=
  (f : AddCircle (1 : ℝ) → ℂ) (alpha : AddCircle (1 : ℝ))

theorem measurePreserving_unitCircleMk_uniform01 :
    MeasurePreserving
      (fun alpha : ℝ ↦ (alpha : AddCircle (1 : ℝ)))
      uniform01Measure
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  rw [uniform01Measure, restrict_Ioo_eq_restrict_Ioc]
  have hvolume :
      (volume : Measure (AddCircle (1 : ℝ))) =
        (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
    simpa using!
      (@AddCircle.volume_eq_smul_haarAddCircle (1 : ℝ) inferInstance)
  rw [← hvolume]
  simpa using! UnitAddCircle.measurePreserving_mk 0

theorem eLpNorm_unitCircleL2Pullback (f : UnitCircleL2) :
    eLpNorm (unitCircleL2Pullback f) 2 uniform01Measure = ‖f‖ₑ := by
  have hcomp := eLpNorm_comp_measurePreserving
    (p := (2 : ℝ≥0∞)) (Lp.aestronglyMeasurable f)
    measurePreserving_unitCircleMk_uniform01
  change eLpNorm
      ((f : AddCircle (1 : ℝ) → ℂ) ∘
        (fun alpha : ℝ ↦ (alpha : AddCircle (1 : ℝ))))
      2 uniform01Measure = ‖f‖ₑ
  rw [hcomp]
  exact (Lp.enorm_def f).symm

theorem aestronglyMeasurable_unitCircleL2Pullback (f : UnitCircleL2) :
    AEStronglyMeasurable (unitCircleL2Pullback f) uniform01Measure := by
  exact (Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
    measurePreserving_unitCircleMk_uniform01.quasiMeasurePreserving

theorem unitCircleL2Pullback_sub_ae (f g : UnitCircleL2) :
    unitCircleL2Pullback (f - g) =ᵐ[uniform01Measure]
      unitCircleL2Pullback f - unitCircleL2Pullback g := by
  have h :=
    measurePreserving_unitCircleMk_uniform01.quasiMeasurePreserving.ae
      (Lp.coeFn_sub f g)
  simpa only [unitCircleL2Pullback, Function.comp_apply, Pi.sub_apply] using! h

theorem unitCircleL2Pullback_smul_ae (c : ℂ) (f : UnitCircleL2) :
    unitCircleL2Pullback (c • f) =ᵐ[uniform01Measure]
      fun alpha ↦ c * unitCircleL2Pullback f alpha := by
  have h :=
    measurePreserving_unitCircleMk_uniform01.quasiMeasurePreserving.ae
      (Lp.coeFn_smul c f)
  simpa only [unitCircleL2Pullback, Function.comp_apply, Pi.smul_apply,
    smul_eq_mul] using! h

private theorem sawtoothCircle_coe_all (x : ℝ) :
    sawtoothCircle (x : AddCircle (1 : ℝ)) = (sawtooth x : ℂ) := by
  let f : ℝ → ℂ := fun y ↦ (sawtooth y : ℂ)
  have hf : Function.Periodic f 1 := by
    intro y
    exact congrArg (fun z : ℝ ↦ (z : ℂ)) (sawtooth_periodic y)
  have heq : sawtoothCircle = hf.lift := by
    ext q
    obtain ⟨y, hy, rfl⟩ := by
      simpa only [Set.mem_image] using!
        (AddCircle.coe_image_Ioc_eq (1 : ℝ) 0 ▸ (mem_univ q))
    norm_num at hy
    rw [sawtoothCircle_coe hy, Function.Periodic.lift_coe]
  rw [heq, Function.Periodic.lift_coe]

theorem rotationSumCircleFunction_coe_real (N : ℕ) (alpha : ℝ) :
    rotationSumCircleFunction N (alpha : AddCircle (1 : ℝ)) =
      (rotationSum N alpha : ℂ) := by
  classical
  unfold rotationSumCircleFunction rotationSum
  have hset : Finset.Icc 1 N = (Finset.range N).image (fun k ↦ k + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      refine ⟨k - 1, ?_, ?_⟩ <;> omega
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hset, Finset.sum_image]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hdil :
      positiveCircleDilation ⟨k + 1, Nat.succ_pos k⟩
          (alpha : AddCircle (1 : ℝ)) =
        (((k + 1 : ℕ) : ℝ) * alpha : AddCircle (1 : ℝ)) := by
    unfold positiveCircleDilation
    rw [← AddCircle.coe_zsmul]
    congr 1
    simp [zsmul_eq_mul]
  rw [hdil, sawtoothCircle_coe_all]
  norm_num
  intro a _ha b _hb hab
  simpa using! hab

theorem allDenominatorReconstructionCircle_coe_real
    (N : ℕ+) (alpha : ℝ) :
    allDenominatorReconstructionCircle N (alpha : AddCircle (1 : ℝ)) =
      (allDenominatorRealReconstruction (N : ℕ) alpha : ℂ) := by
  rw [allDenominatorReconstructionCircle,
    rotationSumCircleFunction_coe_real]
  have hdil : positiveCircleDilation N (alpha : AddCircle (1 : ℝ)) =
      (((N : ℕ) : ℝ) * alpha : AddCircle (1 : ℝ)) := by
    unfold positiveCircleDilation
    rw [← AddCircle.coe_zsmul]
    congr 1
    simp [zsmul_eq_mul]
  rw [hdil, sawtoothCircle_coe_all]
  unfold allDenominatorRealReconstruction
  push_cast
  ring

theorem unitCircleL2Pullback_allDenominator_ae (N : ℕ+) :
    unitCircleL2Pullback (allDenominatorReconstructionL2 N) =ᵐ[uniform01Measure]
      fun alpha ↦ (allDenominatorRealReconstruction (N : ℕ) alpha : ℂ) := by
  have h :=
    measurePreserving_unitCircleMk_uniform01.quasiMeasurePreserving.ae
      (allDenominatorReconstructionL2_coe_ae N)
  filter_upwards [h] with alpha halpha
  change
    (allDenominatorReconstructionL2 N : AddCircle (1 : ℝ) → ℂ)
        (alpha : AddCircle (1 : ℝ)) = _
  rw [halpha, allDenominatorReconstructionCircle_coe_real]

/-- The all-denominator class is already negligible relative to the literal
natural cutoff `P = N` after the manuscript normalization. -/
theorem tendsto_norm_allDenominator_sub_naturalCutoff_div_log :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        ‖allDenominatorReconstructionL2 N -
            naturalCutoffReconstructionL2 N (N : ℕ)‖ /
          Real.log (N : ℝ))
      atTop (nhds 0) := by
  let E : ℕ → ℝ := fun m ↦
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    ‖allDenominatorReconstructionL2 N -
        naturalCutoffReconstructionL2 N (N : ℕ)‖ /
      Real.log (N : ℝ)
  let B : ℕ → ℝ := fun m ↦
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    ‖allDenominatorReconstructionL2 N -
        naturalCutoffReconstructionL2 N
          (manuscriptOuterCutoff (N : ℕ))‖ /
        Real.log (N : ℝ) +
      ‖naturalCutoffReconstructionL2 N
          (manuscriptOuterCutoff (N : ℕ)) -
        naturalCutoffReconstructionL2 N (N : ℕ)‖ /
          Real.log (N : ℝ)
  have hB : Tendsto B atTop (nhds 0) := by
    have hsum :=
      tendsto_norm_allDenominator_sub_manuscriptOuterCutoff_div_log.add
        tendsto_norm_manuscriptOuterCutoff_sub_naturalCutoff_div_log
    simpa only [B, zero_add] using! hsum
  have hlog : Tendsto
      (fun m : ℕ ↦ Real.log (((m + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  change Tendsto E atTop (nhds 0)
  apply squeeze_zero'
  · filter_upwards [hlog.eventually_gt_atTop 0] with m hm
    exact div_nonneg (norm_nonneg _) hm.le
  · filter_upwards [hlog.eventually_gt_atTop 0] with m hm
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    let Fall : UnitCircleL2 := allDenominatorReconstructionL2 N
    let Fouter : UnitCircleL2 :=
      naturalCutoffReconstructionL2 N (manuscriptOuterCutoff (N : ℕ))
    let Fnatural : UnitCircleL2 := naturalCutoffReconstructionL2 N (N : ℕ)
    have htri : ‖Fall - Fnatural‖ ≤
        ‖Fall - Fouter‖ + ‖Fouter - Fnatural‖ := by
      have hdecomp : Fall - Fnatural = (Fall - Fouter) + (Fouter - Fnatural) := by
        abel
      rw [hdecomp]
      exact norm_add_le _ _
    change
      ‖Fall - Fnatural‖ / Real.log (N : ℝ) ≤
        ‖Fall - Fouter‖ / Real.log (N : ℝ) +
          ‖Fouter - Fnatural‖ / Real.log (N : ℝ)
    calc
      ‖Fall - Fnatural‖ / Real.log (N : ℝ) ≤
          (‖Fall - Fouter‖ + ‖Fouter - Fnatural‖) /
            Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right htri hm.le
      _ = ‖Fall - Fouter‖ / Real.log (N : ℝ) +
          ‖Fouter - Fnatural‖ / Real.log (N : ℝ) := by ring
  · exact hB

/-- Circle `L²` normalization of the all-denominator reconstruction. -/
def normalizedAllDenominatorReconstructionL2 (N : ℕ+) : UnitCircleL2 :=
  ((Real.log (N : ℝ))⁻¹ : ℂ) • allDenominatorReconstructionL2 N

/-- Circle `L²` normalization of the natural cutoff `P = N`. -/
def normalizedNaturalCutoffReconstructionL2 (N : ℕ+) : UnitCircleL2 :=
  ((Real.log (N : ℝ))⁻¹ : ℂ) •
    naturalCutoffReconstructionL2 N (N : ℕ)

/-- Canonical pullback of the normalized natural-cutoff `L²` class to the
real probability space used in the statement. -/
def normalizedNaturalCutoffPullback (N : ℕ+) (alpha : ℝ) : ℂ :=
  unitCircleL2Pullback (normalizedNaturalCutoffReconstructionL2 N) alpha

theorem aestronglyMeasurable_normalizedNaturalCutoffPullback (N : ℕ+) :
    AEStronglyMeasurable (normalizedNaturalCutoffPullback N)
      uniform01Measure :=
  aestronglyMeasurable_unitCircleL2Pullback _

theorem unitCircleL2Pullback_normalizedAllDenominator_ae (N : ℕ+) :
    unitCircleL2Pullback (normalizedAllDenominatorReconstructionL2 N)
        =ᵐ[uniform01Measure]
      fun alpha ↦
        (normalizedAllDenominatorRealReconstruction (N : ℕ) alpha : ℂ) := by
  have hsmul := unitCircleL2Pullback_smul_ae
    ((Real.log (N : ℝ))⁻¹ : ℂ) (allDenominatorReconstructionL2 N)
  filter_upwards [hsmul, unitCircleL2Pullback_allDenominator_ae N] with
      alpha hscale hall
  rw [normalizedAllDenominatorReconstructionL2, hscale, hall]
  unfold normalizedAllDenominatorRealReconstruction
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem tendsto_norm_normalizedAllDenominator_sub_normalizedNaturalCutoff :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        ‖normalizedAllDenominatorReconstructionL2 N -
          normalizedNaturalCutoffReconstructionL2 N‖)
      atTop (nhds 0) := by
  apply tendsto_norm_allDenominator_sub_naturalCutoff_div_log.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun m hm ↦ hm⟩] with m hm
  let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
  have hN : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < m + 1 by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN
  symm
  change
    ‖normalizedAllDenominatorReconstructionL2 N -
        normalizedNaturalCutoffReconstructionL2 N‖ =
      ‖allDenominatorReconstructionL2 N -
        naturalCutoffReconstructionL2 N (N : ℕ)‖ /
          Real.log (N : ℝ)
  rw [normalizedAllDenominatorReconstructionL2,
    normalizedNaturalCutoffReconstructionL2, ← smul_sub, norm_smul]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  field_simp

theorem tendsto_eLpNorm_normalizedAllDenominator_sub_naturalCutoffPullback :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        eLpNorm
          (unitCircleL2Pullback (normalizedAllDenominatorReconstructionL2 N) -
            normalizedNaturalCutoffPullback N)
          2 uniform01Measure)
      atTop (nhds 0) := by
  have hnorm :=
    tendsto_norm_normalizedAllDenominator_sub_normalizedNaturalCutoff
  have hennreal : Tendsto
      (fun m : ℕ ↦
        ENNReal.ofReal
          (let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
           ‖normalizedAllDenominatorReconstructionL2 N -
             normalizedNaturalCutoffReconstructionL2 N‖))
      atTop (nhds 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using! h
  apply hennreal.congr'
  filter_upwards with m
  let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
  change
    ENNReal.ofReal
        ‖normalizedAllDenominatorReconstructionL2 N -
          normalizedNaturalCutoffReconstructionL2 N‖ =
      eLpNorm
        (unitCircleL2Pullback (normalizedAllDenominatorReconstructionL2 N) -
          unitCircleL2Pullback (normalizedNaturalCutoffReconstructionL2 N))
        2 uniform01Measure
  rw [ofReal_norm_eq_enorm]
  rw [← eLpNorm_unitCircleL2Pullback]
  exact eLpNorm_congr_ae
    (unitCircleL2Pullback_sub_ae
      (normalizedAllDenominatorReconstructionL2 N)
      (normalizedNaturalCutoffReconstructionL2 N))

/-- Complexification of the normalized reconstructed shot on the real
probability space. -/
def normalizedReconstructedShotComplex (N : ℕ) (alpha : ℝ) : ℂ :=
  (normalizedReconstructedShotSum N alpha : ℂ)

theorem aestronglyMeasurable_normalizedReconstructedShotComplex (N : ℕ) :
    AEStronglyMeasurable (normalizedReconstructedShotComplex N)
      uniform01Measure :=
  (measurable_normalizedReconstructedShotSum N).complex_ofReal.aestronglyMeasurable

/-- The circle pullback and the manuscript's real representative give
exactly the same reconstruction error seminorm. -/
theorem eLpNorm_normalizedAllDenominatorReal_sub_reconstructedShot_eq
    (N : ℕ+) :
    eLpNorm
        (normalizedAllDenominatorRealReconstruction (N : ℕ) -
          normalizedReconstructedShotSum (N : ℕ))
        2 uniform01Measure =
      eLpNorm
        (unitCircleL2Pullback (normalizedAllDenominatorReconstructionL2 N) -
          normalizedReconstructedShotComplex (N : ℕ))
        2 uniform01Measure := by
  apply eLpNorm_congr_norm_ae
  filter_upwards [unitCircleL2Pullback_normalizedAllDenominator_ae N] with
      alpha hall
  simp only [Pi.sub_apply, normalizedReconstructedShotComplex]
  rw [hall]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The only remaining reconstruction input may be stated at the literal
natural denominator cutoff `P=N`.  The previously proved cutoff comparison
then transfers it to the exact all-denominator reconstruction. -/
theorem
    tendsto_eLpNorm_normalizedAllDenominator_sub_reconstructedShot_of_naturalCutoff
    (hnatural : Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        eLpNorm
          (normalizedNaturalCutoffPullback N -
            normalizedReconstructedShotComplex (N : ℕ))
          2 uniform01Measure)
      atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        eLpNorm
          (unitCircleL2Pullback (normalizedAllDenominatorReconstructionL2 N) -
            normalizedReconstructedShotComplex (N : ℕ))
          2 uniform01Measure)
      atTop (nhds 0) := by
  let E : ℕ → ℝ≥0∞ := fun m ↦
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    eLpNorm
      (unitCircleL2Pullback (normalizedAllDenominatorReconstructionL2 N) -
        normalizedReconstructedShotComplex (N : ℕ))
      2 uniform01Measure
  let B : ℕ → ℝ≥0∞ := fun m ↦
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    eLpNorm
        (unitCircleL2Pullback (normalizedAllDenominatorReconstructionL2 N) -
          normalizedNaturalCutoffPullback N)
        2 uniform01Measure +
      eLpNorm
        (normalizedNaturalCutoffPullback N -
          normalizedReconstructedShotComplex (N : ℕ))
        2 uniform01Measure
  have hB : Tendsto B atTop (nhds 0) := by
    have hsum :=
      tendsto_eLpNorm_normalizedAllDenominator_sub_naturalCutoffPullback.add
        hnatural
    simpa only [B, zero_add] using! hsum
  change Tendsto E atTop (nhds 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _m : ℕ ↦ (0 : ℝ≥0∞)) (h := B)
    tendsto_const_nhds hB
  · exact Eventually.of_forall fun _m ↦ bot_le
  · filter_upwards with m
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    let F : ℝ → ℂ :=
      unitCircleL2Pullback (normalizedAllDenominatorReconstructionL2 N)
    let G : ℝ → ℂ := normalizedNaturalCutoffPullback N
    let H : ℝ → ℂ := normalizedReconstructedShotComplex (N : ℕ)
    have hF : AEStronglyMeasurable F uniform01Measure :=
      aestronglyMeasurable_unitCircleL2Pullback _
    have hG : AEStronglyMeasurable G uniform01Measure :=
      aestronglyMeasurable_normalizedNaturalCutoffPullback N
    have hH : AEStronglyMeasurable H uniform01Measure :=
      aestronglyMeasurable_normalizedReconstructedShotComplex (N : ℕ)
    have hdecomp : F - H = (F - G) + (G - H) := by
      funext alpha
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    change eLpNorm (F - H) 2 uniform01Measure ≤
      eLpNorm (F - G) 2 uniform01Measure +
        eLpNorm (G - H) 2 uniform01Measure
    rw [hdecomp]
    exact eLpNorm_add_le (hF.sub hG) (hG.sub hH)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-- Real-line form of the preceding reduction, still indexed by positive
integers so that every logarithmic normalization is literal. -/
theorem
    tendsto_eLpNorm_allDenominatorReal_sub_reconstructedShot_of_naturalCutoff
    (hnatural : Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        eLpNorm
          (normalizedNaturalCutoffPullback N -
            normalizedReconstructedShotComplex (N : ℕ))
          2 uniform01Measure)
      atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ ↦
        eLpNorm
          (normalizedAllDenominatorRealReconstruction (m + 1) -
            normalizedReconstructedShotSum (m + 1))
          2 uniform01Measure)
      atTop (nhds 0) := by
  have hcomplex :=
    tendsto_eLpNorm_normalizedAllDenominator_sub_reconstructedShot_of_naturalCutoff
      hnatural
  apply hcomplex.congr'
  filter_upwards with m
  let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
  exact (eLpNorm_normalizedAllDenominatorReal_sub_reconstructedShot_eq N).symm

/-- Final conditional reconstruction theorem: after all exact cutoff and
endpoint bridges, the sole analytic hypothesis left is the natural-cutoff
error displayed above. -/
theorem tendsto_rotation_reconstruction_of_naturalCutoff_reconstruction
    (hnatural : Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        eLpNorm
          (normalizedNaturalCutoffPullback N -
            normalizedReconstructedShotComplex (N : ℕ))
          2 uniform01Measure)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        eLpNorm
          (normalizedRotationSum N - normalizedReconstructedShotSum N)
          2 uniform01Measure)
      atTop (nhds 0) := by
  apply tendsto_rotation_reconstruction_of_allDenominator_reconstruction
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  simpa only using!
    tendsto_eLpNorm_allDenominatorReal_sub_reconstructedShot_of_naturalCutoff
      hnatural

end

end Erdos1002
