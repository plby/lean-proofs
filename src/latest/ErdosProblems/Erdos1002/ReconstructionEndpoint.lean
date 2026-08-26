import ErdosProblems.Erdos1002.ReconstructionCoefficients
import ErdosProblems.Erdos1002.ShotLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The half-weight endpoint in the exact reconstruction

The all-denominator Fourier--Ramanujan reconstruction differs from the
literal rotation sum by the single endpoint term

`(1 / 2) * sawtooth (N * alpha)`.

This file records the corresponding real-line identity and proves directly,
under the exact probability measure used in the statement, that this term is
`o(1)` in `L²` after division by `log N`.  Thus the endpoint convention is
not hidden in a later asymptotic estimate.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos1002

noncomputable section

/-- Real-line representative of the exact all-denominator reconstruction. -/
def allDenominatorRealReconstruction (N : ℕ) (α : ℝ) : ℝ :=
  rotationSum N α - (1 / 2 : ℝ) * sawtooth ((N : ℝ) * α)

/-- The preceding representative with the manuscript normalization. -/
def normalizedAllDenominatorRealReconstruction (N : ℕ) (α : ℝ) : ℝ :=
  allDenominatorRealReconstruction N α / Real.log (N : ℝ)

theorem measurable_allDenominatorRealReconstruction (N : ℕ) :
    Measurable (allDenominatorRealReconstruction N) := by
  unfold allDenominatorRealReconstruction
  exact (measurable_rotationSum N).sub
    (measurable_const.mul
      (sawtooth_measurable.comp (measurable_const.mul measurable_id)))

theorem measurable_normalizedAllDenominatorRealReconstruction (N : ℕ) :
    Measurable (normalizedAllDenominatorRealReconstruction N) := by
  exact (measurable_allDenominatorRealReconstruction N).div_const _

/-- Exact pointwise endpoint identity, with no exceptional set. -/
theorem normalizedRotationSum_sub_normalizedAllDenominatorRealReconstruction
    (N : ℕ) (α : ℝ) :
    normalizedRotationSum N α -
        normalizedAllDenominatorRealReconstruction N α =
      ((1 / 2 : ℝ) * sawtooth ((N : ℝ) * α)) /
        Real.log (N : ℝ) := by
  unfold normalizedRotationSum normalizedAllDenominatorRealReconstruction
    allDenominatorRealReconstruction
  ring

/-- Uniform pointwise bound for the normalized endpoint term. -/
theorem abs_normalizedRotationSum_sub_normalizedAllDenominator_le
    {N : ℕ} (hN : 2 ≤ N) (α : ℝ) :
    |normalizedRotationSum N α -
        normalizedAllDenominatorRealReconstruction N α| ≤
      1 / (4 * Real.log (N : ℝ)) := by
  rw [normalizedRotationSum_sub_normalizedAllDenominatorRealReconstruction,
    abs_div]
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  rw [abs_of_pos hlog]
  have hnum : |(1 / 2 : ℝ) * sawtooth ((N : ℝ) * α)| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith [abs_sawtooth_le_half ((N : ℝ) * α)]
  calc
    |(1 / 2 : ℝ) * sawtooth ((N : ℝ) * α)| /
          Real.log (N : ℝ) ≤
        (1 / 4 : ℝ) / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hnum hlog.le
    _ = 1 / (4 * Real.log (N : ℝ)) := by ring

/-- The exact `L²` endpoint error is bounded by the displayed deterministic
majorant.  The measure is precisely Lebesgue measure restricted to `(0,1)`. -/
theorem eLpNorm_normalizedRotationSum_sub_normalizedAllDenominator_le
    {N : ℕ} (hN : 2 ≤ N) :
    eLpNorm
        (normalizedRotationSum N -
          normalizedAllDenominatorRealReconstruction N)
        2 uniform01Measure ≤
      ENNReal.ofReal (1 / (4 * Real.log (N : ℝ))) := by
  have hpoint : ∀ᵐ α ∂uniform01Measure,
      ‖(normalizedRotationSum N -
          normalizedAllDenominatorRealReconstruction N) α‖ ≤
        1 / (4 * Real.log (N : ℝ)) := by
    filter_upwards with α
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using!
      abs_normalizedRotationSum_sub_normalizedAllDenominator_le hN α
  have hbound := eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hpoint
  simpa using! hbound

private theorem tendsto_endpoint_real_majorant :
    Tendsto (fun N : ℕ ↦ 1 / (4 * Real.log (N : ℝ)))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun N : ℕ ↦ 4 * Real.log (N : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).2 hlog
  simpa only [one_div] using!
    (tendsto_inv_atTop_zero.comp hden :
      Tendsto (fun N : ℕ ↦ (4 * Real.log (N : ℝ))⁻¹) atTop (nhds 0))

private theorem tendsto_endpoint_ennreal_majorant :
    Tendsto
      (fun N : ℕ ↦ ENNReal.ofReal (1 / (4 * Real.log (N : ℝ))))
      atTop (nhds 0) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    tendsto_endpoint_real_majorant
  simpa using! h

/-- After the manuscript normalization, the half-weight endpoint vanishes
in `L²`. -/
theorem tendsto_eLpNorm_normalizedRotationSum_sub_normalizedAllDenominator :
    Tendsto
      (fun N : ℕ ↦
        eLpNorm
          (normalizedRotationSum N -
            normalizedAllDenominatorRealReconstruction N)
          2 uniform01Measure)
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℕ ↦ (0 : ENNReal))
    (h := fun N : ℕ ↦ ENNReal.ofReal (1 / (4 * Real.log (N : ℝ))))
    tendsto_const_nhds tendsto_endpoint_ennreal_majorant
  · exact Eventually.of_forall fun _ ↦ bot_le
  · filter_upwards [eventually_atTop.2 ⟨2, fun N hN ↦ hN⟩] with N hN
    exact eLpNorm_normalizedRotationSum_sub_normalizedAllDenominator_le hN

/-- Reduction of the manuscript's reconstruction input to the periodized
reconstruction.  Once the nearest-cell shot sum has been shown to approach
the exact all-denominator representative in `L²`, the original rotation sum
does so as well; the only additional term is the endpoint just estimated. -/
theorem tendsto_rotation_reconstruction_of_allDenominator_reconstruction
    (hperiodized : Tendsto
      (fun N : ℕ ↦
        eLpNorm
          (normalizedAllDenominatorRealReconstruction N -
            normalizedReconstructedShotSum N)
          2 uniform01Measure)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        eLpNorm
          (normalizedRotationSum N - normalizedReconstructedShotSum N)
          2 uniform01Measure)
      atTop (nhds 0) := by
  let endpointNorm : ℕ → ENNReal := fun N ↦
    eLpNorm
      (normalizedRotationSum N -
        normalizedAllDenominatorRealReconstruction N)
      2 uniform01Measure
  let periodizedNorm : ℕ → ENNReal := fun N ↦
    eLpNorm
      (normalizedAllDenominatorRealReconstruction N -
        normalizedReconstructedShotSum N)
      2 uniform01Measure
  have hendpoint : Tendsto endpointNorm atTop (nhds 0) := by
    simpa only [endpointNorm] using!
      tendsto_eLpNorm_normalizedRotationSum_sub_normalizedAllDenominator
  have hperiod : Tendsto periodizedNorm atTop (nhds 0) := by
    simpa only [periodizedNorm] using! hperiodized
  have hsum : Tendsto (fun N ↦ endpointNorm N + periodizedNorm N)
      atTop (nhds 0) := by
    simpa using! hendpoint.add hperiod
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℕ ↦ (0 : ENNReal))
    (h := fun N : ℕ ↦ endpointNorm N + periodizedNorm N)
    tendsto_const_nhds hsum
  · exact Eventually.of_forall fun _ ↦ bot_le
  · exact Eventually.of_forall fun N ↦ by
      let f : ℝ → ℝ :=
        normalizedRotationSum N -
          normalizedAllDenominatorRealReconstruction N
      let g : ℝ → ℝ :=
        normalizedAllDenominatorRealReconstruction N -
          normalizedReconstructedShotSum N
      have hf : AEStronglyMeasurable f uniform01Measure :=
        ((measurable_normalizedRotationSum N).sub
          (measurable_normalizedAllDenominatorRealReconstruction N)).aestronglyMeasurable
      have hg : AEStronglyMeasurable g uniform01Measure :=
        ((measurable_normalizedAllDenominatorRealReconstruction N).sub
          (measurable_normalizedReconstructedShotSum N)).aestronglyMeasurable
      have hadd := eLpNorm_add_le hf hg (by norm_num : (1 : ENNReal) ≤ 2)
      have hfun :
          normalizedRotationSum N - normalizedReconstructedShotSum N =
            f + g := by
        funext α
        dsimp [f, g]
        ring
      rw [hfun]
      simpa only [endpointNorm, periodizedNorm, f, g] using! hadd

end

end Erdos1002
