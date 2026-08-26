import ErdosProblems.Erdos1002.ConvergingTogether
import ErdosProblems.Erdos1002.RotationShotBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Final assembly of the proof

This file records the precise logical interface between the three deep
inputs of the manuscript: reconstruction in `L²`, deletion of minor shots in
probability, and fixed-cutoff convergence.  The union bound and both orders
of limits are proved explicitly.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

local instance probabilityMeasureWeakTopologyFA :
    TopologicalSpace (ProbabilityMeasure ℝ) :=
  ProbabilityMeasure.instTopologicalSpace

/-- The reconstruction error and the minor-shot error combine to give the
two-parameter approximation required by the converging-together theorem. -/
theorem rotation_finite_close_of_reconstruction_and_minor
    (hL2 : Tendsto
      (fun N ↦ eLpNorm
        (normalizedRotationSum N - normalizedReconstructedShotSum N)
        2 uniform01Measure) atTop (nhds 0))
    (hminor : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {α | r ≤ ‖normalizedMinorResonanceShotSum N (A : ℝ) α‖} < δ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {α | r ≤ ‖normalizedRotationSum N α -
            normalizedFiniteResonanceShotSum N (A : ℝ) α‖} < δ := by
  have hrecTM : TendstoInMeasure uniform01Measure
      (normalizedRotationSum - normalizedReconstructedShotSum) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal)) (by norm_num)
    · intro N
      exact ((measurable_normalizedRotationSum N).sub
        (measurable_normalizedReconstructedShotSum N)).aestronglyMeasurable
    · exact aestronglyMeasurable_zero
    · simpa only [Pi.sub_apply, sub_zero] using! hL2
  rw [tendstoInMeasure_iff_measureReal_norm] at hrecTM
  intro r hr δ hδ
  have hreclim := hrecTM (r / 2) (by positivity)
  have hrecN : ∀ᶠ N : ℕ in atTop,
      uniform01Measure.real
        {α | r / 2 ≤ ‖normalizedRotationSum N α -
          normalizedReconstructedShotSum N α‖} < δ / 2 := by
    rw [Metric.tendsto_nhds] at hreclim
    have he := hreclim (δ / 2) (by positivity)
    simpa [Real.dist_eq, abs_of_nonneg measureReal_nonneg] using! he
  have hminorA := hminor (r / 2) (by positivity) (δ / 2) (by positivity)
  filter_upwards [hminorA] with A hminorN
  filter_upwards [hminorN, hrecN] with N hmin hrec
  let U : Set ℝ := {α | r ≤ ‖normalizedRotationSum N α -
    normalizedFiniteResonanceShotSum N (A : ℝ) α‖}
  let R : Set ℝ := {α | r / 2 ≤ ‖normalizedRotationSum N α -
    normalizedReconstructedShotSum N α‖}
  let M : Set ℝ := {α | r / 2 ≤
    ‖normalizedMinorResonanceShotSum N (A : ℝ) α‖}
  have hsubset : U ⊆ R ∪ M := by
    intro α hα
    by_cases hR : r / 2 ≤ ‖normalizedRotationSum N α -
        normalizedReconstructedShotSum N α‖
    · exact Or.inl hR
    · apply Or.inr
      by_contra hM
      have hRlt : ‖normalizedRotationSum N α -
          normalizedReconstructedShotSum N α‖ < r / 2 := lt_of_not_ge hR
      have hMlt : ‖normalizedMinorResonanceShotSum N (A : ℝ) α‖ < r / 2 :=
        lt_of_not_ge hM
      have hdecomp : normalizedRotationSum N α -
          normalizedFiniteResonanceShotSum N (A : ℝ) α =
          (normalizedRotationSum N α - normalizedReconstructedShotSum N α) +
            normalizedMinorResonanceShotSum N (A : ℝ) α := by
        rw [normalizedReconstructedShotSum_eq_finite_add_minor]
        ring
      have htri : ‖normalizedRotationSum N α -
          normalizedFiniteResonanceShotSum N (A : ℝ) α‖ ≤
          ‖normalizedRotationSum N α - normalizedReconstructedShotSum N α‖ +
            ‖normalizedMinorResonanceShotSum N (A : ℝ) α‖ := by
        rw [hdecomp]
        exact norm_add_le _ _
      dsimp [U] at hα
      simp only [Real.norm_eq_abs] at hRlt hMlt htri
      linarith
  simp only [Real.norm_eq_abs] at hrec hmin
  calc
    uniform01Measure.real U ≤ uniform01Measure.real (R ∪ M) :=
      measureReal_mono hsubset
    _ ≤ uniform01Measure.real R + uniform01Measure.real M :=
      measureReal_union_le R M
    _ < δ := by
      dsimp [R, M]
      linarith

/-- Once the three substantive estimates have been established, the exact
Erdős 1002 conclusion follows.  This theorem is the kernel-checked version of
the manuscript's final converging-together paragraph. -/
theorem erdos1002Conclusion_of_shot_inputs
    (νA : ℕ → ProbabilityMeasure ℝ)
    (hfixed : ∀ A : ℕ,
      Tendsto (fun N ↦ finiteResonanceShotLaw N (A : ℝ)) atTop
        (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyFA (νA A)))
    (hPoissonLimit : Tendsto νA atTop
      (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyFA
        cauchyLimitProbability))
    (hL2 : Tendsto
      (fun N ↦ eLpNorm
        (normalizedRotationSum N - normalizedReconstructedShotSum N)
        2 uniform01Measure) atTop (nhds 0))
    (hminor : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {α | r ≤ ‖normalizedMinorResonanceShotSum N (A : ℝ) α‖} < δ) :
    Erdos1002Conclusion := by
  have hclose := rotation_finite_close_of_reconstruction_and_minor hL2 hminor
  have hweak := tendsto_map_of_convergingTogether
    (μ := uniform01Measure)
    (fun N ↦ normalizedRotationSum N)
    (fun A N ↦ normalizedFiniteResonanceShotSum N (A : ℝ))
    νA cauchyLimitProbability
    (fun N ↦ (measurable_normalizedRotationSum N).aemeasurable)
    (fun A N ↦ (measurable_normalizedFiniteResonanceShotSum N (A : ℝ)).aemeasurable)
    (by simpa [finiteResonanceShotLaw, uniform01] using! hfixed)
    hPoissonLimit hclose
  apply erdos1002Conclusion_of_rotationLaw_tendsto
  simpa [rotationLaw, uniform01] using! hweak

end

end Erdos1002
