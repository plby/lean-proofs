import ErdosProblems.Erdos1002.AnnularShotConvergence
import ErdosProblems.Erdos1002.SmallCoordinateTruncation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Reinstating the singular coordinate in a fixed cutoff shot

For a fixed outer resonance cutoff, the continuous-mapping argument is first
carried out on an annulus `ε ≤ |ξ| ≤ A`.  This file performs the missing
two-parameter closure as `ε ↓ 0`.  The finite shot and its annular version can
differ only when a marked resonance enters the deleted strip, whose probability
is bounded by `2 ε + o(1)`.  Billingsley's converging-together theorem then
transfers any coherent family of annular limits to the literal fixed-cutoff
shot law.

No probabilistic or arithmetic estimate is assumed inside the proof beyond the
annular weak limits supplied as theorem arguments.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

local instance probabilityMeasureWeakTopologyFCSA :
    TopologicalSpace (ProbabilityMeasure ℝ) :=
  ProbabilityMeasure.instTopologicalSpace

/-- A concrete positive sequence decreasing to zero, used for the deleted
singular-coordinate strip. -/
def smallCoordinateCutoff (m : ℕ) : ℝ :=
  1 / ((m : ℝ) + 1)

theorem smallCoordinateCutoff_nonneg (m : ℕ) :
    0 ≤ smallCoordinateCutoff m := by
  unfold smallCoordinateCutoff
  positivity

theorem tendsto_smallCoordinateCutoff :
    Tendsto smallCoordinateCutoff atTop (nhds 0) := by
  change Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1)) atTop (nhds 0)
  have hden : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  simpa only [one_div, Function.comp_def] using!
    tendsto_inv_atTop_zero.comp hden

/-- The original fixed-cutoff shot and its annular approximation are close
in the exact nested order needed by `tendsto_map_of_convergingTogether`.
The proof uses disagreement, rather than the magnitude of an individual
shot, so it remains valid at the singular coordinate. -/
theorem finiteShot_annular_twoParameter_close (A : ℝ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ m : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {α | r ≤ ‖normalizedFiniteResonanceShotSum N A α -
            annularMarkedShotFunctional N (smallCoordinateCutoff m) A α‖} < δ := by
  intro r hr δ hδ
  have htwo : Tendsto (fun m : ℕ ↦ 2 * smallCoordinateCutoff m)
      atTop (nhds 0) := by
    simpa only [mul_zero] using!
      tendsto_const_nhds.mul tendsto_smallCoordinateCutoff
  have hm : ∀ᶠ m : ℕ in atTop, 2 * smallCoordinateCutoff m < δ :=
    htwo (Iio_mem_nhds hδ)
  filter_upwards [hm] with m hmδ
  have hdelete :=
    eventually_uniform01Measure_real_finiteShot_ne_annular_lt
      (smallCoordinateCutoff_nonneg m) hmδ A
  filter_upwards [hdelete] with N hN
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans_lt hN
  intro α hα
  change r ≤ ‖normalizedFiniteResonanceShotSum N A α -
    annularMarkedShotFunctional N (smallCoordinateCutoff m) A α‖ at hα
  by_contra heq
  change ¬ normalizedFiniteResonanceShotSum N A α ≠
    annularMarkedShotFunctional N (smallCoordinateCutoff m) A α at heq
  rw [not_ne_iff.mp heq, sub_self, norm_zero] at hα
  linarith

/-- If every fixed annulus has a weak limit and those annular limits converge
as the inner radius tends to zero, then the literal fixed-cutoff finite shot
has the same weak limit.  This is the rigorous small-coordinate closure used
in the manuscript's fixed-`A` argument. -/
theorem tendsto_finiteResonanceShotLaw_of_annular_limits
    (A : ℝ) (νAnnular : ℕ → ProbabilityMeasure ℝ)
    (ν : ProbabilityMeasure ℝ)
    (hAnnular : ∀ m : ℕ,
      Tendsto
        (fun N ↦ annularMarkedShotLaw N (smallCoordinateCutoff m) A)
        atTop
        (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyFCSA
          (νAnnular m)))
    (hAnnularLimit : Tendsto νAnnular atTop
      (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyFCSA ν)) :
    Tendsto (fun N ↦ finiteResonanceShotLaw N A) atTop
      (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyFCSA ν) := by
  let X : ℕ → ℝ → ℝ :=
    fun N ↦ normalizedFiniteResonanceShotSum N A
  let XAnnular : ℕ → ℕ → ℝ → ℝ :=
    fun m N ↦ annularMarkedShotFunctional N (smallCoordinateCutoff m) A
  have hfixed : ∀ m,
      Tendsto
        (fun N ↦ (⟨uniform01Measure.map (XAnnular m N),
          Measure.isProbabilityMeasure_map
            (measurable_annularMarkedShotFunctional
              N (smallCoordinateCutoff m) A).aemeasurable⟩ :
            ProbabilityMeasure ℝ))
        atTop
        (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyFCSA
          (νAnnular m)) := by
    intro m
    simpa only [XAnnular, annularMarkedShotLaw, uniform01] using! hAnnular m
  have hmain := tendsto_map_of_convergingTogether
    (μ := uniform01Measure) X XAnnular νAnnular ν
    (fun N ↦ (measurable_normalizedFiniteResonanceShotSum N A).aemeasurable)
    (fun m N ↦
      (measurable_annularMarkedShotFunctional
        N (smallCoordinateCutoff m) A).aemeasurable)
    hfixed hAnnularLimit (finiteShot_annular_twoParameter_close A)
  simpa only [X, finiteResonanceShotLaw, uniform01] using! hmain

end

end Erdos1002
