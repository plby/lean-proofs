import ErdosProblems.Erdos1002.CountControlledApproximation
import ErdosProblems.Erdos1002.MarkedResonances

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Tightness of finite marked resonance counts

The mesh-to-zero shot argument needs tightness only of the number of marked
points in a fixed compact annulus.  This file verifies integrability for the
literal finite resonance count and derives tightness directly from
convergence of its first factorial moment.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1002

noncomputable section

/-- A finite marked count, cast to `ℝ`, is integrable. -/
theorem integrable_markedResonanceCount_cast
    (N P : ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B) :
    Integrable
      (fun α ↦ (markedResonanceCount N P B α : ℝ))
      uniform01Measure := by
  have hmeas : Measurable
      (fun α ↦ (markedResonanceCount N P B α : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_markedResonanceCount N P hB)
  apply Integrable.of_bound hmeas.aestronglyMeasurable (P : ℝ)
  exact ae_of_all _ fun α ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
    exact_mod_cast markedResonanceCount_le N P B α

/-- If the first moments of actual marked counts converge, those counts are
uniformly tight along the tail of the sequence. -/
theorem markedResonanceCount_tight_of_tendsto_firstMoment
    (Ns Ps : ℕ → ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hmean : Tendsto
      (fun n ↦ ∫ α,
        (markedResonanceCount (Ns n) (Ps n) B α : ℝ)
          ∂uniform01Measure)
      atTop (nhds lam)) :
    ∀ δ > 0, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      uniform01Measure.real
        {α | K < markedResonanceCount (Ns n) (Ps n) B α} < δ := by
  apply count_tight_of_tendsto_firstMoment uniform01Measure
    (fun n α ↦ markedResonanceCount (Ns n) (Ps n) B α)
    (fun n ↦ integrable_markedResonanceCount_cast (Ns n) (Ps n) hB)
    lam hlam hmean

end

end Erdos1002
