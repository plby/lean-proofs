import ErdosProblems.Erdos1002.GaussDenominatorMaximal
import ErdosProblems.Erdos1002.MarkedCountMoments
import ErdosProblems.Erdos1002.VanishingEventMomentDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Removing the global denominator bad event from marked moments

This module specializes Cauchy--Schwarz deletion to the literal marked
resonance count.  A uniform factorial moment of order `2r` supplies the
ordinary `2r` moment bound, while the maximal denominator weak law makes the
single global bad event negligible.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1002

noncomputable section

/-- Along every depth scale tending to infinity, the `r`-th power of a
marked resonance count has vanishing integral on the global denominator bad
event.  The denominator cutoff `Ps` is kept independent of `Ns`, so this can
also be reused for truncated count vectors. -/
theorem tendsto_markedResonanceCount_pow_on_denominatorBadEvent
    (Ns Ps Ls : ℕ → ℕ) (r Cdepth : ℕ) {Delta : ℝ}
    {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B)
    (hCdepth : 0 < Cdepth) (hDelta : 0 < Delta)
    (hLs : Tendsto Ls atTop atTop)
    {Cmoment : ℝ}
    (hfactorial : ∀ n,
      ∫ α,
        ((markedResonanceCount (Ns n) (Ps n) B α).descFactorial
          (2 * r) : ℝ) ∂uniform01Measure ≤ Cmoment) :
    Tendsto
      (fun n ↦ ∫ α in
          gaussDenominatorLinearBadEvent Cdepth (Ls n) Delta,
        (markedResonanceCount (Ns n) (Ps n) B α : ℝ) ^ r
          ∂uniform01Measure)
      atTop (𝓝 0) := by
  let X : ℕ → ℝ → ℕ := fun n ↦
    markedResonanceCount (Ns n) (Ps n) B
  let E : ℕ → Set ℝ := fun n ↦
    gaussDenominatorLinearBadEvent Cdepth (Ls n) Delta
  let D : ℝ :=
    (2 : ℝ) ^ (2 * r) * Cmoment +
      ((2 * (2 * r) : ℕ) : ℝ) ^ (2 * r)
  have hordinary : ∀ n,
      ∫ α, (X n α : ℝ) ^ (2 * r) ∂uniform01Measure ≤ D := by
    intro n
    dsimp only [X, D]
    exact integral_markedResonanceCount_pow_le_of_factorial
      (Ns n) (Ps n) (2 * r) hB (hfactorial n)
  have hEzero : Tendsto
      (fun n ↦ uniform01Measure.real (E n)) atTop (𝓝 0) := by
    exact
      (tendsto_gaussDenominatorLinearBadEvent_uniform01MeasureReal_zero
        hCdepth hDelta).comp hLs
  apply tendsto_setIntegral_natCast_pow_on_vanishing_events
    uniform01Measure X E r
  · intro n
    exact measurable_markedResonanceCount (Ns n) (Ps n) hB
  · intro n
    exact integrable_markedResonanceCount_pow
      (Ns n) (Ps n) (2 * r) hB
  · intro n
    exact measurableSet_gaussDenominatorLinearBadEvent
      Cdepth (Ls n) Delta
  · exact hEzero
  · exact hordinary

end

end Erdos1002
