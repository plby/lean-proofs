import ErdosProblems.Erdos1002.FactorialMomentBounds
import ErdosProblems.Erdos1002.MarkedCountTightness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform ordinary moments of marked resonance counts

This specializes the general falling-factorial comparison to the literal
marked resonance counts.  It supplies the all-orders moment bounds used for
uniform integrability, boundary strips, close tuples, and good-event
complements.
-/

open MeasureTheory Set

namespace Erdos1002

noncomputable section

/-- Every fixed falling-factorial moment of a finite marked count is
integrable. -/
theorem integrable_markedResonanceCount_descFactorial
    (N P s : ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B) :
    Integrable
      (fun α ↦ ((markedResonanceCount N P B α).descFactorial s : ℝ))
      uniform01Measure := by
  have hmeas : Measurable
      (fun α ↦ ((markedResonanceCount N P B α).descFactorial s : ℝ)) :=
    (measurable_of_countable
      (fun n : ℕ ↦ (n.descFactorial s : ℝ))).comp
        (measurable_markedResonanceCount N P hB)
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (P.descFactorial s : ℝ)
  exact ae_of_all _ fun α ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
    exact_mod_cast Nat.descFactorial_le s
      (markedResonanceCount_le N P B α)

/-- Every ordinary power of the actual finite marked count is integrable.
This is the explicit integrability input needed when a uniform higher
moment is used to delete a set of vanishing probability. -/
theorem integrable_markedResonanceCount_pow
    (N P s : ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B) :
    Integrable
      (fun α ↦ (markedResonanceCount N P B α : ℝ) ^ s)
      uniform01Measure := by
  have hmeas : Measurable
      (fun α ↦ (markedResonanceCount N P B α : ℝ) ^ s) :=
    ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_markedResonanceCount N P hB)).pow_const s
  apply Integrable.of_bound hmeas.aestronglyMeasurable ((P : ℝ) ^ s)
  exact ae_of_all _ fun α ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast markedResonanceCount_le N P B α) s

/-- Quantitative ordinary-moment bound from the same-order factorial
moment of the actual count. -/
theorem integral_markedResonanceCount_pow_le_of_factorial
    (N P s : ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B)
    {C : ℝ}
    (hfac : ∫ α,
      ((markedResonanceCount N P B α).descFactorial s : ℝ)
        ∂uniform01Measure ≤ C) :
    ∫ α, (markedResonanceCount N P B α : ℝ) ^ s
        ∂uniform01Measure ≤
      (2 : ℝ) ^ s * C + ((2 * s : ℕ) : ℝ) ^ s := by
  exact integral_natCast_pow_le_of_descFactorial_integral_le
    uniform01Measure (markedResonanceCount N P B)
    (measurable_markedResonanceCount N P hB) s
    (integrable_markedResonanceCount_descFactorial N P s hB) hfac

/-- Sequence form: a uniform factorial-moment bound gives a uniform
ordinary-moment bound with an explicit constant. -/
theorem uniform_integral_markedResonanceCount_pow
    (Ns Ps : ℕ → ℕ) (s : ℕ) {B : Set (ℝ × ℝ × ℝ)}
    (hB : MeasurableSet B) {C : ℝ}
    (hfac : ∀ n,
      ∫ α,
        ((markedResonanceCount (Ns n) (Ps n) B α).descFactorial s : ℝ)
          ∂uniform01Measure ≤ C) :
    ∀ n,
      ∫ α, (markedResonanceCount (Ns n) (Ps n) B α : ℝ) ^ s
          ∂uniform01Measure ≤
        (2 : ℝ) ^ s * C + ((2 * s : ℕ) : ℝ) ^ s := by
  intro n
  exact integral_markedResonanceCount_pow_le_of_factorial
    (Ns n) (Ps n) s hB (hfac n)

end

end Erdos1002
