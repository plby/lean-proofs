import ErdosProblems.Erdos1002.MarkedResonances
import ErdosProblems.Erdos1002.MultivariatePoissonFactorial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite vectors of marked resonance counts

This file connects the literal marked counts to the multivariate method of
factorial moments.  In particular, integrability is proved automatically
from the finite denominator cutoff; it is not left as an implicit uniform
integrability assertion.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

variable {ι : Type*} [Fintype ι]

/-- Vector of counts in a finite labeled family of mark sets. -/
def markedResonanceCountVector (N P : ℕ)
    (B : ι → Set (ℝ × ℝ × ℝ)) (α : ℝ) : ι → ℕ :=
  fun i ↦ markedResonanceCount N P (B i) α

omit [Fintype ι] in
theorem measurable_markedResonanceCountVector (N P : ℕ)
    {B : ι → Set (ℝ × ℝ × ℝ)} (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (markedResonanceCountVector N P B) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_markedResonanceCount N P (hB i)

/-- Law of the finite vector of marked counts under uniform Lebesgue
measure on `(0,1)`. -/
def markedResonanceCountVectorLaw (N P : ℕ)
    (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) : ProbabilityMeasure (ι → ℕ) :=
  uniform01.map (measurable_markedResonanceCountVector N P hB).aemeasurable

omit [Fintype ι] in
theorem markedResonanceCountVector_le (N P : ℕ)
    (B : ι → Set (ℝ × ℝ × ℝ)) (α : ℝ) (i : ι) :
    markedResonanceCountVector N P B α i ≤ P :=
  markedResonanceCount_le N P (B i) α

private theorem mixedDescFactorial_comp_bound (N P : ℕ)
    (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ) (α : ℝ) :
    ‖mixedDescFactorial k (markedResonanceCountVector N P B α)‖ ≤
      ∏ i, (P.descFactorial (k i) : ℝ) := by
  have hnonneg : 0 ≤
      mixedDescFactorial k (markedResonanceCountVector N P B α) := by
    unfold mixedDescFactorial
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  unfold mixedDescFactorial
  gcongr with i
  exact markedResonanceCountVector_le N P B α i

/-- Every mixed factorial monomial is integrable for a finite marked count.
The bound may depend on the fixed order and cutoff, which is all the method
of moments requires. -/
theorem integrable_mixedDescFactorial_markedResonanceCountVectorLaw
    (N P : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ) :
    Integrable (mixedDescFactorial k)
      (markedResonanceCountVectorLaw N P B hB : Measure (ι → ℕ)) := by
  let X : ℝ → (ι → ℕ) := markedResonanceCountVector N P B
  have hX : Measurable X := measurable_markedResonanceCountVector N P hB
  have hg : Measurable (mixedDescFactorial k : (ι → ℕ) → ℝ) :=
    measurable_of_countable _
  have hcomp : Integrable (mixedDescFactorial k ∘ X) uniform01Measure := by
    apply MeasureTheory.Integrable.of_bound
      (hg.comp hX).aestronglyMeasurable
      (∏ i, (P.descFactorial (k i) : ℝ))
    filter_upwards with α
    exact mixedDescFactorial_comp_bound N P B k α
  change Integrable (mixedDescFactorial k)
    (Measure.map X uniform01Measure)
  exact (integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).mpr hcomp

/-- The mixed factorial moment of the count-vector law is exactly the
Lebesgue integral of the corresponding product of falling factorials. -/
theorem mixedFactorialMoment_markedResonanceCountVectorLaw
    (N P : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ) :
    mixedFactorialMoment (markedResonanceCountVectorLaw N P B hB) k =
      ∫ α, mixedDescFactorial k
        (markedResonanceCountVector N P B α) ∂uniform01Measure := by
  unfold mixedFactorialMoment markedResonanceCountVectorLaw uniform01
  change ∫ x, mixedDescFactorial k x
      ∂Measure.map (markedResonanceCountVector N P B) uniform01Measure = _
  exact integral_map
    (measurable_markedResonanceCountVector N P hB).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- Kernel-checked finite-dimensional Poisson conclusion from the mixed
factorial limits of the actual marked resonance counts. -/
theorem tendsto_markedResonanceCountVectorLaw_of_mixedFactorialMoments
    (Ns Ps : ℕ → ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (r : ι → NNReal)
    (hFac : ∀ k : ι → ℕ,
      Tendsto
        (fun n ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ps n) B hB) k)
        atTop (nhds (∏ i, (r i : ℝ) ^ (k i)))) :
    Tendsto
      (fun n ↦ markedResonanceCountVectorLaw (Ns n) (Ps n) B hB)
      atTop (nhds (independentPoissonProbabilityMeasure r)) := by
  apply tendsto_independentPoisson_of_mixedFactorialMoments
  · intro n k
    exact integrable_mixedDescFactorial_markedResonanceCountVectorLaw
      (Ns n) (Ps n) B hB k
  · exact hFac

end

end Erdos1002
