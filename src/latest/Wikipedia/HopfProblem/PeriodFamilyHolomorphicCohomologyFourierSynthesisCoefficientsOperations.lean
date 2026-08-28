import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsAlgebra
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsDerivativeBasic

/-!
# Joint directional differentiation of coefficient families

Finite sums preserve the original compact-uniform summable bounds. The
coefficient obtained by differentiating a joint base/torus Fourier mode
therefore satisfies the same smooth rapid-decay condition. This is a
statement about actual coefficient functions and their original base
derivatives; no infinite-series regularity is assumed or asserted here.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

namespace SmoothRapidCoefficients

variable {U : Opens ℂ} {c : Coefficients}

/-- Finite sums preserve the actual smooth rapid-coefficient condition. -/
theorem sum {ι : Type*} (s : Finset ι) (f : ι → Coefficients)
    (hf : ∀ i ∈ s, SmoothRapidCoefficients U (f i)) :
    SmoothRapidCoefficients U (∑ i ∈ s, f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa only [Finset.sum_empty] using zero U
  | @insert i s hi ih =>
    intro hf
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Differentiating in an arbitrary fixed real direction of the joint
base/torus coordinates preserves every required coefficient bound. -/
theorem jointDerivative (hc : SmoothRapidCoefficients U c)
    (v : ℂ × (Fin 4 → ℝ)) :
    SmoothRapidCoefficients U (jointDerivativeCoefficients v c) := by
  unfold jointDerivativeCoefficients
  apply (hc.baseDiff v.1).add
  exact sum Finset.univ (fun j k z => (v.2 j : ℂ) * FourierSynthesis.frequencyDiff j c k z)
    (fun j _ => (hc.frequencyDiff j).const_mul (v.2 j : ℂ))

end SmoothRapidCoefficients

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
