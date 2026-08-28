import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeCoefficient

/-!
# Actual iterated base derivatives and Fourier coefficients

Both operators apply the tail of the direction list first, and then
differentiate in its head direction. The family operator stays within
genuinely jointly smooth families. Its coefficient equals the literal
iterated Fréchet derivative of the original coefficient at every point of
the original open base. The induction uses only equality near that point;
it makes no assertion about derivatives across the boundary of the base.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

/-- Literal iterated real Fréchet derivatives in fixed base directions, tail first. -/
def iteratedDirectionalDerivativeList : List ℂ → (ℂ → ℂ) → ℂ → ℂ
  | [], g => g
  | v :: s, g => fun z => fderiv ℝ (iteratedDirectionalDerivativeList s g) z v

variable {U : Opens ℂ} {d : Type*} [Fintype d]

namespace SmoothFamily

/-- Iterate the actual base derivative on the joint family in the same tail-first order. -/
def iteratedBaseDerivativeList : List ℂ → SmoothFamily U d → SmoothFamily U d
  | [], f => f
  | v :: s, f => (iteratedBaseDerivativeList s f).baseDerivative v

/-- Coefficients commute with these literal iterated derivatives on the original open base. -/
theorem iteratedCoefficientDerivative_eqOn (f : SmoothFamily U d) (s : List ℂ)
    (k : d → ℤ) :
    Set.EqOn (iteratedDirectionalDerivativeList s (f.coefficientValue k))
      ((iteratedBaseDerivativeList s f).coefficientValue k) U := by
  induction s with
  | nil => exact fun _ _ => rfl
  | cons v s ih =>
    intro z hz
    have hnear : iteratedDirectionalDerivativeList s (f.coefficientValue k) =ᶠ[𝓝 z]
        (iteratedBaseDerivativeList s f).coefficientValue k :=
      Filter.mem_of_superset (U.isOpen.mem_nhds hz) (fun _ hy => ih hy)
    change fderiv ℝ (iteratedDirectionalDerivativeList s (f.coefficientValue k)) z v =
      ((iteratedBaseDerivativeList s f).baseDerivative v).coefficientValue k z
    rw [hnear.fderiv_eq]
    exact (iteratedBaseDerivativeList s f).coefficientValue_fderiv_apply k z hz v

/-- Pointwise form in the original ambient base coordinate, only inside the base open. -/
theorem iteratedCoefficientDerivative_eq (f : SmoothFamily U d) (s : List ℂ)
    (k : d → ℤ) (z : ℂ) (hz : z ∈ U) :
    iteratedDirectionalDerivativeList s (f.coefficientValue k) z =
      (iteratedBaseDerivativeList s f).coefficientValue k z :=
  f.iteratedCoefficientDerivative_eqOn s k hz

/-- The actual iterated coefficient derivative is the Haar coefficient of the genuine family. -/
theorem iteratedCoefficientDerivative_apply (f : SmoothFamily U d) (s : List ℂ)
    (k : d → ℤ) (b : U) :
    iteratedDirectionalDerivativeList s (f.coefficientValue k) (b : ℂ) =
      mFourierCoeff (fun t => iteratedBaseDerivativeList s f (b, t)) k := by
  rw [f.iteratedCoefficientDerivative_eq s k (b : ℂ) b.property, coefficientValue_apply]

end SmoothFamily

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
