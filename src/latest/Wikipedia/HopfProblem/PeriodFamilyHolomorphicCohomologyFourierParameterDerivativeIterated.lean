import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeIteratedBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDecay

/-!
# Compact-uniform decay of actual iterated coefficient derivatives

For a fixed list of real base directions, the iterated coefficient
derivative is the coefficient of an actual jointly smooth derivative
family. Applying the already proved compact-uniform estimates to that
family gives rapid decay and summable polynomial majorants for the literal
iterated derivatives, simultaneously for every parameter and Fourier mode.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

namespace SmoothFamily

/-- Every fixed iterated coefficient derivative is continuous on the original native base. -/
theorem iteratedCoefficientDerivative_continuous (f : SmoothFamily U d) (s : List ℂ)
    (k : d → ℤ) :
    Continuous (fun b : U =>
      iteratedDirectionalDerivativeList s (f.coefficientValue k) (b : ℂ)) := by
  have h : Continuous (fun b : U =>
      mFourierCoeff (fun t => iteratedBaseDerivativeList s f (b, t)) k) :=
    (iteratedBaseDerivativeList s f).coefficient_continuous k
  simpa only [iteratedCoefficientDerivative_apply] using h

/-- Actual iterated coefficient derivatives decay rapidly, uniformly on compact parameter sets. -/
theorem iteratedCoefficientDerivative_rapidDecay_compact (f : SmoothFamily U d)
    (s : List ℂ) (K : Set U) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ k : d → ℤ,
      ‖iteratedDirectionalDerivativeList s (f.coefficientValue k) (b : ℂ)‖ ≤
        C / fourierEllipticWeight k ^ n := by
  obtain ⟨C, hC, hbound⟩ := (iteratedBaseDerivativeList s f).rapidDecay_compact K hK n
  refine ⟨C, hC, fun b hb k => ?_⟩
  rw [f.iteratedCoefficientDerivative_apply s k b]
  exact hbound b hb k

/-- Polynomially weighted actual iterated derivatives have a compact-uniform summable majorant. -/
theorem iteratedCoefficientDerivative_polynomial_majorant_compact (f : SmoothFamily U d)
    (s : List ℂ) (K : Set U) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      Summable (fun k : d → ℤ => C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹) ∧
      ∀ b ∈ K, ∀ k : d → ℤ,
        (1 + ‖(fun i => (k i : ℝ))‖) ^ r *
            ‖iteratedDirectionalDerivativeList s (f.coefficientValue k) (b : ℂ)‖ ≤
          C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹ := by
  obtain ⟨C, hC, hsum, hbound⟩ :=
    (iteratedBaseDerivativeList s f).polynomial_majorant_compact K hK r
  refine ⟨C, hC, hsum, fun b hb k => ?_⟩
  rw [f.iteratedCoefficientDerivative_apply s k b]
  exact hbound b hb k

end SmoothFamily

/-- Raw joint smoothness supplies compact-uniform rapid decay for each actual direction list. -/
theorem iteratedCoefficientDerivative_rapidDecay_compact_of_contDiffOn_lift
    {f : U × UnitAddTorus d → ℂ}
    (hf : ContDiffOn ℝ ∞ (ambientLift f) (Smooth.baseProductDomain U (d → ℝ)))
    (s : List ℂ) (K : Set U) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ k : d → ℤ,
      ‖iteratedDirectionalDerivativeList s
          (fun z : ℂ => mFourierCoeff (fun t => ambientValue f (z, t)) k) (b : ℂ)‖ ≤
        C / fourierEllipticWeight k ^ n :=
  SmoothFamily.iteratedCoefficientDerivative_rapidDecay_compact ⟨f, hf⟩ s K hK n

/-- Raw joint smoothness also supplies summable majorants for the actual weighted derivatives. -/
theorem iteratedCoefficientDerivative_polynomial_majorant_compact_of_contDiffOn_lift
    {f : U × UnitAddTorus d → ℂ}
    (hf : ContDiffOn ℝ ∞ (ambientLift f) (Smooth.baseProductDomain U (d → ℝ)))
    (s : List ℂ) (K : Set U) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      Summable (fun k : d → ℤ => C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹) ∧
      ∀ b ∈ K, ∀ k : d → ℤ,
        (1 + ‖(fun i => (k i : ℝ))‖) ^ r *
            ‖iteratedDirectionalDerivativeList s
              (fun z : ℂ => mFourierCoeff (fun t => ambientValue f (z, t)) k) (b : ℂ)‖ ≤
          C * (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹ :=
  SmoothFamily.iteratedCoefficientDerivative_polynomial_majorant_compact ⟨f, hf⟩ s K hK r

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
