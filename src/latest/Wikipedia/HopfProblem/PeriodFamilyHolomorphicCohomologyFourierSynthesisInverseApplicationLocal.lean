import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseApplicationIdentity
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseApplicationParameter

/-!
# One genuine inverse neighborhood and its actual smooth Fourier operators

A single proved smaller base open has the original inverse equations,
complex holomorphicity, and real-derivative multiplier bounds. That same
open works for every rapid coefficient input and every genuinely smooth
original family. The output families are the literal inverse-mode Fourier
sums constructed using the proved coefficient product and synthesis.

No primitive equation, relative cohomology comparison, or base-change
conclusion is assumed or asserted here.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

open FourierSynthesis PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The same original inverse neighborhood supports its exact inverse equations,
holomorphicity, and actual smooth inverse-mode sums for every input family. -/
theorem exists_open_inverse_operators (b₀ : U) :
    ∃ V : Opens ℂ, ∃ hVU : V ≤ U, (b₀ : ℂ) ∈ V ∧
      SmoothPolynomiallyBoundedCoefficients V
        (RelativeFourier.ambientInverse P (P.point b₀)) ∧
      (∀ k : Fin 4 → ℤ,
        DifferentiableOn ℂ (RelativeFourier.ambientInverse P (P.point b₀) k) V) ∧
      (∀ (b : V) (k : Fin 4 → ℤ), k ≠ 0 →
        RelativeFourier.centreCoefficient (P.point b₀) (P.point (Set.inclusion hVU b))
            (integerFrequency k) *
          RelativeFourier.ambientInverse P (P.point b₀) k (b : ℂ) = 1) ∧
      (∀ b : V, RelativeFourier.ambientInverse P (P.point b₀) 0 (b : ℂ) = 0) ∧
      (∀ (c : Coefficients), SmoothRapidCoefficients U c →
        ∃ g : FourierParameter.SmoothFamily V (Fin 4),
          ∀ (b : V) (t : UnitAddTorus (Fin 4)), g (b, t) =
            ∑' k, (RelativeFourier.ambientInverse P (P.point b₀) k (b : ℂ) * c k (b : ℂ)) *
              mFourier k t) ∧
      ∀ f : FourierParameter.SmoothFamily U (Fin 4),
        ∃ g : FourierParameter.SmoothFamily V (Fin 4),
          ∀ (b : V) (t : UnitAddTorus (Fin 4)), g (b, t) =
            ∑' k, (RelativeFourier.denominatorInverse (P.point b₀)
              (P.point (Set.inclusion hVU b)) (integerFrequency k) *
                mFourierCoeff (fun q => f (Set.inclusion hVU b, q)) k) * mFourier k t := by
  obtain ⟨V, hVU, hb, hm, hhol, heq, hzero⟩ := exists_open_inverse_identity_data P b₀
  refine ⟨V, hVU, hb, hm, hhol, heq, hzero, ?_, ?_⟩
  · intro c hc
    exact ⟨inverseSmoothFamily P b₀ hVU hm hc,
      inverseSmoothFamily_apply P b₀ hVU hm hc⟩
  · intro f
    exact ⟨inverseFourierFamily P b₀ hVU hm f,
      inverseFourierFamily_apply_native P b₀ hVU hm f⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse
