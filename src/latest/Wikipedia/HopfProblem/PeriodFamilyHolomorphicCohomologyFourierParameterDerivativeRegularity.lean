import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeCoefficient
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Genuine Fourier coefficients are real smooth in the original base

Differentiation under Haar integration identifies every directional
derivative with the coefficient of another genuine smooth family. Finite
dimensionality of the real complex line then gives smoothness to every
order, by induction. No regularity of the coefficient is assumed.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

variable {U : Opens ℂ} {d : Type*} [Fintype d]

namespace SmoothFamily

variable (f : SmoothFamily U d)

/-- Each finite order follows from the actual derivative-family identity. -/
theorem coefficientValue_contDiffOn_nat (n : ℕ) (k : d → ℤ) :
    ContDiffOn ℝ n (f.coefficientValue k) U := by
  induction n generalizing f with
  | zero =>
    change ContDiffOn ℝ (0 : ℕ∞ω) (f.coefficientValue k) U
    rw [contDiffOn_zero]
    exact fun z hz => (f.coefficientValue_hasFDerivAt k ⟨z, hz⟩).continuousAt.continuousWithinAt
  | succ n ih =>
    change ContDiffOn ℝ ((n : ℕ∞ω) + 1) (f.coefficientValue k) U
    apply (contDiffOn_succ_iff_fderiv_of_isOpen U.isOpen).mpr
    refine ⟨f.coefficientValue_differentiableOn k, ?_, ?_⟩
    · intro h
      simp at h
    · apply contDiffOn_clm_apply.mpr
      intro v
      exact (ih (f.baseDerivative v)).congr
        (fun z hz => f.coefficientValue_fderiv_apply k z hz v)

/-- The actual Haar coefficient is real smooth on the original open base. -/
theorem coefficientValue_contDiffOn (k : d → ℤ) :
    ContDiffOn ℝ ∞ (f.coefficientValue k) U :=
  contDiffOn_infty.mpr (fun n => f.coefficientValue_contDiffOn_nat n k)

/-- Native real smoothness uses the unchanged inherited chart of the original open base. -/
theorem coefficient_native_contMDiff (k : d → ℤ) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun b : U => mFourierCoeff (fun t => f (b, t)) k) := by
  have h : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun b : U => f.coefficientValue k (b : ℂ)) := by
    rw [← contMDiffOn_univ]
    exact (f.coefficientValue_contDiffOn k).contMDiffOn.comp
      contMDiff_subtype_val.contMDiffOn (fun b _ => b.property)
  simpa only [coefficientValue_apply] using h

end SmoothFamily

/-- Raw real smoothness of the actual parameterized Haar coefficient follows from its joint lift. -/
theorem coefficient_contDiffOn_of_contDiffOn_lift {f : U × UnitAddTorus d → ℂ}
    (hf : ContDiffOn ℝ ∞ (ambientLift f) (Smooth.baseProductDomain U (d → ℝ)))
    (k : d → ℤ) :
    ContDiffOn ℝ ∞ (fun z : ℂ => mFourierCoeff (fun t => ambientValue f (z, t)) k) U :=
  SmoothFamily.coefficientValue_contDiffOn ⟨f, hf⟩ k

/-- The original native coefficient is real smooth, with no extra coefficient-regularity premise. -/
theorem coefficient_native_contMDiff_of_contDiffOn_lift {f : U × UnitAddTorus d → ℂ}
    (hf : ContDiffOn ℝ ∞ (ambientLift f) (Smooth.baseProductDomain U (d → ℝ)))
    (k : d → ℤ) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun b : U => mFourierCoeff (fun t => f (b, t)) k) :=
  SmoothFamily.coefficient_native_contMDiff ⟨f, hf⟩ k

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
