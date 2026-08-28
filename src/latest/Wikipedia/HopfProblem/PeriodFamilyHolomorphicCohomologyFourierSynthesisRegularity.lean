import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Genuine joint smoothness of the original Fourier synthesis

The derivative of the actual sum is the actual synthesis of the
differentiated coefficients. Since the proved rapid-coefficient class is
closed under every fixed joint direction, finite-dimensional induction
gives all orders of joint real smoothness. This constructs a genuine
smooth family on the original base and unit torus, without postulating
any regularity of the infinite sum.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

/-- Every finite order of joint regularity follows from the genuine
termwise derivative theorem and the proved coefficient closure. -/
theorem jointSynthesis_contDiffOn_nat {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (n : ℕ) :
    ContDiffOn ℝ n (jointSynthesis c) (Smooth.baseProductDomain U (Fin 4 → ℝ)) := by
  induction n generalizing c with
  | zero =>
    change ContDiffOn ℝ (0 : ℕ∞ω) (jointSynthesis c)
      (Smooth.baseProductDomain U (Fin 4 → ℝ))
    rw [contDiffOn_zero]
    exact fun x hx => (hasFDerivAt_jointSynthesis hc x hx).continuousAt.continuousWithinAt
  | succ n ih =>
    change ContDiffOn ℝ ((n : ℕ∞ω) + 1) (jointSynthesis c)
      (Smooth.baseProductDomain U (Fin 4 → ℝ))
    apply (contDiffOn_succ_iff_fderiv_of_isOpen
      (Smooth.baseProductDomain_isOpen U (Fin 4 → ℝ))).mpr
    refine ⟨jointSynthesis_differentiableOn hc, ?_, ?_⟩
    · intro h
      simp at h
    · apply contDiffOn_clm_apply.mpr
      intro v
      exact (ih (hc.jointDerivative v)).congr
        (fun x hx => jointSynthesis_fderiv_apply hc x v hx)

/-- The actual infinite Fourier sum is jointly real smooth on the
original open base product. -/
theorem jointSynthesis_contDiffOn {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) :
    ContDiffOn ℝ ∞ (jointSynthesis c) (Smooth.baseProductDomain U (Fin 4 → ℝ)) :=
  contDiffOn_infty.mpr (fun n => jointSynthesis_contDiffOn_nat hc n)

/-- The literal quotient Fourier series is a genuine jointly smooth
family. Its regularity is proved from the original coefficient data. -/
def smoothFamily {U : Opens ℂ} {c : Coefficients} (hc : SmoothRapidCoefficients U c) :
    FourierParameter.SmoothFamily U (Fin 4) where
  toFun := synthesis c
  smooth_lift := (jointSynthesis_contDiffOn hc).congr (ambientLift_synthesis_eqOn c)

@[simp] theorem smoothFamily_apply {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (b : U) (t : UnitAddTorus (Fin 4)) :
    smoothFamily hc (b, t) = ∑' k, c k (b : ℂ) * mFourier k t := rfl

/-- Joint continuity on the actual quotient is derived from the proved
smooth lift, not assumed separately. -/
theorem synthesis_continuous {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) : Continuous (synthesis (U := U) c) :=
  (smoothFamily hc).continuous

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
