import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Real and complex derivatives of maps in their original manifold charts

Both derivatives use exactly the same original source and target charts.
Their comparison follows from the actual written-in-chart derivative and
restriction of scalars for the Fréchet derivative. The displayed model
identifications are only the defining type synonyms of tangent fibres.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  {f : M → N} {x : M}

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
/-- Genuine complex manifold differentiability gives the actual complex
Fréchet derivative of the map written in the original chosen charts. -/
theorem writtenInChart_differentiableAt
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x) :
    DifferentiableAt ℂ ((chartAt F (f x)) ∘ f ∘ (chartAt E x).symm)
      (chartAt E x x) := by
  simpa only [mfld_simps, differentiableWithinAt_univ] using
    hf.differentiableWithinAt_writtenInExtChartAt

/-- Complex differentiability implies real differentiability in the same
original source and target charted-space structures. -/
theorem mdifferentiableAt_real_of_complex
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x := by
  apply (mdifferentiableAt_iff f x).mpr
  refine ⟨hf.continuousAt, ?_⟩
  simpa only [mfld_simps] using
    hf.differentiableWithinAt_writtenInExtChartAt.restrictScalars ℝ

/-- The actual real manifold derivative is precisely the scalar
restriction of the actual complex manifold derivative, without an atlas
change or an assumed compatibility of derivatives. -/
theorem mfderiv_restrictScalars
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x) :
    (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) =
      (show E →L[ℂ] F from mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x).restrictScalars ℝ := by
  have hr := mdifferentiableAt_real_of_complex hf
  rw [hr.mfderiv, hf.mfderiv]
  simpa only [mfld_simps, fderivWithin_univ] using
    (writtenInChart_differentiableAt hf).fderiv_restrictScalars ℝ

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
