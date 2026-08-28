import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsNativeDerivativeBasic

/-!
# Actual native holomorphic pullback preserves antiholomorphic covectors

Complex-scalar compatibility is proved for the genuine real manifold
derivative, rather than imposed on a candidate pullback map.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  {f : M → N} {x : M}

/-- The genuine real manifold derivative of a complex differentiable map
commutes with every original complex scalar. -/
theorem mfderiv_complex_smul
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x) (c : ℂ) (v : E) :
    (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) (c • v) =
      c • (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) v := by
  rw [mfderiv_restrictScalars hf]
  exact (show E →L[ℂ] F from mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x).map_smul c v

/-- In particular, the actual real manifold derivative respects the
original complex structure on the source and target tangent models. -/
theorem mfderiv_I
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x) (v : E) :
    (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) (Complex.I • v) =
      Complex.I • (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) v :=
  mfderiv_complex_smul hf Complex.I v

/-- Antiholomorphic projection commutes with pullback by the actual
native real derivative of a genuinely complex differentiable map. -/
theorem antiPart_comp_mfderiv
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x) (L : F →L[ℝ] ℂ) :
    antiPart (L.comp
      (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) =
      (antiPart L).comp
        (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) := by
  apply ContinuousLinearMap.ext
  intro v
  change antiPart (L.comp
      (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) v =
    antiPart L ((show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) v)
  rw [antiPart_apply, antiPart_apply]
  change
    (L ((show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) v) +
      Complex.I * L
        ((show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) (Complex.I • v))) / 2 =
    (L ((show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) v) +
      Complex.I * L
        (Complex.I • (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) v)) / 2
  rw [mfderiv_I hf]

/-- Pullback of an actual antiholomorphic covector along the genuine
native derivative remains an actual antiholomorphic covector. -/
theorem pullback_mem_antiCovectors
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x) (L : AntiCovector F) :
    L.val.comp (show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) ∈
      antiCovectors := by
  intro v
  change L.val
      ((show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) (Complex.I • v)) =
    -Complex.I * L.val
      ((show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) v)
  rw [mfderiv_I hf]
  exact L.property _

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
