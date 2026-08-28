import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothOpen
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothMatrix
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneTangent

/-!
# Joint real smoothness of the original inverse period coordinates

The inverse is the genuine inverse of the original real period matrix.
Its entries are real smooth because the original period functions are
holomorphic and their actual determinant is everywhere nonzero. The native
open-base statement uses the unchanged inherited base and covering-space
charts, and its function is literally `P.periodEquiv.symm`.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- Real smoothness of the genuine inverse matrix in the original open base chart. -/
theorem realPeriodMatrix_inv_contDiffOn :
    ContDiffOn ℝ ∞ (fun z => (realPeriodMatrix P z)⁻¹) U :=
  matrix_inv_contDiffOn (realPeriodMatrix_contDiffOn P) (realPeriodMatrix_det_ne_zero P)

/-- Ambient coordinate expression for the original inverse period isomorphism. -/
def inversePeriodCoordinates (x : ℂ × ComplexPlane₂) : RealPlane₄ :=
  (realPeriodMatrix P x.1)⁻¹ *ᵥ complexCoordinates.symm x.2

/-- On the original base open this is exactly the native inverse period map. -/
@[simp] theorem inversePeriodCoordinates_apply (b : U) (z : ComplexPlane₂) :
    inversePeriodCoordinates P ((b : ℂ), z) = (P.periodEquiv b).symm z := by
  change (realPeriodMatrix P b)⁻¹ *ᵥ complexCoordinates.symm z = _
  rw [realPeriodMatrix_apply, P.periodEquiv_symm_apply]

/-- The coordinate expression is jointly real smooth in the base and complex vector. -/
theorem inversePeriodCoordinates_contDiffOn :
    ContDiffOn ℝ ∞ (inversePeriodCoordinates P) (baseProductDomain U ComplexPlane₂) := by
  have hA : ContDiffOn ℝ ∞ (fun x : ℂ × ComplexPlane₂ => realPeriodMatrix P x.1)
      (baseProductDomain U ComplexPlane₂) :=
    (realPeriodMatrix_contDiffOn P).comp
      (f := fun x : ℂ × ComplexPlane₂ => x.1) contDiffOn_fst (fun _ hx => hx)
  have hv : ContDiffOn ℝ ∞ (fun x : ℂ × ComplexPlane₂ => complexCoordinates.symm x.2)
      (baseProductDomain U ComplexPlane₂) :=
    (complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp
      (f := fun x : ℂ × ComplexPlane₂ => x.2) contDiff_snd).contDiffOn
  exact matrix_inv_mulVec_contDiffOn hA hv
    (fun x hx => realPeriodMatrix_det_ne_zero P x.1 hx)

local instance smoothCoordinatesProductChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

/-- The actual inverse-period map is jointly real smooth in the unchanged
native open-base product chart, with no smooth-symbol premise. -/
theorem inversePeriodCoordinates_native_contMDiff :
    ContMDiff (modelWithCornersSelf ℝ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℝ RealPlane₄) ∞
      (fun x : U × ComplexPlane₂ => (P.periodEquiv x.1).symm x.2) := by
  have h := contMDiff_productOpen_of_contDiffOn (inversePeriodCoordinates_contDiffOn P)
  exact h.congr (fun x => (inversePeriodCoordinates_apply P x.1 x.2).symm)

/-- Changing from the actual varying basis to any fixed original period basis
is real smooth on the original complex-vector covering spaces. -/
theorem inversePeriodChange_native_contMDiff (p₀ : PeriodDomain) :
    ContMDiff (modelWithCornersSelf ℝ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℝ ComplexPlane₂) ∞
      (fun x : U × ComplexPlane₂ =>
        PeriodTorusTypeOneOne.periodEquiv p₀ ((P.periodEquiv x.1).symm x.2)) := by
  have h₀ : ContDiff ℝ ∞ (PeriodTorusTypeOneOne.periodEquiv p₀) :=
    (PeriodTorusTypeOneOne.periodEquiv p₀).toContinuousLinearEquiv.contDiff
  exact h₀.contMDiff.comp (inversePeriodCoordinates_native_contMDiff P)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth
