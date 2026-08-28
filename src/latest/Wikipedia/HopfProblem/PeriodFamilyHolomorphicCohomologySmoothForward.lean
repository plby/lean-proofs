import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothMatrix
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothOpen
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneTangent

/-!
# Joint real smoothness of the original forward period coordinates

The ambient formula uses the actual real period matrix on the original open
base. On that base it agrees literally with `P.periodEquiv`. Its smoothness
therefore gives real smoothness on the unchanged native open-base product.
The same argument covers change from any fixed genuine period coordinates.
No holomorphicity of the real-coordinate trivialization is asserted.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local instance smoothForwardProductChartedSpace {F : Type*}
    [NormedAddCommGroup F] : ChartedSpace (ℂ × F) (U × F) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ F) (U × F))

/-- The original forward period formula in ambient real coordinates. -/
def periodCoordinates (x : ℂ × RealPlane₄) : ComplexPlane₂ :=
  complexCoordinates (realPeriodMatrix P x.1 *ᵥ x.2)

/-- On the original base this is exactly the given family's period equivalence. -/
@[simp] theorem periodCoordinates_apply (b : U) (v : RealPlane₄) :
    periodCoordinates P ((b : ℂ), v) = P.periodEquiv b v := by
  simp only [periodCoordinates, realPeriodMatrix_apply, HolomorphicPeriodMap.periodEquiv_apply]

/-- Joint smoothness in the original base coordinate and real fibre vector. -/
theorem periodCoordinates_contDiffOn :
    ContDiffOn ℝ ∞ (periodCoordinates P) (baseProductDomain U RealPlane₄) := by
  have hM : ContDiffOn ℝ ∞
      (fun x : ℂ × RealPlane₄ => realPeriodMatrix P x.1)
      (baseProductDomain U RealPlane₄) :=
    (realPeriodMatrix_contDiffOn P).comp contDiffOn_fst (fun _ hx => hx)
  exact complexCoordinates.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (matrix_mulVec_contDiffOn hM contDiffOn_snd)

/-- The actual native forward period map is jointly real smooth. -/
theorem periodCoordinates_native_contMDiff :
    ContMDiff (modelWithCornersSelf ℝ (ℂ × RealPlane₄))
      (modelWithCornersSelf ℝ ComplexPlane₂) ∞
      (fun x : U × RealPlane₄ => P.periodEquiv x.1 x.2) := by
  simpa only [periodCoordinates_apply] using
    contMDiff_productOpen_of_contDiffOn (periodCoordinates_contDiffOn P)

/-- Change from a fixed original period coordinate system to the varying one. -/
def periodChange (p₀ : PeriodDomain) (x : ℂ × ComplexPlane₂) : ComplexPlane₂ :=
  periodCoordinates P (x.1, (PeriodTorusTypeOneOne.periodEquiv p₀).symm x.2)

/-- The change formula uses the actual varying and fixed real period equivalences. -/
@[simp] theorem periodChange_apply (p₀ : PeriodDomain) (b : U) (z : ComplexPlane₂) :
    periodChange P p₀ ((b : ℂ), z) =
      P.periodEquiv b ((PeriodTorusTypeOneOne.periodEquiv p₀).symm z) :=
  periodCoordinates_apply P b _

/-- The fixed-period coordinate change is jointly real smooth on the full base domain. -/
theorem periodChange_contDiffOn (p₀ : PeriodDomain) :
    ContDiffOn ℝ ∞ (periodChange P p₀) (baseProductDomain U ComplexPlane₂) := by
  have hlin : ContDiff ℝ ∞ (fun z : ComplexPlane₂ =>
      (PeriodTorusTypeOneOne.periodEquiv p₀).symm z) :=
    (PeriodTorusTypeOneOne.periodEquiv p₀).symm.toContinuousLinearEquiv.contDiff
  exact (periodCoordinates_contDiffOn P).comp
    (contDiffOn_fst.prodMk (hlin.comp_contDiffOn contDiffOn_snd))
    (fun _ hx => hx)

/-- Native real smoothness of the actual change from a fixed period torus. -/
theorem periodChange_native_contMDiff (p₀ : PeriodDomain) :
    ContMDiff (modelWithCornersSelf ℝ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℝ ComplexPlane₂) ∞
      (fun x : U × ComplexPlane₂ =>
        P.periodEquiv x.1 ((PeriodTorusTypeOneOne.periodEquiv p₀).symm x.2)) := by
  simpa only [periodChange_apply] using
    contMDiff_productOpen_of_contDiffOn (periodChange_contDiffOn P p₀)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth
