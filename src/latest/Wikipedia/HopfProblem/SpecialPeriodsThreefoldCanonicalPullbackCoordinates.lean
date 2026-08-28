import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalLocalFrames
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Actual tangent coordinates for canonical pullback

The coordinate derivative of a map is computed from its genuine manifold
derivative and the actual tangent-bundle chart changes.  Thus determinant
coefficients used for canonical pullback are not additional transition data.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace Model M]
  [IsManifold I ω M] [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- The actual derivative of the coordinate expression of a map. -/
def chartDerivative (f : M → N) (i : atlas Model M) (j : atlas Model N)
    (x : M) : Model →L[ℂ] Model :=
  fderiv ℂ (j.val ∘ f ∘ i.val.symm) (i.val x)

/-- The determinant of the genuine chart-coordinate derivative. -/
def chartDeterminant (f : M → N) (i : atlas Model M) (j : atlas Model N)
    (x : M) : ℂ :=
  LinearMap.det (chartDerivative f i j x).toLinearMap

/-- The derivative of an actual atlas chart is its tangent coordinate
change from the preferred chart. -/
theorem mfderiv_atlas (i : atlas Model M) {x : M} (hx : x ∈ i.val.source) :
    mfderiv I I i.val x = (Atlas.tangentCore M).coordChange (achart Model x) i x := by
  have hi : MDifferentiableAt I I i.val x := mdifferentiableAt_atlas i.property hx
  rw [hi.mfderiv, Atlas.tangentCore_coordChange]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ, chartAt_self_eq]
  rfl

/-- The inverse atlas chart gives the reverse tangent coordinate change. -/
theorem mfderiv_atlas_symm (i : atlas Model M) {x : M} (hx : x ∈ i.val.source) :
    mfderiv I I i.val.symm (i.val x) =
      (Atlas.tangentCore M).coordChange i (achart Model x) x := by
  have hi : MDifferentiableAt I I i.val.symm (i.val x) :=
    mdifferentiableAt_atlas_symm i.property (i.val.map_source hx)
  rw [hi.mfderiv, Atlas.tangentCore_coordChange]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ, i.val.left_inv hx,
    chartAt_self_eq]
  rfl

/-- Coordinate chain rule through the actual tangent-bundle chart changes. -/
theorem chartDerivative_eq_tangentCore (f : M → N)
    (i : atlas Model M) (j : atlas Model N) {x : M}
    (hi : x ∈ i.val.source) (hj : f x ∈ j.val.source)
    (hf : MDifferentiableAt I I f x) :
    chartDerivative f i j x =
      ((Atlas.tangentCore N).coordChange (achart Model (f x)) j (f x)).comp
        ((mfderiv I I f x).comp
          ((Atlas.tangentCore M).coordChange i (achart Model x) x)) := by
  have his : MDifferentiableAt I I i.val.symm (i.val x) :=
    mdifferentiableAt_atlas_symm i.property (i.val.map_source hi)
  have hjd : MDifferentiableAt I I j.val (f x) := mdifferentiableAt_atlas j.property hj
  have hfd : MDifferentiableAt I I f (i.val.symm (i.val x)) := by
    simpa only [i.val.left_inv hi] using hf
  have hjd' : MDifferentiableAt I I j.val ((f ∘ i.val.symm) (i.val x)) := by
    simpa only [Function.comp_apply, i.val.left_inv hi] using hjd
  rw [chartDerivative, ← mfderiv_eq_fderiv,
    mfderiv_comp (i.val x) hjd' (hfd.comp (i.val x) his),
    mfderiv_comp (i.val x) hfd his]
  apply ContinuousLinearMap.ext
  intro v
  change mfderiv I I j.val (f (i.val.symm (i.val x)))
    (mfderiv I I f (i.val.symm (i.val x)) (mfderiv I I i.val.symm (i.val x) v)) = _
  rw [i.val.left_inv hi]
  rw [mfderiv_atlas j hj, mfderiv_atlas_symm i hi]
  rfl

private theorem determinant_comp_three (A B C : Model →L[ℂ] Model) :
    LinearMap.det (A.comp (B.comp C)).toLinearMap =
      LinearMap.det A.toLinearMap * LinearMap.det B.toLinearMap *
        LinearMap.det C.toLinearMap := by
  change LinearMap.det (A.toLinearMap.comp (B.toLinearMap.comp C.toLinearMap)) = _
  rw [LinearMap.det_comp, LinearMap.det_comp, ← mul_assoc]

/-- The coordinate determinant factors through the intrinsic derivative
and the two genuine tangent-coordinate Jacobians. -/
theorem chartDeterminant_eq_jacobians (f : M → N)
    (i : atlas Model M) (j : atlas Model N) {x : M}
    (hi : x ∈ i.val.source) (hj : f x ∈ j.val.source)
    (hf : MDifferentiableAt I I f x) :
    chartDeterminant f i j x =
      Atlas.jacobian N (achart Model (f x)) j (f x) *
        LinearMap.det (mfderiv I I f x).toLinearMap *
        Atlas.jacobian M i (achart Model x) x := by
  rw [chartDeterminant, chartDerivative_eq_tangentCore f i j hi hj hf]
  exact determinant_comp_three
    ((Atlas.tangentCore N).coordChange (achart Model (f x)) j (f x))
    (mfderiv I I f x) ((Atlas.tangentCore M).coordChange i (achart Model x) x)

/-- A genuine local biholomorphism has nonzero chart determinant. -/
theorem chartDeterminant_ne_zero (f : M → N)
    (i : atlas Model M) (j : atlas Model N) {x : M}
    (hi : x ∈ i.val.source) (hj : f x ∈ j.val.source)
    (hf : IsLocalDiffeomorphAt I I ω f x) : chartDeterminant f i j x ≠ 0 := by
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let e : Model ≃L[ℂ] Model := hf.mfderivToContinuousLinearEquiv hω
  have hd : LinearMap.det (mfderiv I I f x).toLinearMap ≠ 0 :=
    e.toLinearEquiv.isUnit_det'.ne_zero
  rw [chartDeterminant_eq_jacobians f i j hi hj (hf.mdifferentiableAt hω)]
  exact mul_ne_zero
    (mul_ne_zero (Atlas.jacobian_ne_zero N (achart Model (f x)) j
      (mem_chart_source Model (f x)) hj) hd)
    (Atlas.jacobian_ne_zero M i (achart Model x) hi (mem_chart_source Model x))

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
