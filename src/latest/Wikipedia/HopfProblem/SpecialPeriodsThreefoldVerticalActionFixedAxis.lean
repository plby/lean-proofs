import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedTangent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedToricLocus
import Wikipedia.HopfProblem.CuspAxisCharts

/-!
# The actual middle-axis differential

The fixed coordinate line is parametrized inside the genuine open toric
domain. Its composite into the threefold is exactly the original cusp
double-curve axis map. The chain rule identifies its actual tangent
image with the middle line under the actual coordinate differential.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates

open ToricCharts ToricFan HolomorphicDifferentialForms

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "CD" => CuspGeometry.data

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The literal middle-coordinate linear inclusion. -/
def axisLinear : ℂ →L[ℂ] E₃ := ContinuousLinearMap.single ℂ (fun _ : Fin 3 => ℂ) 1

@[simp] theorem axisLinear_apply (z : ℂ) : axisLinear z = ![0, z, 0] := by
  ext j
  fin_cases j <;> simp [axisLinear]

/-- The middle line lies in the actual cusp coordinate domain at every point. -/
def axis (z : ℂ) : Domain :=
  ⟨axisLinear z, by
    change ‖Triangle.time (axisLinear z)‖ < (CD).radius
    rw [axisLinear_apply]
    simpa [Triangle.time] using (CD).radius_pos⟩

@[simp] theorem axis_coe (z : ℂ) : (axis z : E₃) = axisLinear z := rfl

theorem axis_holomorphic : ContMDiff I₁ I₃ ω axis := by
  intro z
  have he : ContMDiffAt I₁ I₃ ω ((Subtype.val : Domain → E₃) ∘ axis) z ↔
      ContMDiffAt I₁ I₃ ω axis z := ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (axisLinear.contDiff.contMDiff z)

theorem axis_mfderiv (z : ℂ) : mfderiv I₁ I₃ axis z = axisLinear := by
  have h := mfderiv_comp z
    (hasMFDerivAt_openSubtypeVal (E := E₃) Domain (axis z)).mdifferentiableAt
    (axis_holomorphic.mdifferentiableAt (by simp) (x := z))
  change mfderiv I₁ I₃ axisLinear z = _ at h
  rw [mfderiv_openSubtypeVal, ContinuousLinearMap.mfderiv_eq] at h
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L : ℂ →L[ℂ] E₃ => L v) h.symm

theorem axis_fixed (u : ℂˣ) (z : ℂ) : coordinateAction u (axis z) = axis z :=
  coordinateAction_eq_self u (axis z) (by simp [axis_coe])

/-- The genuine affine axis map into the global threefold. -/
def globalAxis (a : Triangle) : ℂ → Threefold.Space := globalMap a ∘ axis

theorem globalAxis_holomorphic (a : Triangle) : ContMDiff I₁ IF ω (globalAxis a) :=
  (globalMap_holomorphic a).comp axis_holomorphic

/-- Agreement with the original cusp double-curve parametrization. -/
theorem globalAxis_eq_native (a : Triangle) (z : ℂ) :
    globalAxis a z = CuspGeometry.inclusion
      (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos a 1 z) := by
  apply congrArg CuspGeometry.inclusion
  apply congrArg (CuspQuotient.quotientMap (CD).correction (CD).radius)
  apply Subtype.ext
  change ToricSpace.inclusion a (axisLinear z) =
    ToricSpace.inclusion a (Triangle.axisPoint a 1 z)
  rw [axisLinear_apply, FixedToric.axisPoint_one]

/-- The actual derivative of the global curve parametrization. -/
theorem globalAxis_mfderiv (a : Triangle) (z : ℂ) (v : ℂ) :
    mfderiv I₁ IF (globalAxis a) z v = tangentEquiv a (axis z) (axisLinear v) := by
  have h := mfderiv_comp z
    ((globalMap_holomorphic a).mdifferentiableAt (by simp) (x := axis z))
    (axis_holomorphic.mdifferentiableAt (by simp) (x := z))
  rw [axis_mfderiv] at h
  exact congrArg (fun L : ℂ →L[ℂ] (ℂ × ComplexPlane₂) => L v) h

/-- The actual tangent range is the image of the middle coordinate line
under the derivative of the genuine local coordinate covering. -/
theorem tangentEquiv_axis_range (a : Triangle) (z : ℂ) :
    axisLinear.range.map (tangentEquiv a (axis z)).toLinearEquiv.toLinearMap =
      (mfderiv I₁ IF (globalAxis a) z).range := by
  apply le_antisymm
  · rintro w ⟨v, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, globalAxis_mfderiv a z t⟩
  · rintro w ⟨t, rfl⟩
    exact ⟨axisLinear t, ⟨t, rfl⟩, (globalAxis_mfderiv a z t).symm⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates
