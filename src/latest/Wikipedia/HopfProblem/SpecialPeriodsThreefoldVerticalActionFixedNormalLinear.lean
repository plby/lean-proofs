import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedAxis
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The quotient by the actual middle coordinate line

This is the elementary coordinate quotient used to identify the genuine
geometric normal tangent space. Its topology is the original quotient
topology, and the identification records the two remaining coordinates.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates

open ToricCharts ToricFan

local notation "E₃" => CoordinateSpace 3
local notation "E₂" => CoordinateSpace 2

/-- The two coordinates transverse to the fixed line, in weight order `(-1,+1)`. -/
def normalProjection : E₃ →L[ℂ] E₂ :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (![0, 2] j)

@[simp] theorem normalProjection_apply (w : E₃) : normalProjection w = ![w 0, w 2] := by
  ext j
  fin_cases j <;> rfl

/-- The literal complementary coordinate plane. -/
def normalSection : E₂ →L[ℂ] E₃ :=
  ContinuousLinearMap.pi fun j =>
    ![ContinuousLinearMap.proj 0, 0, ContinuousLinearMap.proj 1] j

@[simp] theorem normalSection_apply (w : E₂) : normalSection w = ![w 0, 0, w 1] := by
  ext j
  fin_cases j <;> rfl

@[simp] theorem normalProjection_section (w : E₂) :
    normalProjection (normalSection w) = w := by
  ext j
  fin_cases j <;> rfl

theorem normalProjection_surjective : Function.Surjective normalProjection :=
  fun w => ⟨normalSection w, normalProjection_section w⟩

/-- Its kernel is exactly the middle-coordinate tangent image. -/
theorem normalProjection_ker : normalProjection.ker = axisLinear.range := by
  ext w
  constructor
  · intro hw
    have h : normalProjection w = 0 := hw
    have h0 : w 0 = 0 := congrFun h 0
    have h2 : w 2 = 0 := congrFun h 1
    refine ⟨w 1, ?_⟩
    change axisLinear (w 1) = w
    rw [axisLinear_apply]
    ext j
    fin_cases j <;> simp [h0, h2]
  · rintro ⟨z, rfl⟩
    change normalProjection (axisLinear z) = 0
    ext j
    fin_cases j <;> simp [normalProjection_apply, axisLinear_apply]

/-- The natural quotient by the coordinate tangent line. -/
abbrev CoordinateNormal := E₃ ⧸ axisLinear.range

/-- The first isomorphism theorem identifies this actual quotient with
the two transverse coordinates. -/
def coordinateNormalLinearEquiv : CoordinateNormal ≃ₗ[ℂ] E₂ :=
  (Submodule.quotEquivOfEq _ _ normalProjection_ker.symm).trans
    (normalProjection.toLinearMap.quotKerEquivOfSurjective normalProjection_surjective)

@[simp] theorem coordinateNormalLinearEquiv_mk (w : E₃) :
    coordinateNormalLinearEquiv (Submodule.Quotient.mk w) = normalProjection w := rfl

@[simp] theorem coordinateNormalLinearEquiv_symm_apply (w : E₂) :
    coordinateNormalLinearEquiv.symm w = Submodule.Quotient.mk (normalSection w) := by
  apply coordinateNormalLinearEquiv.injective
  rw [LinearEquiv.apply_symm_apply, coordinateNormalLinearEquiv_mk, normalProjection_section]

/-- The same identification is continuous in both directions for the
natural quotient topology, without replacing that topology. -/
def coordinateNormalEquiv : CoordinateNormal ≃L[ℂ] E₂ :=
  { coordinateNormalLinearEquiv with
    continuous_toFun := axisLinear.range.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
      normalProjection.continuous
    continuous_invFun := by
      change Continuous (fun w => coordinateNormalLinearEquiv.symm w)
      simp only [coordinateNormalLinearEquiv_symm_apply]
      exact continuous_quot_mk.comp normalSection.continuous }

@[simp] theorem coordinateNormalEquiv_mk (w : E₃) :
    coordinateNormalEquiv (Submodule.Quotient.mk w) = normalProjection w := rfl

@[simp] theorem diagonal_axisLinear (u : ℂˣ) (z : ℂ) :
    diagonal u (axisLinear z) = axisLinear z := by
  rw [diagonal_apply, axisLinear_apply]
  ext j
  fin_cases j <;> simp

/-- The two transverse coordinates have exactly the two source characters. -/
theorem normalProjection_diagonal (u : ℂˣ) (w : E₃) :
    normalProjection (diagonal u w) =
      ![(u : ℂ)⁻¹ * (normalProjection w) 0, (u : ℂ) * (normalProjection w) 1] := by
  ext j
  fin_cases j <;> simp

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates
