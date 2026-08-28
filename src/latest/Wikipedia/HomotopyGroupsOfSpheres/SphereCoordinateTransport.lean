import Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

/-! # Transport of target coordinates along an equality of sphere centers -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def tangentTransport (x y : UnitSphere E) (h : x = y) : Tangent x ≃L[ℝ] Tangent y :=
  (LinearEquiv.ofEq (Tangent x) (Tangent y) (congrArg Tangent h)).toContinuousLinearEquiv

theorem tangentTransport_val (x y : UnitSphere E) (h : x = y) (v : Tangent x) :
    (tangentTransport x y h v).val = v.val := rfl

theorem tangentTransport_stereoToFun (x y : UnitSphere E) (h : x = y) (v : E) :
    tangentTransport x y h (stereoToFun (-x.val) v) = stereoToFun (-y.val) v := by
  cases h
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
