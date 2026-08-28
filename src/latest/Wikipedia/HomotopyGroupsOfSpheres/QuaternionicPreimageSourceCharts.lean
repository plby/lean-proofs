import Wikipedia.HomotopyGroupsOfSpheres.ComplexSphereRotationCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSignCoordinateComparison

/-!
# Coherent outward source charts at the twelve explicit preimages

The source action is the actual sign change, followed by the diagonalizing
rotation and scalar phase. Its positive ambient determinant compares the
outward frames of the actual inverse sphere charts at all these centers.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

local notation "Ambient" => EuclideanSpace ℂ (Fin 3)

def signSourceIsometry (x y : Bool) : Ambient ≃ₗᵢ[ℝ] Ambient :=
  (signRealIsometry x y).trans rotationRealIsometry

theorem signSourceIsometry_det_pos (x y : Bool) :
    0 < (signSourceIsometry x y).toLinearEquiv.toLinearMap.det := by
  change 0 < (rotationRealIsometry.toLinearEquiv.toLinearMap.comp
    (signRealIsometry x y).toLinearEquiv.toLinearMap).det
  rw [LinearMap.det_comp]
  exact mul_pos rotationRealIsometry_det_pos (signRealIsometry_det_pos x y)

theorem signSourceIsometry_sphere (x y : Bool) (z : UnitSphere) :
    SphereCenteredCoordinates.sphereIsometry (signSourceIsometry x y) z =
      rotationSphere (signSphere x y z) := by
  apply Subtype.ext
  rfl

def preimageSourceIsometry (u : unitary ℂ) (b : Bool × Bool) : Ambient ≃ₗᵢ[ℝ] Ambient :=
  (signSourceIsometry b.1 b.2).trans (scalarRealIsometry (negativePhase u))

theorem preimageSourceIsometry_det_pos (u : unitary ℂ) (b : Bool × Bool) :
    0 < (preimageSourceIsometry u b).toLinearEquiv.toLinearMap.det := by
  change 0 < ((scalarRealIsometry (negativePhase u)).toLinearEquiv.toLinearMap.comp
    (signSourceIsometry b.1 b.2).toLinearEquiv.toLinearMap).det
  rw [LinearMap.det_comp, scalarRealIsometry_det, one_mul]
  exact signSourceIsometry_det_pos b.1 b.2

theorem preimageSourceIsometry_sphere (u : unitary ℂ) (b : Bool × Bool) (z : UnitSphere) :
    SphereCenteredCoordinates.sphereIsometry (preimageSourceIsometry u b) z =
      scalarSphere (negativePhase u) (rotationSphere (signSphere b.1 b.2 z)) := by
  apply Subtype.ext
  rfl

theorem preimageSourceIsometry_center (u : unitary ℂ) (b : Bool × Bool) :
    SphereCenteredCoordinates.sphereIsometry (preimageSourceIsometry u b) rotatedInput =
      phaseInput u b := by
  rw [preimageSourceIsometry_sphere, phaseInput_eq_scalar_signSphereInput]
  rfl

def preimageSourceChart (u : unitary ℂ) (b : Bool × Bool)
    (v : SphereCenteredCoordinates.Tangent rotatedInput) : UnitSphere :=
  SphereCenteredCoordinates.sphereIsometry (preimageSourceIsometry u b)
    (SphereCenteredCoordinates.inverse rotatedInput v)

theorem preimageSourceChart_zero (u : unitary ℂ) (b : Bool × Bool) :
    preimageSourceChart u b 0 = phaseInput u b := by
  rw [preimageSourceChart, SphereCenteredCoordinates.inverse_zero,
    preimageSourceIsometry_center]

theorem preimageSourceChart_is_centered_chart (u : unitary ℂ) (b : Bool × Bool)
    (v : SphereCenteredCoordinates.Tangent rotatedInput) :
    preimageSourceChart u b v =
      SphereCenteredCoordinates.inverse
        (SphereCenteredCoordinates.sphereIsometry (preimageSourceIsometry u b) rotatedInput)
        (SphereCenteredCoordinates.tangentIsometry (preimageSourceIsometry u b) rotatedInput v) :=
  (SphereCenteredCoordinates.inverse_tangentIsometry
    (preimageSourceIsometry u b) rotatedInput v).symm

theorem hasFDerivAt_preimageSourceChart (u : unitary ℂ) (b : Bool × Bool) :
    HasFDerivAt (fun v ↦ (preimageSourceChart u b v).val)
      ((preimageSourceIsometry u b).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (SphereCenteredCoordinates.Tangent rotatedInput).subtypeL) 0 :=
  (preimageSourceIsometry u b).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp 0
    (SphereCenteredCoordinates.hasFDerivAt_inverse_val rotatedInput)

def preimageOutwardFrame (u : unitary ℂ) (b : Bool × Bool)
    (v : Module.Basis (Fin 5) ℝ (SphereCenteredCoordinates.Tangent rotatedInput)) :
    Module.Basis (Unit ⊕ Fin 5) ℝ Ambient :=
  (SphereCenteredCoordinates.outwardFrame rotatedInput v).map
    (preimageSourceIsometry u b).toLinearEquiv

theorem preimageOutwardFrame_normal (u : unitary ℂ) (b : Bool × Bool)
    (v : Module.Basis (Fin 5) ℝ (SphereCenteredCoordinates.Tangent rotatedInput)) :
    preimageOutwardFrame u b v (Sum.inl ()) = (phaseInput u b).val := by
  change preimageSourceIsometry u b
    (SphereCenteredCoordinates.outwardFrame rotatedInput v (Sum.inl ())) = _
  rw [SphereCenteredCoordinates.outwardFrame_normal]
  exact congrArg Subtype.val (preimageSourceIsometry_center u b)

theorem preimageOutwardFrame_tangent (u : unitary ℂ) (b : Bool × Bool)
    (v : Module.Basis (Fin 5) ℝ (SphereCenteredCoordinates.Tangent rotatedInput)) (i : Fin 5) :
    preimageOutwardFrame u b v (Sum.inr i) =
      fderiv ℝ (fun w ↦ (preimageSourceChart u b w).val) 0 (v i) := by
  rw [(hasFDerivAt_preimageSourceChart u b).fderiv]
  change preimageSourceIsometry u b
    (SphereCenteredCoordinates.outwardFrame rotatedInput v (Sum.inr i)) =
      preimageSourceIsometry u b (v i).val
  rw [SphereCenteredCoordinates.outwardFrame_tangent]

/-- The actual normal-plus-chart-derivative frames have one common orientation. -/
theorem preimageOutwardFrame_orientation (u : unitary ℂ) (b : Bool × Bool)
    (v : Module.Basis (Fin 5) ℝ (SphereCenteredCoordinates.Tangent rotatedInput)) :
    (preimageOutwardFrame u b v).orientation =
      (SphereCenteredCoordinates.outwardFrame rotatedInput v).orientation :=
  (Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos
    (SphereCenteredCoordinates.outwardFrame rotatedInput v)
    (preimageSourceIsometry u b).toLinearEquiv).mpr
      (preimageSourceIsometry_det_pos u b)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
