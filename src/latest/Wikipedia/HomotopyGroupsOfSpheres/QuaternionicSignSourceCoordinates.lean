import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPreimageSourceCharts
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateTransport

/-! # The sign families in the original centered source and target charts -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix

def signSourceTangentEquiv (x y : Bool) :
    SphereCenteredCoordinates.Tangent rotatedInput ≃ₗᵢ[ℝ]
      SphereCenteredCoordinates.Tangent (signSphereInput x y) :=
  (signTangentEquiv x y rotatedInput).trans
    (rotationTangentEquiv (signSphere x y rotatedInput))

def signSourceParameterEquiv (x y : Bool) :
    ParameterSpace rotatedInput ≃L[ℝ] ParameterSpace (signSphereInput x y) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (signSourceTangentEquiv x y).toContinuousLinearEquiv)

theorem localSphere_signSourceParameterEquiv (x y : Bool) (p : ParameterSpace rotatedInput) :
    localSphere (signSphereInput x y) (signSourceParameterEquiv x y p) =
      rotationSphere (signSphere x y (SphereCenteredCoordinates.inverse rotatedInput p.2.2)) := by
  change SphereCenteredCoordinates.inverse (rotationSphere (signSphere x y rotatedInput))
    (rotationTangentEquiv _ (signTangentEquiv x y rotatedInput p.2.2)) = _
  rw [inverse_rotationTangentEquiv, inverse_signTangentEquiv]

theorem signProjection_eq_localProjection (x y : Bool) (p : ParameterSpace rotatedInput) :
    signProjection x y p =
      localProjection (signSphereInput x y) (signSourceParameterEquiv x y p) := by
  change firstColumnFormula (Real.pi / 2 + p.1) (Real.pi / 2 + p.2.1)
    (signMatrixFamily x y p) = firstColumnFormula (Real.pi / 2 + p.1)
      (Real.pi / 2 + p.2.1)
        (symmetricMap (localSphere (signSphereInput x y) (signSourceParameterEquiv x y p)))
  rw [localSphere_signSourceParameterEquiv]
  rfl

theorem signSphereInput_hits_target (x y : Bool) :
    firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap (signSphereInput x y)) =
      targetColumn := by
  have h := signProjection_zero x y
  rw [signProjection_eq_localProjection, map_zero, localProjection_zero] at h
  exact h

theorem targetCenter_eq (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    localColumn z 0 = localColumn input 0 := by
  apply Subtype.ext
  change WithLp.toLp 2 (localProjection z 0) = WithLp.toLp 2 (localProjection input 0)
  rw [localProjection_zero, localProjection_zero, hz, input_hits_target]

def targetCoordinateTransport (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    TargetSpace z ≃L[ℝ] TargetSpace input :=
  SphereCenteredCoordinates.tangentTransport (localColumn z 0) (localColumn input 0)
    (targetCenter_eq z hz)

theorem fixedTargetCoordinates_eq_transport (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (p : ParameterSpace z) :
    fixedTargetCoordinates (localProjection z p) =
      targetCoordinateTransport z hz (localCoordinateMap z p) :=
  (SphereCenteredCoordinates.tangentTransport_stereoToFun
    (localColumn z 0) (localColumn input 0) (targetCenter_eq z hz) (localColumn z p).val).symm

theorem signCoordinateMap_eq_transport (x y : Bool) :
    signCoordinateMap x y =
      targetCoordinateTransport (signSphereInput x y) (signSphereInput_hits_target x y) ∘
        localCoordinateMap (signSphereInput x y) ∘ signSourceParameterEquiv x y := by
  funext p
  change fixedTargetCoordinates (signProjection x y p) = _
  rw [signProjection_eq_localProjection, fixedTargetCoordinates_eq_transport]
  rfl

def signCoordinateDerivativeEquiv (x y : Bool) :
    ParameterSpace rotatedInput ≃L[ℝ] TargetSpace input :=
  (signSourceParameterEquiv x y).trans
    ((localCoordinateDerivativeEquiv (signSphereInput x y) (signSphereInput_hits_target x y)).trans
      (targetCoordinateTransport (signSphereInput x y) (signSphereInput_hits_target x y)))

theorem hasFDerivAt_signCoordinateDerivativeEquiv (x y : Bool) :
    HasFDerivAt (signCoordinateMap x y)
      (signCoordinateDerivativeEquiv x y).toContinuousLinearMap 0 := by
  rw [signCoordinateMap_eq_transport]
  have hD := hasFDerivAt_localCoordinateDerivativeEquiv (signSphereInput x y)
    (signSphereInput_hits_target x y)
  have hP := (signSourceParameterEquiv x y).toContinuousLinearMap.hasFDerivAt (x := 0)
  have hD' : HasFDerivAt (localCoordinateMap (signSphereInput x y))
      (localCoordinateDerivativeEquiv (signSphereInput x y)
        (signSphereInput_hits_target x y)).toContinuousLinearMap
      (signSourceParameterEquiv x y 0) := by
    rw [map_zero]
    exact hD
  have hC := hD'.comp 0 hP
  let T := targetCoordinateTransport (signSphereInput x y) (signSphereInput_hits_target x y)
  exact T.toContinuousLinearMap.hasFDerivAt.comp 0 hC

theorem signCoordinateDerivativeEquiv_apply (x y : Bool) (p : ParameterSpace rotatedInput) :
    signCoordinateDerivativeEquiv x y p = fderiv ℝ (signCoordinateMap x y) 0 p := by
  rw [(hasFDerivAt_signCoordinateDerivativeEquiv x y).fderiv]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
