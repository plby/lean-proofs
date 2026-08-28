import Wikipedia.SmoothSixDPoincare.TubularBigonIntersectionSigns
import Wikipedia.HopfProblem.OrbitPairMixedChartDeterminant

/-!
# Fixed coordinate identifications for the immersed corner comparison

Use one source ordering and one ambient identification at both corners.
The upper branch is first, matching the actual tubular bigon Jacobian.
The coordinate factor is nonzero and fixed, so it cannot change the
relative corner sign.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner

open Wikipedia.SmoothSixDPoincare WhitneyPairModel FrameField
open OrbitPair.MixedChartDeterminant

abbrev NormalSpace := (ℝ × ℝ) × EuclideanSpace ℝ (Fin 4)

def normalCoordinates : Space ≃L[ℝ] NormalSpace :=
  (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)).prodCongr normalPairCoordinates

variable {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (J : Sheet ≃L[ℝ] G) (K : (G × G) ≃L[ℝ] E)

def sourceCoordinates : (G × G) ≃L[ℝ] Space :=
  (J.symm.prodCongr J.symm).trans (ContinuousLinearEquiv.prodProdProdComm ℝ ℝ Plane ℝ Plane)

def targetCoordinates : Space ≃L[ℝ] E := (sourceCoordinates J).symm.trans K

def tubeCoordinates : E ≃L[ℝ] NormalSpace := (targetCoordinates J K).symm.trans normalCoordinates

def coordinateScale : ℝ :=
  (fixedCoordinates K (sourceCoordinates J) (targetCoordinates J K)).toContinuousLinearMap.det

theorem coordinateScale_ne_zero : coordinateScale J K ≠ 0 :=
  fixedCoordinates_det_ne_zero K (sourceCoordinates J) (targetCoordinates J K)

theorem tube_target_coordinates (z : Space) :
    tubeCoordinates J K (targetCoordinates J K z) = normalCoordinates z := by
  change normalCoordinates ((targetCoordinates J K).symm (targetCoordinates J K z)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem normal_jointBlock_source
    (P Q : Sheet →L[ℝ] NormalSpace) (u v : G) :
    normalCoordinates (IntersectionCoordinates.jointBlock normalPairCoordinates P Q
      (sourceCoordinates J (u, v))) = P (J.symm u) + Q (J.symm v) := by
  change ((P (J.symm u) + Q (J.symm v)).1,
    normalPairCoordinates (normalPairCoordinates.symm (P (J.symm u) + Q (J.symm v)).2)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner
