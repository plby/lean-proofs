import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundarySquareLift
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridians

/-!
# Actual elliptic attaching-square deck frames

Lift the previously constructed native-chart-to-meridian square, starting
with its literal elliptic root path.  The final basepoint defines an actual
triangle deck frame.  Comparing the full final lifted path with the fixed
meridian lift determines the conjugation equation for that same frame.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Meridians
open SpecialPeriods.EllipticAttachingMeridians
open SpecialPeriods.Threefold.EllipticGeometry

/-- Projection of the previously constructed complete compatible meridian lift. -/
theorem compatibleLift_projection (b : Bool) (t : unitInterval) :
    triangleRegularProject (compatibleMeridianLift b t) = compatibleRegularMeridian b t := by
  apply triangleRegularPlaneHomeomorph.injective
  exact (compatibleMeridianLift_coordinate b t).trans
    (compatibleRegularMeridian_coordinate b t).symm

/-- The actual endpoint transformation of the fixed clockwise meridian. -/
def clockwiseLiftEndpoint (b : Bool) : TriangleGroup :=
  if normalizationReversesMeridians then (compatibleMeridianGenerator b)⁻¹
  else compatibleMeridianGenerator b

/-- The original compatible lift, or its genuinely translated reversed path. -/
def clockwiseFinalLift (b : Bool) : C(unitInterval, TriangleRegularPoint) :=
  if normalizationReversesMeridians then (compatibleMeridianLift b).toContinuousMap
  else ((compatibleMeridianLift b).symm.map
    (continuous_const_smul (compatibleMeridianGenerator b))).toContinuousMap

@[simp] theorem clockwiseFinalLift_zero (b : Bool) :
    clockwiseFinalLift b 0 = normalizedRegularMeridianBasepoint := by
  by_cases h : normalizationReversesMeridians = true
  · rw [clockwiseFinalLift, if_pos h]
    exact (compatibleMeridianLift b).source
  · rw [clockwiseFinalLift, if_neg h]
    exact (((compatibleMeridianLift b).symm.map
      (continuous_const_smul (compatibleMeridianGenerator b))).source).trans
        (smul_inv_smul (compatibleMeridianGenerator b) normalizedRegularMeridianBasepoint)

theorem clockwiseFinalLift_one (b : Bool) :
    clockwiseFinalLift b 1 = clockwiseLiftEndpoint b • clockwiseFinalLift b 0 := by
  rw [clockwiseFinalLift_zero]
  by_cases h : normalizationReversesMeridians = true
  · rw [clockwiseFinalLift, clockwiseLiftEndpoint, if_pos h, if_pos h]
    exact (compatibleMeridianLift b).target
  · rw [clockwiseFinalLift, clockwiseLiftEndpoint, if_neg h, if_neg h]
    exact ((compatibleMeridianLift b).symm.map
      (continuous_const_smul (compatibleMeridianGenerator b))).target

/-- This is the entire actual clockwise path lift, not just an endpoint formula. -/
theorem clockwiseFinalLift_projection (b : Bool) (t : unitInterval) :
    triangleRegularProject (clockwiseFinalLift b t) = clockwiseRegularMeridian b t := by
  by_cases h : normalizationReversesMeridians = true
  · rw [clockwiseFinalLift, clockwiseRegularMeridian, if_pos h, if_pos h]
    exact compatibleLift_projection b t
  · rw [clockwiseFinalLift, clockwiseRegularMeridian, if_neg h, if_neg h]
    change triangleRegularProject
      (compatibleMeridianGenerator b • compatibleMeridianLift b (unitInterval.symm t)) = _
    rw [triangleRegularProject_covering.map_smul]
    exact compatibleLift_projection b (unitInterval.symm t)

/-- The literal upstairs root path for the already selected sufficiently small native loop. -/
def chosenNativeLift (j : Elliptic.Kind) : C(unitInterval, TriangleRegularPoint) :=
  ⟨attachingUpstairsPoint j (chosenAttachingParameter j) (chosenAttachingParameter_im_pos j),
    attachingUpstairsPoint_continuous j _ _⟩

@[simp] theorem chosenNativeLift_projection (j : Elliptic.Kind) (t : unitInterval) :
    triangleRegularProject (chosenNativeLift j t) = chosenAttachingBaseLoop j t := rfl

/-- The endpoint follows from the actual local root rotation. -/
theorem chosenNativeLift_one (j : Elliptic.Kind) :
    chosenNativeLift j 1 = ellipticGenerator j • chosenNativeLift j 0 :=
  attachingUpstairsPoint_one j _ _

/-- The genuine covering lift of the previously proved native attaching square. -/
def chosenNativeSquareLift (j : Elliptic.Kind) :
    C(unitInterval × unitInterval, TriangleRegularPoint) :=
  loopSquareLift (chosenAttachingSquare j) (chosenNativeLift j) (chosenNativeLift_projection j)

/-- The final basepoint determines a deck frame over the fixed canonical point. -/
def nativeTailFrame (j : Elliptic.Kind) : TriangleGroup :=
  (loopSquareLift_exists_frame (chosenAttachingSquare j) (chosenNativeLift j)
    (chosenNativeLift_projection j) normalizedRegularMeridianBasepoint rfl).choose

/-- The frame is tied to the actual endpoint of the actual lifted square. -/
theorem nativeTailFrame_apply (j : Elliptic.Kind) :
    chosenNativeSquareLift j (1, 0) = nativeTailFrame j • normalizedRegularMeridianBasepoint :=
  (loopSquareLift_exists_frame (chosenAttachingSquare j) (chosenNativeLift j)
    (chosenNativeLift_projection j) normalizedRegularMeridianBasepoint rfl).choose_spec

/-- The full final edge is the fixed clockwise lift in that same actual frame. -/
theorem chosenNativeSquareLift_final (j : Elliptic.Kind) (t : unitInterval) :
    chosenNativeSquareLift j (1, t) =
      nativeTailFrame j • clockwiseFinalLift (attachingMeridianIndex j) t := by
  apply loopSquareLift_final_frame (chosenAttachingSquare j) (chosenNativeLift j)
    (chosenNativeLift_projection j) (clockwiseFinalLift (attachingMeridianIndex j))
    (clockwiseFinalLift_projection (attachingMeridianIndex j)) (nativeTailFrame j) _ t
  rw [clockwiseFinalLift_zero]
  exact nativeTailFrame_apply j

/-- The native root transformation and the fixed meridian endpoint obey
the conjugation equation forced by their actual lifted square. -/
theorem nativeTailFrame_relation (j : Elliptic.Kind) :
    ellipticGenerator j * nativeTailFrame j =
      nativeTailFrame j * clockwiseLiftEndpoint (attachingMeridianIndex j) := by
  apply loopSquareLift_frame_relation (chosenAttachingSquare j) (chosenNativeLift j)
    (chosenNativeLift_projection j) (ellipticGenerator j) (chosenNativeLift_one j)
    (clockwiseFinalLift (attachingMeridianIndex j))
    (clockwiseFinalLift_projection (attachingMeridianIndex j))
    (clockwiseLiftEndpoint (attachingMeridianIndex j))
    (clockwiseFinalLift_one (attachingMeridianIndex j)) (nativeTailFrame j)
  rw [clockwiseFinalLift_zero]
  exact nativeTailFrame_apply j

theorem nativeTailFrame_relation_if (j : Elliptic.Kind) :
    ellipticGenerator j * nativeTailFrame j = nativeTailFrame j *
      (if normalizationReversesMeridians then (ellipticGenerator j)⁻¹
        else ellipticGenerator j) := by
  have h := nativeTailFrame_relation j
  cases j <;> exact h

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
