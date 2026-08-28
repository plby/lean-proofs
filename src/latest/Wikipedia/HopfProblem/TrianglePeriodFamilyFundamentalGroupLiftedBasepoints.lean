import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupHalfPlane
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupSemicircles
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansBoundary

/-!
# Canonical actual lifts of the three real semicircle endpoints

All three points are the inverse images of explicit real coordinates
under the constructed half-triangle normalization. The proved boundary
ordering identifies the reflection fixing each endpoint. In particular,
the common point lies on the circular side, not at an elliptic vertex.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping

def halfPlaneMeridianBasepoint : RegularHalfPlane :=
  realHalfPlaneValue (1 / 2) (by norm_num) (by norm_num)

def halfPlaneMeridianLeftPoint : RegularHalfPlane :=
  realHalfPlaneValue (-1 / 2) (by norm_num) (by norm_num)

def halfPlaneMeridianRightPoint : RegularHalfPlane :=
  realHalfPlaneValue (3 / 2) (by norm_num) (by norm_num)

@[simp] theorem halfPlaneValue_basepoint :
    halfPlaneValue halfPlaneMeridianBasepoint = meridianBasepoint := by
  apply Subtype.ext
  norm_num [halfPlaneValue, halfPlaneMeridianBasepoint, realHalfPlaneValue, meridianBasepoint]

@[simp] theorem halfPlaneValue_leftPoint :
    halfPlaneValue halfPlaneMeridianLeftPoint = meridianLeftPoint := by
  apply Subtype.ext
  norm_num [halfPlaneValue, halfPlaneMeridianLeftPoint, realHalfPlaneValue, meridianLeftPoint]

@[simp] theorem halfPlaneValue_rightPoint :
    halfPlaneValue halfPlaneMeridianRightPoint = meridianRightPoint := by
  apply Subtype.ext
  norm_num [halfPlaneValue, halfPlaneMeridianRightPoint, realHalfPlaneValue, meridianRightPoint]

/-- The canonical regular upper-half-plane lift of normalized coordinate `1/2`. -/
def normalizedRegularMeridianBasepoint : TriangleRegularPoint :=
  halfPlaneLift halfPlaneMeridianBasepoint

def normalizedRegularMeridianLeftPoint : TriangleRegularPoint :=
  halfPlaneLift halfPlaneMeridianLeftPoint

def normalizedRegularMeridianRightPoint : TriangleRegularPoint :=
  halfPlaneLift halfPlaneMeridianRightPoint

@[simp] theorem normalizedRegularMeridianBasepoint_coe :
    (normalizedRegularMeridianBasepoint : ℍ) = (halfFordRealPreimage (1 / 2) : ℍ) := rfl

@[simp] theorem normalizedRegularMeridianLeftPoint_coe :
    (normalizedRegularMeridianLeftPoint : ℍ) = (halfFordRealPreimage (-1 / 2) : ℍ) := rfl

@[simp] theorem normalizedRegularMeridianRightPoint_coe :
    (normalizedRegularMeridianRightPoint : ℍ) = (halfFordRealPreimage (3 / 2) : ℍ) := rfl

@[simp] theorem normalizedRegularMeridianBasepoint_coordinate :
    triangleRegularPlaneHomeomorph (triangleRegularProject normalizedRegularMeridianBasepoint) =
      meridianBasepoint := by
  rw [normalizedRegularMeridianBasepoint, halfPlaneLift_projection, halfPlaneValue_basepoint]

@[simp] theorem normalizedRegularMeridianBasepoint_project :
    triangleRegularProject normalizedRegularMeridianBasepoint =
      triangleRegularMeridianBasepoint := by
  apply triangleRegularPlaneHomeomorph.injective
  rw [normalizedRegularMeridianBasepoint_coordinate, triangleRegularMeridianBasepoint_coordinate]

@[simp] theorem normalizedRegularMeridianLeftPoint_coordinate :
    triangleRegularPlaneHomeomorph (triangleRegularProject normalizedRegularMeridianLeftPoint) =
      meridianLeftPoint := by
  rw [normalizedRegularMeridianLeftPoint, halfPlaneLift_projection, halfPlaneValue_leftPoint]

@[simp] theorem normalizedRegularMeridianRightPoint_coordinate :
    triangleRegularPlaneHomeomorph (triangleRegularProject normalizedRegularMeridianRightPoint) =
      meridianRightPoint := by
  rw [normalizedRegularMeridianRightPoint, halfPlaneLift_projection, halfPlaneValue_rightPoint]

/-- The common endpoint is on the actual circular side. -/
theorem normalizedRegularMeridianBasepoint_circleReflection :
    circleReflection (normalizedRegularMeridianBasepoint : ℍ) =
      (normalizedRegularMeridianBasepoint : ℍ) :=
  halfFordRealPreimage_circleReflection (1 / 2) (by norm_num)

/-- The left real endpoint is on the actual right vertical side. -/
theorem normalizedRegularMeridianLeftPoint_rightReflection :
    rightReflection (normalizedRegularMeridianLeftPoint : ℍ) =
      (normalizedRegularMeridianLeftPoint : ℍ) :=
  halfFordRealPreimage_rightReflection (-1 / 2) (by norm_num)

/-- The right real endpoint is on the actual left vertical side. -/
theorem normalizedRegularMeridianRightPoint_leftReflection :
    leftReflection (normalizedRegularMeridianRightPoint : ℍ) =
      (normalizedRegularMeridianRightPoint : ℍ) :=
  halfFordRealPreimage_leftReflection (3 / 2) (by norm_num)

@[simp] theorem reflectedHalfPlaneLift_basepoint :
    reflectedHalfPlaneLift halfPlaneMeridianBasepoint = normalizedRegularMeridianBasepoint := by
  apply Subtype.ext
  exact normalizedRegularMeridianBasepoint_circleReflection

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
