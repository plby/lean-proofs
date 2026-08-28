import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupSideActions

/-!
# Actual lifts of the two semicircles and their conjugates

The chosen semicircles lie in the actual normalized half-plane. Applying
the inverse half-triangle map and its circular reflection gives genuine
continuous paths in the regular upper half-plane, with the exact
generator-translated endpoints proved from boundary geometry.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping

def halfPlaneZeroPath : Path halfPlaneMeridianBasepoint halfPlaneMeridianLeftPoint where
  toFun t := ⟨⟨(zeroHalfPath t : ℂ), zeroHalfPath_mem_halfPlane t⟩,
    (zeroHalfPath t).property⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp zeroHalfPath.continuous).subtype_mk _).subtype_mk _
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change (zeroHalfPath 0 : ℂ) = _
    rw [Path.source]
    norm_num [halfPlaneMeridianBasepoint, realHalfPlaneValue, meridianBasepoint]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change (zeroHalfPath 1 : ℂ) = _
    rw [Path.target]
    norm_num [halfPlaneMeridianLeftPoint, realHalfPlaneValue, meridianLeftPoint]

def halfPlaneOnePath : Path halfPlaneMeridianBasepoint halfPlaneMeridianRightPoint where
  toFun t := ⟨⟨(oneHalfPath t : ℂ), oneHalfPath_mem_halfPlane t⟩,
    (oneHalfPath t).property⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp oneHalfPath.continuous).subtype_mk _).subtype_mk _
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change (oneHalfPath 0 : ℂ) = _
    rw [Path.source]
    norm_num [halfPlaneMeridianBasepoint, realHalfPlaneValue, meridianBasepoint]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change (oneHalfPath 1 : ℂ) = _
    rw [Path.target]
    norm_num [halfPlaneMeridianRightPoint, realHalfPlaneValue, meridianRightPoint]

@[simp] theorem halfPlaneZeroPath_value (t : unitInterval) :
    halfPlaneValue (halfPlaneZeroPath t) = zeroHalfPath t := rfl

@[simp] theorem halfPlaneOnePath_value (t : unitInterval) :
    halfPlaneValue (halfPlaneOnePath t) = oneHalfPath t := rfl

@[simp] theorem halfPlaneZeroPath_conjugateValue (t : unitInterval) :
    halfPlaneConjugateValue (halfPlaneZeroPath t) = oppositeZeroPath t := by
  apply Subtype.ext
  exact (oppositeZeroPath_coe t).symm

@[simp] theorem halfPlaneOnePath_conjugateValue (t : unitInterval) :
    halfPlaneConjugateValue (halfPlaneOnePath t) = oppositeOnePath t := by
  apply Subtype.ext
  exact (oppositeOnePath_coe t).symm

/-- The zero half-circle lifted in the actual half-Ford triangle. -/
def liftedZeroHalfPath :
    Path normalizedRegularMeridianBasepoint normalizedRegularMeridianLeftPoint :=
  halfPlaneZeroPath.map halfPlaneLift_continuous

/-- The one half-circle lifted in the actual half-Ford triangle. -/
def liftedOneHalfPath :
    Path normalizedRegularMeridianBasepoint normalizedRegularMeridianRightPoint :=
  halfPlaneOnePath.map halfPlaneLift_continuous

/-- The opposite zero half-circle, with its proved inverse-generator endpoint. -/
def reflectedZeroHalfPath :
    Path normalizedRegularMeridianBasepoint
      (triangleGenerator₁⁻¹ • normalizedRegularMeridianLeftPoint) :=
  (halfPlaneZeroPath.map reflectedHalfPlaneLift_continuous).cast
    reflectedHalfPlaneLift_basepoint.symm reflectedHalfPlaneLift_leftPoint.symm

/-- The opposite one half-circle, with its proved generator endpoint. -/
def reflectedOneHalfPath :
    Path normalizedRegularMeridianBasepoint
      (triangleGenerator₂ • normalizedRegularMeridianRightPoint) :=
  (halfPlaneOnePath.map reflectedHalfPlaneLift_continuous).cast
    reflectedHalfPlaneLift_basepoint.symm reflectedHalfPlaneLift_rightPoint.symm

@[simp] theorem liftedZeroHalfPath_coordinate (t : unitInterval) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (liftedZeroHalfPath t)) =
      zeroHalfPath t :=
  halfPlaneLift_projection (halfPlaneZeroPath t)

@[simp] theorem liftedOneHalfPath_coordinate (t : unitInterval) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (liftedOneHalfPath t)) =
      oneHalfPath t :=
  halfPlaneLift_projection (halfPlaneOnePath t)

@[simp] theorem reflectedZeroHalfPath_coordinate (t : unitInterval) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (reflectedZeroHalfPath t)) =
      oppositeZeroPath t :=
  (reflectedHalfPlaneLift_projection (halfPlaneZeroPath t)).trans
    (halfPlaneZeroPath_conjugateValue t)

@[simp] theorem reflectedOneHalfPath_coordinate (t : unitInterval) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (reflectedOneHalfPath t)) =
      oppositeOnePath t :=
  (reflectedHalfPlaneLift_projection (halfPlaneOnePath t)).trans
    (halfPlaneOnePath_conjugateValue t)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
