import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRadius
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMeridianLifts

/-!
# Actual covering monodromy of the small-radius meridians

The explicit based radial homotopy is transported through the actual
regular-quotient coordinate homeomorphism.  It identifies the resulting
quotient loop with the already constructed meridian, as actual homotopic
paths.  Covering monodromy therefore has the proved inverse-generator
endpoint for every positive radius at most one half.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryRadius

open SpecialPeriods SpecialPeriods.Triangle Meridians

/-- The actual small-radius loop in the regular quotient, with its canonical starting point. -/
def regularRadiusMeridian (b : Bool) (r : SmallRadius) :
    Path (triangleRegularProject normalizedRegularMeridianBasepoint)
      (triangleRegularProject normalizedRegularMeridianBasepoint) :=
  ((compatibleRadiusMeridian b r).map triangleRegularPlaneHomeomorph.symm.continuous).cast
    normalizedRegularMeridianBasepoint_project normalizedRegularMeridianBasepoint_project

@[simp] theorem regularRadiusMeridian_apply (b : Bool) (r : SmallRadius) (t : unitInterval) :
    regularRadiusMeridian b r t =
      triangleRegularPlaneHomeomorph.symm (compatibleRadiusMeridian b r t) := rfl

/-- Its normalized coordinate is the literal based small-radius meridian. -/
@[simp] theorem regularRadiusMeridian_coordinate (b : Bool) (r : SmallRadius)
    (t : unitInterval) :
    triangleRegularPlaneHomeomorph (regularRadiusMeridian b r t) =
      compatibleRadiusMeridian b r t :=
  triangleRegularPlaneHomeomorph.apply_symm_apply _

private theorem compatibleRegularMeridian_eq_pullback (b : Bool) :
    ((compatiblePlanarMeridian b).map triangleRegularPlaneHomeomorph.symm.continuous).cast
        normalizedRegularMeridianBasepoint_project normalizedRegularMeridianBasepoint_project =
      compatibleRegularMeridian b := by
  apply Path.ext
  funext t
  apply triangleRegularPlaneHomeomorph.injective
  change triangleRegularPlaneHomeomorph
    (triangleRegularPlaneHomeomorph.symm (compatiblePlanarMeridian b t)) =
      triangleRegularPlaneHomeomorph (compatibleRegularMeridian b t)
  rw [Homeomorph.apply_symm_apply, compatibleRegularMeridian_coordinate]

/-- The actual radial homotopy identifies the regular quotient loop with the marked meridian. -/
theorem regularRadiusMeridian_homotopic (b : Bool) (r : SmallRadius) :
    (regularRadiusMeridian b r).Homotopic (compatibleRegularMeridian b) := by
  let f : C(TwicePuncturedPlane, TriangleRegularQuotient) :=
    triangleRegularPlaneHomeomorph.symm
  have h := ((compatibleRadiusMeridian_homotopic b r).map
    f).pathCast
      normalizedRegularMeridianBasepoint_project normalizedRegularMeridianBasepoint_project
  rw [compatibleRegularMeridian_eq_pullback] at h
  exact h

/-- Equality of the genuine path-homotopy classes follows from the constructed homotopy. -/
theorem regularRadiusMeridian_class (b : Bool) (r : SmallRadius) :
    Path.Homotopic.Quotient.mk (regularRadiusMeridian b r) =
      Path.Homotopic.Quotient.mk (compatibleRegularMeridian b) :=
  Path.Homotopic.Quotient.eq.mpr (regularRadiusMeridian_homotopic b r)

/-- The canonical covering endpoint is the inverse actual triangle generator at every radius. -/
theorem regularRadiusMeridian_monodromy (b : Bool) (r : SmallRadius) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (regularRadiusMeridian b r))
        ⟨normalizedRegularMeridianBasepoint, rfl⟩ : TriangleRegularPoint) =
      (compatibleMeridianGenerator b)⁻¹ • normalizedRegularMeridianBasepoint := by
  rw [regularRadiusMeridian_class]
  exact compatibleRegularMeridian_monodromy b

/-- The canonical actual path lift has the same proved inverse-generator endpoint. -/
theorem regularRadiusMeridian_liftPath_apply_one (b : Bool) (r : SmallRadius) :
    triangleRegularProject_covering.isCoveringMap.liftPath (regularRadiusMeridian b r)
        normalizedRegularMeridianBasepoint (regularRadiusMeridian b r).source 1 =
      (compatibleMeridianGenerator b)⁻¹ • normalizedRegularMeridianBasepoint :=
  regularRadiusMeridian_monodromy b r

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryRadius
