import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupSemicircleLifts
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansCore

/-!
# The actual jointly marked meridian lifts

Concatenate the reflected semicircle with the appropriate translated
return semicircle. Both resulting paths start at the same canonical
regular point and end at the inverse first or second triangle generator.
Their projections are exactly the previously proved free planar basis.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle

private theorem trans_coordinate {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {a b c : X} {x y z : Y} (f : X → Y)
    (p : Path a b) (q : Path b c) (α : Path x y) (β : Path y z)
    (hp : ∀ t : unitInterval, f (p t) = α t)
    (hq : ∀ t : unitInterval, f (q t) = β t) (t : unitInterval) :
    f ((p.trans q) t) = (α.trans β) t := by
  simp only [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

/-- The full first meridian lift, ending at the inverse first generator. -/
def liftedMeridianZero :
    Path normalizedRegularMeridianBasepoint
      (triangleGenerator₁⁻¹ • normalizedRegularMeridianBasepoint) :=
  reflectedZeroHalfPath.trans
    (liftedZeroHalfPath.symm.map (continuous_const_smul triangleGenerator₁⁻¹))

/-- The full second meridian lift, ending at the inverse second generator. -/
def liftedMeridianOne :
    Path normalizedRegularMeridianBasepoint
      (triangleGenerator₂⁻¹ • normalizedRegularMeridianBasepoint) :=
  liftedOneHalfPath.trans
    ((reflectedOneHalfPath.symm.map (continuous_const_smul triangleGenerator₂⁻¹)).cast
      (inv_smul_smul triangleGenerator₂ normalizedRegularMeridianRightPoint).symm rfl)

theorem liftedMeridianZero_coordinate (t : unitInterval) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (liftedMeridianZero t)) =
      compatiblePlanarMeridian false t := by
  change triangleRegularPlaneHomeomorph
    (triangleRegularProject ((reflectedZeroHalfPath.trans
      (liftedZeroHalfPath.symm.map (continuous_const_smul triangleGenerator₁⁻¹))) t)) =
        (oppositeZeroPath.trans zeroHalfPath.symm) t
  apply trans_coordinate (fun z => triangleRegularPlaneHomeomorph (triangleRegularProject z))
  · exact reflectedZeroHalfPath_coordinate
  · intro s
    change triangleRegularPlaneHomeomorph
      (triangleRegularProject (triangleGenerator₁⁻¹ •
        liftedZeroHalfPath (unitInterval.symm s))) = zeroHalfPath (unitInterval.symm s)
    rw [triangleRegularProject_covering.map_smul]
    exact liftedZeroHalfPath_coordinate _

theorem liftedMeridianOne_coordinate (t : unitInterval) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (liftedMeridianOne t)) =
      compatiblePlanarMeridian true t := by
  change triangleRegularPlaneHomeomorph
    (triangleRegularProject ((liftedOneHalfPath.trans
      ((reflectedOneHalfPath.symm.map (continuous_const_smul triangleGenerator₂⁻¹)).cast
        (inv_smul_smul triangleGenerator₂ normalizedRegularMeridianRightPoint).symm rfl)) t)) =
      (oneHalfPath.trans oppositeOnePath.symm) t
  apply trans_coordinate (fun z => triangleRegularPlaneHomeomorph (triangleRegularProject z))
  · exact liftedOneHalfPath_coordinate
  · intro s
    change triangleRegularPlaneHomeomorph
      (triangleRegularProject (triangleGenerator₂⁻¹ •
        reflectedOneHalfPath (unitInterval.symm s))) = oppositeOnePath (unitInterval.symm s)
    rw [triangleRegularProject_covering.map_smul]
    exact reflectedOneHalfPath_coordinate _

def compatibleMeridianGenerator : Bool → TriangleGroup
  | false => triangleGenerator₁
  | true => triangleGenerator₂

/-- A single dependent family of the two actual constructed lifts. -/
def compatibleMeridianLift (b : Bool) :
    Path normalizedRegularMeridianBasepoint
      ((compatibleMeridianGenerator b)⁻¹ • normalizedRegularMeridianBasepoint) :=
  match b with
  | false => liftedMeridianZero
  | true => liftedMeridianOne

theorem compatibleMeridianLift_coordinate (b : Bool) (t : unitInterval) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (compatibleMeridianLift b t)) =
      compatiblePlanarMeridian b t := by
  cases b
  · exact liftedMeridianZero_coordinate t
  · exact liftedMeridianOne_coordinate t

/-- The actual projected loops share the canonical source basepoint. -/
def compatibleRegularMeridian (b : Bool) :
    Path (triangleRegularProject normalizedRegularMeridianBasepoint)
      (triangleRegularProject normalizedRegularMeridianBasepoint) :=
  projectLift normalizedRegularMeridianBasepoint (compatibleMeridianGenerator b)
    (compatibleMeridianLift b)

@[simp] theorem compatibleRegularMeridian_coordinate (b : Bool) (t : unitInterval) :
    triangleRegularPlaneHomeomorph (compatibleRegularMeridian b t) =
      compatiblePlanarMeridian b t :=
  compatibleMeridianLift_coordinate b t

/-- Unique path lifting verifies the whole chosen lift. -/
theorem compatibleRegularMeridian_liftPath (b : Bool) :
    triangleRegularProject_covering.isCoveringMap.liftPath (compatibleRegularMeridian b)
      normalizedRegularMeridianBasepoint (compatibleRegularMeridian b).source =
        (compatibleMeridianLift b).toContinuousMap :=
  projectLift_liftPath _ _ _

/-- The endpoint is a consequence of the constructed lift, not an extra
hypothesis on a separately chosen loop. -/
theorem compatibleRegularMeridian_monodromy (b : Bool) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (compatibleRegularMeridian b))
        ⟨normalizedRegularMeridianBasepoint, rfl⟩ : TriangleRegularPoint) =
      (compatibleMeridianGenerator b)⁻¹ • normalizedRegularMeridianBasepoint :=
  congrArg Subtype.val (projectLift_monodromy _ _ _)

/-- The genuine fundamental-group classes of the two constructed loops. -/
def compatibleRegularMeridianClass (b : Bool) :
    FundamentalGroup TriangleRegularQuotient
      (triangleRegularProject normalizedRegularMeridianBasepoint) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (compatibleRegularMeridian b))

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
