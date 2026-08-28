import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySlitLifts
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMeridianLifts

/-!
# Slit sections along actual meridian lifts

The canonical meridian starting point gives a specified lift of the slit
basepoint.  Covering uniqueness on the connected unit interval identifies
each slit section with every actual path whose projection stays in that
slit and which starts at the specified lift.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SpecialPeriods.Triangle

/-- The actual meridian basepoint as a lift of the common slit basepoint. -/
def normalizedSlitBaseLift : SlitBaseLift :=
  ⟨Meridians.normalizedRegularMeridianBasepoint, by
    change triangleRegularProject Meridians.normalizedRegularMeridianBasepoint = slitBasepoint
    apply triangleRegularPlaneHomeomorph.injective
    rw [Meridians.normalizedRegularMeridianBasepoint_coordinate, slitBasepoint_coordinate]⟩

@[simp] theorem normalizedSlitBaseLift_val :
    normalizedSlitBaseLift.val = Meridians.normalizedRegularMeridianBasepoint := rfl

@[simp] theorem normalizedSlitBaseLift_project :
    triangleRegularProject normalizedSlitBaseLift.val = slitBasepoint :=
  normalizedSlitBaseLift.property

/-- The upper section agrees with every actual path lift that remains over its slit. -/
theorem upperLift_path (b : SlitBaseLift) {z : TriangleRegularPoint} (p : Path b.val z)
    (hp : ∀ t, triangleRegularProject (p t) ∈ upperBase) (t : unitInterval) :
    upperLift b ⟨triangleRegularProject (p t), hp t⟩ = p t := by
  let q : C(unitInterval, upperBase) :=
    ⟨fun s => ⟨triangleRegularProject (p s), hp s⟩,
      (triangleRegularProject_covering.continuous.comp p.continuous).subtype_mk hp⟩
  have hq : q 0 = upperBasePoint := by
    apply Subtype.ext
    change triangleRegularProject (p 0) = slitBasepoint
    rw [p.source]
    exact b.property
  have h : (fun s => upperLift b (q s)) = (p : unitInterval → TriangleRegularPoint) := by
    refine triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
      ((upperLift b).continuous.comp q.continuous) p.continuous ?_ (0 : unitInterval) ?_
    · funext s
      exact upperLift_project b (q s)
    · rw [hq, upperLift_basepoint, p.source]
  exact congrFun h t

/-- The lower section agrees with every actual path lift that remains over its slit. -/
theorem lowerLift_path (b : SlitBaseLift) {z : TriangleRegularPoint} (p : Path b.val z)
    (hp : ∀ t, triangleRegularProject (p t) ∈ lowerBase) (t : unitInterval) :
    lowerLift b ⟨triangleRegularProject (p t), hp t⟩ = p t := by
  let q : C(unitInterval, lowerBase) :=
    ⟨fun s => ⟨triangleRegularProject (p s), hp s⟩,
      (triangleRegularProject_covering.continuous.comp p.continuous).subtype_mk hp⟩
  have hq : q 0 = lowerBasePoint := by
    apply Subtype.ext
    change triangleRegularProject (p 0) = slitBasepoint
    rw [p.source]
    exact b.property
  have h : (fun s => lowerLift b (q s)) = (p : unitInterval → TriangleRegularPoint) := by
    refine triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
      ((lowerLift b).continuous.comp q.continuous) p.continuous ?_ (0 : unitInterval) ?_
    · funext s
      exact lowerLift_project b (q s)
    · rw [hq, lowerLift_basepoint, p.source]
  exact congrFun h t

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
