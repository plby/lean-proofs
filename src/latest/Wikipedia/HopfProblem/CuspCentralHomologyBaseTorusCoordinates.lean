import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelShear

/-!
# The marked base coordinate of the actual honeycomb plane

The base coordinate is the inverse quarter-turn of the honeycomb
coordinate, taken modulo the integral lattice.  A geometric deck
translation by `cuspVector v` therefore changes the lift by exactly `v`.
This shared coordinate map is independent of the phase and of the cusp
parameter, and is used both on the central fibre and on its base cover.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspHoneycombTiling PeriodTorusHigherHomology SpecializationModel

/-- The actual marked base point of a honeycomb coordinate. -/
def baseTorusPoint (y : CuspHoneycombTiling.Plane) : ProductTorus 2 :=
  coordinateProjection 2 (sourceBaseMarking y)

@[simp] theorem baseTorusPoint_apply (y : CuspHoneycombTiling.Plane) :
    baseTorusPoint y = coordinateProjection 2 (-realCuspVector y) := rfl

theorem baseTorusPoint_continuous : Continuous baseTorusPoint :=
  (coordinateProjection_continuous 2).comp sourceBaseMarking.continuous

theorem baseTorusPoint_surjective : Function.Surjective baseTorusPoint :=
  (coordinateProjection_surjective 2).comp sourceBaseMarking.surjective

/-- The marked coordinate is unchanged under every actual deck shift. -/
theorem baseTorusPoint_deck (v : Fin 2 → ℤ) (y : CuspHoneycombTiling.Plane) :
    baseTorusPoint (y + latticePoint (cuspVector v)) = baseTorusPoint y := by
  apply (sourceCoordinateProjection_eq_iff _ _).mpr
  exact ⟨v, sourceBaseMarking_deck v y⟩

@[simp] theorem baseTorusPoint_realCuspVector (y : CuspHoneycombTiling.Plane) :
    baseTorusPoint (realCuspVector y) = coordinateProjection 2 y := by
  change coordinateProjection 2 (sourceBaseMarking (sourceBaseMarking.symm y)) = _
  rw [Homeomorph.apply_symm_apply]

/-- Equality of marked base points is precisely the geometric deck
translation relation on the plane. -/
theorem baseTorusPoint_eq_iff (y z : CuspHoneycombTiling.Plane) :
    baseTorusPoint y = baseTorusPoint z ↔
      ∃ v : Fin 2 → ℤ, y = z + latticePoint (cuspVector v) := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (sourceCoordinateProjection_eq_iff _ _).mp h
    refine ⟨v, sourceBaseMarking.injective ?_⟩
    rw [sourceBaseMarking_deck]
    exact hv
  · rintro ⟨v, rfl⟩
    exact baseTorusPoint_deck v z

end Wikipedia.HopfProblem.CuspCentralHomology
