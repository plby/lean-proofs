import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusCoordinates
import Wikipedia.HopfProblem.CuspHoneycombTiling

/-!
# The actual compact hexagon presentation of the marked base torus

The base map is the existing inverse-quarter-turn coordinate modulo the
integer lattice. The literal closed dual hexagon surjects onto this
torus, and its fibres are exactly integral translations. Compactness
proves that the inherited torus topology is the quotient topology.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open ToricSpace CuspHoneycombTiling PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane
local notation "Lattice" => CuspHoneycombTiling.Lattice

abbrev BaseTorus := ProductTorus 2

abbrev basePoint := baseTorusPoint

/-- The underlying integral lattice is unchanged by the unimodular
quarter-turn used for the marked base coordinates. -/
theorem basePoint_eq_iff (y z : Plane) :
    basePoint y = basePoint z ↔ ∃ v : Lattice, y = z + latticePoint v := by
  rw [baseTorusPoint_eq_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨cuspVector v, hv⟩
  · rintro ⟨v, hv⟩
    refine ⟨-cuspVector v, ?_⟩
    simpa only [cuspVector_neg, cuspVector_cuspVector, neg_neg] using hv

theorem basePoint_add_latticePoint (v : Lattice) (y : Plane) :
    basePoint (y + latticePoint v) = basePoint y :=
  (basePoint_eq_iff _ _).mpr ⟨v, rfl⟩

theorem basePoint_sub_latticePoint (v : Lattice) (y : Plane) :
    basePoint (y - latticePoint v) = basePoint y := by
  simpa only [latticePoint_neg, sub_eq_add_neg] using
    basePoint_add_latticePoint (-v) y

/-- Restriction of the actual marked base map to the compact fundamental
hexagon; no quotient topology is assigned to a replacement space. -/
def cellMap : C(baseCell, BaseTorus) :=
  ⟨fun y => basePoint (y : Plane), baseTorusPoint_continuous.comp continuous_subtype_val⟩

@[simp] theorem cellMap_apply (y : baseCell) :
    cellMap y = baseTorusPoint (y : Plane) := rfl

theorem cellMap_continuous : Continuous cellMap := cellMap.continuous

/-- Every marked torus point has an actual representative in the
literal closed dual hexagon, using its proved floor-based tiling. -/
theorem cellMap_surjective : Function.Surjective cellMap := by
  intro q
  obtain ⟨y, hy⟩ := baseTorusPoint_surjective q
  exact ⟨⟨y - latticePoint (floorCenter y), mem_cell_floorCenter y⟩,
    (basePoint_sub_latticePoint (floorCenter y) y).trans hy⟩

/-- The fibres are exactly the genuine integral lattice identifications,
including the opposite-edge and vertex identifications. -/
theorem cellMap_eq_iff (y z : baseCell) :
    cellMap y = cellMap z ↔ ∃ v : Lattice, (y : Plane) = (z : Plane) + latticePoint v :=
  basePoint_eq_iff y z

theorem cellMap_eq_iff_deck (y z : baseCell) :
    cellMap y = cellMap z ↔
      ∃ v : Lattice, (y : Plane) = (z : Plane) + latticePoint (cuspVector v) :=
  baseTorusPoint_eq_iff y z

theorem cellMap_isProperMap : IsProperMap cellMap := by
  let : CompactSpace baseCell := isCompact_iff_compactSpace.mp baseCell_isCompact
  exact cellMap.continuous.isProperMap

theorem cellMap_isClosedMap : IsClosedMap cellMap :=
  cellMap_isProperMap.isClosedMap

theorem cellMap_isQuotientMap : IsQuotientMap cellMap :=
  cellMap_isClosedMap.isQuotientMap cellMap.continuous cellMap_surjective

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover
