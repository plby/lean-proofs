import Wikipedia.HopfProblem.DegreeCollapseTopCellLifting
import Wikipedia.HopfProblem.DegreeCollapseThreefoldFiniteCells

/-!
# A genuine right homotopy inverse of the original sphere map

Exact relative lifting is discharged in all dimensions through six, and the
original threefold has a proved finite homotopy cell construction in those
dimensions. Lifting its identity gives an actual continuous reverse map and
an actual homotopy. The other composite is treated separately.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse

open SixSphereCube SpecialPeriods.Threefold

/-- The original sphere map has an actual right homotopy inverse, without a lifting premise. -/
theorem exists_right_homotopy_inverse (x : Space) :
    ∃ g : C(Space, StandardSphere),
      ((SphereHomologyEquivalence.sphereMap x).comp g).Homotopic (ContinuousMap.id Space) :=
  FiniteCells.mapsLift_of_built (SphereHomologyEquivalence.sphereMap x)
    (TopCellLifting.sphereMap_relativeDiskLifting_six x)
    Threefold.finite_homotopy_cells (ContinuousMap.id Space)

end Wikipedia.HopfProblem.DegreeCollapse
