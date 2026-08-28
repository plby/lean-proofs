import Wikipedia.SmoothSixDPoincare.SuspensionReflection
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionMayerVietoris

/-!
# Reflection acts by minus one on positive suspension homology

The middle-band projection is unchanged by reflection. The genuine
Mayer–Vietoris connecting map is injective and changes sign when reflection
interchanges the two cone charts. Together these compute the actual induced
homology map, including degree one.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.SuspensionReflection

open Wikipedia.HopfProblem.CuspCentralHomology
  Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X]

theorem middle_homology (k : ℕ) (a : SingularHomology (Suspension.middleBand X) k) :
    singularHomologyMap middleMap k a = a := by
  apply (homotopyEquivHomologyEquiv Suspension.middleBandHomotopyEquiv k).injective
  change singularHomologyMap Suspension.middleBandHomotopyEquiv.toFun k
      (singularHomologyMap middleMap k a) =
    singularHomologyMap Suspension.middleBandHomotopyEquiv.toFun k a
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, middle_projection_comp]

/-- Actual height reflection induces negation on every positive homology group. -/
theorem reflect_homology [Nonempty X] (n : ℕ)
    (a : SingularHomology (Suspension X) (n + 1)) :
    singularHomologyMap reflect (n + 1) a = -a := by
  apply contractibleCoverConnecting_injective Suspension.northOpen Suspension.southOpen
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover n
  rw [CoverNaturality.connecting_reversing_naturality
    Suspension.northOpen Suspension.southOpen Suspension.northOpen Suspension.southOpen
    reflect reflect_north reflect_south
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover n a]
  change -singularHomologyMap middleMap n
    (connectingHomomorphism _ _ _ _ _ n a) = _
  rw [middle_homology, map_neg]

end Wikipedia.SmoothSixDPoincare.SuspensionReflection
