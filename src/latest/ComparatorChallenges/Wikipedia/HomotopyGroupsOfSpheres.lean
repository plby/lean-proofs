import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Data.ZMod.Basic

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

/-- The Euclidean unit sphere with its subspace topology. -/
abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The first homotopy group of the circle is infinite cyclic. -/
theorem pi1_sphere_one (x : Sphere 1) :
    Nonempty (π_ 1 (Sphere 1) x ≃* Multiplicative ℤ) := by
  sorry

/-- The second homotopy group of the circle is trivial. -/
theorem pi2_sphere_one (x : Sphere 1) : Nonempty (π_ 2 (Sphere 1) x ≃* PUnit) := by
  sorry

/-- The fundamental group of the two-sphere is trivial. -/
theorem pi1_sphere_two (x : Sphere 2) : Nonempty (π_ 1 (Sphere 2) x ≃* PUnit) := by
  sorry

/-- The second homotopy group of the two-sphere is infinite cyclic. -/
theorem pi2_sphere_two (x : Sphere 2) :
    Nonempty (π_ 2 (Sphere 2) x ≃* Multiplicative ℤ) := by
  sorry

/-- The third homotopy group of the two-sphere is infinite cyclic. -/
theorem pi3_sphere_two (x : Sphere 2) :
    Nonempty (π_ 3 (Sphere 2) x ≃* Multiplicative ℤ) := by
  sorry

/-- The sixth homotopy group of the two-sphere is cyclic of order twelve. -/
theorem pi6_sphere_two (x : Sphere 2) :
    Nonempty (π_ 6 (Sphere 2) x ≃* Multiplicative (ZMod 12)) := by
  sorry

/-- The third homotopy group of the three-sphere is infinite cyclic. -/
theorem pi3_sphere_three (x : Sphere 3) :
    Nonempty (π_ 3 (Sphere 3) x ≃* Multiplicative ℤ) := by
  sorry

/-- The sixth homotopy group of the three-sphere is cyclic of order twelve. -/
theorem pi6_sphere_three (x : Sphere 3) :
    Nonempty (π_ 6 (Sphere 3) x ≃* Multiplicative (ZMod 12)) := by
  sorry

/-- The seventh homotopy group of the seven-sphere is infinite cyclic. -/
theorem pi7_sphere_seven (x : Sphere 7) :
    Nonempty (π_ 7 (Sphere 7) x ≃* Multiplicative ℤ) := by
  sorry

end Wikipedia.HomotopyGroupsOfSpheres
