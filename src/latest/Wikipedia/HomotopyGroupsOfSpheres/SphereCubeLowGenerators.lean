import Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator
import Wikipedia.HomotopyGroupsOfSpheres.SphereFive
import Wikipedia.HomotopyGroupsOfSpheres.SphereSeven

/-! # Actual primitive quotient cubes in dimensions five and seven -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

theorem quotientClass_five_generates :
    Function.Surjective (fun k : ℤ ↦ quotientClass 5 ^ k) :=
  quotientClass_generates (pi5_sphere_five_mulEquiv (point 5))

theorem quotientClass_seven_generates :
    Function.Surjective (fun k : ℤ ↦ quotientClass 7 ^ k) :=
  quotientClass_generates (pi7_sphere_seven_mulEquiv (point 7))

theorem quotientClass_five_coordinate_natAbs :
    Int.natAbs (pi5_sphere_five_mulEquiv (point 5) (quotientClass 5)).toAdd = 1 :=
  quotientClass_coordinate_natAbs (pi5_sphere_five_mulEquiv (point 5))

theorem quotientClass_seven_coordinate_natAbs :
    Int.natAbs (pi7_sphere_seven_mulEquiv (point 7) (quotientClass 7)).toAdd = 1 :=
  quotientClass_coordinate_natAbs (pi7_sphere_seven_mulEquiv (point 7))

end Wikipedia.HomotopyGroupsOfSpheres.SphereCubeGenerator
