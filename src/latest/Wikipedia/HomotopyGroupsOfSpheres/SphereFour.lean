import Wikipedia.HomotopyGroupsOfSpheres.SphereThree
import Wikipedia.HopfProblem.FourthHurewiczIso

/-! # The native fourth homotopy group of the balanced parameter four-sphere -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem HopfProblem.SphereHomology

instance sphereFour_piTwo_subsingleton (x : Sphere 4) : Subsingleton (π_ 2 (Sphere 4) x) :=
  unitSphere_piTwo_subsingleton 1 x

instance sphereFour_piThree_subsingleton (x : Sphere 4) : Subsingleton (π_ 3 (Sphere 4) x) := by
  let := unitSphere_homology_subsingleton 3 3 (by decide) (by decide)
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

@[irreducible] def pi4_sphere_four_mulEquiv (x : Sphere 4) :
    π_ 4 (Sphere 4) x ≃* Multiplicative ℤ :=
  (FourthHurewicz.hurewiczPi4Equiv x).trans
    (unitSphereHomologyTopEquiv 3).toAddEquiv.toMultiplicative

end Wikipedia.HomotopyGroupsOfSpheres
