import Wikipedia.HomotopyGroupsOfSpheres.SphereThree
import Wikipedia.HopfProblem.FourthHurewiczIso
import Wikipedia.HopfProblem.FifthHurewiczIso

/-! # The native fifth homotopy group of the parameter five-sphere -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem HopfProblem.SphereHomology

instance sphereFive_piTwo_subsingleton (x : Sphere 5) : Subsingleton (π_ 2 (Sphere 5) x) :=
  unitSphere_piTwo_subsingleton 2 x

instance sphereFive_piThree_subsingleton (x : Sphere 5) : Subsingleton (π_ 3 (Sphere 5) x) := by
  let := unitSphere_homology_subsingleton 4 3 (by decide) (by decide)
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

instance sphereFive_piFour_subsingleton (x : Sphere 5) : Subsingleton (π_ 4 (Sphere 5) x) := by
  let := unitSphere_homology_subsingleton 4 4 (by decide) (by decide)
  exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton

@[irreducible] def pi5_sphere_five_mulEquiv (x : Sphere 5) :
    π_ 5 (Sphere 5) x ≃* Multiplicative ℤ :=
  (FifthHurewicz.hurewiczPi5Equiv x).trans
    (unitSphereHomologyTopEquiv 4).toAddEquiv.toMultiplicative

end Wikipedia.HomotopyGroupsOfSpheres
