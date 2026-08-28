import Wikipedia.HomotopyGroupsOfSpheres.SphereTwo
import Wikipedia.HopfProblem.ThirdHurewiczIso

/-! # The third homotopy group of the three-sphere, for the Hopf comparison -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

/-- The third Hurewicz isomorphism and the sphere's top integral homology. -/
def pi3_sphere_three_mulEquiv (x : Sphere 3) :
    π_ 3 (Sphere 3) x ≃* Multiplicative ℤ := by
  let := HopfProblem.SphereHomology.unitSphere_piTwo_subsingleton 0 x
  exact ((HopfProblem.ThirdHurewicz.hurewiczLinearEquiv x).trans
    (HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 2)).toAddEquiv.toMultiplicativeRight

end Wikipedia.HomotopyGroupsOfSpheres
