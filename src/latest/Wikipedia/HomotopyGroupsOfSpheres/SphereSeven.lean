import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenConnectivity
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Iso

/-! # The seventh homotopy group of the literal seven-sphere -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

/-- The seventh Hurewicz isomorphism followed by the proved integral sphere marking. -/
@[irreducible] def pi7_sphere_seven_mulEquiv (x : Sphere 7) :
    π_ 7 (Sphere 7) x ≃* Multiplicative ℤ :=
  (SeventhHurewicz.hurewiczPi7Equiv x).trans
    (HopfProblem.SphereHomology.unitSphereHomologyTopEquiv 6).toAddEquiv.toMultiplicative

end Wikipedia.HomotopyGroupsOfSpheres
