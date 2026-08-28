import Wikipedia.HomotopyGroupsOfSpheres.SphereThree
import Wikipedia.HopfProblem.FourthHurewiczIso
import Wikipedia.HopfProblem.FifthHurewiczIso
import Wikipedia.HopfProblem.SixthHurewiczIso

/-! # Vanishing below degree seven for the actual Euclidean seven-sphere -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem HopfProblem.SphereHomology

instance sphereSeven_piTwo_subsingleton (x : Sphere 7) : Subsingleton (π_ 2 (Sphere 7) x) :=
  unitSphere_piTwo_subsingleton 4 x

instance sphereSeven_piThree_subsingleton (x : Sphere 7) : Subsingleton (π_ 3 (Sphere 7) x) := by
  let := unitSphere_homology_subsingleton 6 3 (by decide) (by decide)
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

instance sphereSeven_piFour_subsingleton (x : Sphere 7) : Subsingleton (π_ 4 (Sphere 7) x) := by
  let := unitSphere_homology_subsingleton 6 4 (by decide) (by decide)
  exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton

instance sphereSeven_piFive_subsingleton (x : Sphere 7) : Subsingleton (π_ 5 (Sphere 7) x) := by
  let := unitSphere_homology_subsingleton 6 5 (by decide) (by decide)
  exact (FifthHurewicz.hurewiczPi5Equiv x).injective.subsingleton

instance sphereSeven_piSix_subsingleton (x : Sphere 7) : Subsingleton (π_ 6 (Sphere 7) x) := by
  let := unitSphere_homology_subsingleton 6 6 (by decide) (by decide)
  exact (SixthHurewicz.hurewiczPi6Equiv x).injective.subsingleton

end Wikipedia.HomotopyGroupsOfSpheres
