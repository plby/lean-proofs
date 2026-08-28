import Wikipedia.HopfProblem.SphereHomologySimplyConnected
import Wikipedia.HopfProblem.ThirdHurewiczIso
import Wikipedia.HopfProblem.FourthHurewiczIso
import Wikipedia.HopfProblem.FifthHurewiczIso
import Wikipedia.HopfProblem.SixSphereCubeSphere

/-!
# Five-connectivity of the literal standard six-sphere

Successive native Hurewicz isomorphisms and the already computed sphere
homology give all the precise connectivity inputs needed for the based
degree classification. No smooth sphere-recognition assertion is imported.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.Sphere

open SixSphereCube SingularMayerVietoris

theorem piTwo_subsingleton (x : StandardSphere) : Subsingleton (π_ 2 StandardSphere x) :=
  SphereHomology.unitSphere_piTwo_subsingleton 3 x

theorem piThree_subsingleton (x : StandardSphere) : Subsingleton (π_ 3 StandardSphere x) := by
  let := piTwo_subsingleton x
  let := SphereHomology.unitSphere_homology_subsingleton 5 3 (by decide) (by decide)
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

theorem piFour_subsingleton (x : StandardSphere) : Subsingleton (π_ 4 StandardSphere x) := by
  let := piTwo_subsingleton x
  let := piThree_subsingleton x
  let := SphereHomology.unitSphere_homology_subsingleton 5 4 (by decide) (by decide)
  exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton

theorem piFive_subsingleton (x : StandardSphere) : Subsingleton (π_ 5 StandardSphere x) := by
  let := piTwo_subsingleton x
  let := piThree_subsingleton x
  let := piFour_subsingleton x
  let := SphereHomology.unitSphere_homology_subsingleton 5 5 (by decide) (by decide)
  exact (FifthHurewicz.hurewiczPi5Equiv x).injective.subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.Sphere
