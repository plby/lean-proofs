import Wikipedia.HomotopyGroupsOfSpheres.HopfInjectivity
import Wikipedia.HomotopyGroupsOfSpheres.SphereThree
import Wikipedia.HopfProblem.OrbitPairNormalSphereConnectivity
import Wikipedia.HopfProblem.OrbitPairMeridianSphereHomology

/-!
# The third homotopy group of the two-sphere

The actual Hopf sphere map induces an isomorphism on third homotopy groups.
Homeomorphisms to the ordinary Euclidean spheres and the third Hurewicz
calculation for the three-sphere identify this group with the integers.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem HopfProblem.OrbitPair
open HopfProblem.SpecialPeriods
open HopfProblem.CuspCircleNormalTrivialization

/-- Transport the chosen base point along an actual equality. -/
private def basepointMulEquiv {X : Type} [TopologicalSpace X] {x y : X} (h : x = y) :
    π_ 3 X x ≃* π_ 3 X y := by
  cases h
  exact MulEquiv.refl _

/-- The third native homotopy group of the standard two-sphere is infinite cyclic. -/
def pi3_sphere_two_mulEquiv (x : Sphere 2) :
    π_ 3 (Sphere 2) x ≃* Multiplicative ℤ := by
  let r : ℝ := injectiveRadius / 2
  have hr₀ : 0 < r := half_pos injectiveRadius_pos
  have hr : r < injectiveRadius := half_lt_self injectiveRadius_pos
  let eB := meridianSphereHomeomorph r hr₀
  let eE := normalSphereHomeomorph r hr₀
  let v : NormalSphere r := Classical.choose (sphereHopfMap_surjective r (eB.symm x))
  have hv : sphereHopfMap r v = eB.symm x :=
    Classical.choose_spec (sphereHopfMap_surjective r (eB.symm x))
  let e₃ : π_ 3 (NormalSphere r) v ≃* Multiplicative ℤ :=
    (homeomorphMulEquiv (N := Fin 3) eE v).trans (pi3_sphere_three_mulEquiv (eE v))
  let e₂ : π_ 3 (MeridianSphere r) (eB.symm x) ≃* Multiplicative ℤ :=
    (basepointMulEquiv hv.symm).trans
      ((hopfPi3MulEquiv (OnePoint.infty : RiemannSphere) r hr₀ hr v).symm.trans e₃)
  exact (homeomorphMulEquiv (N := Fin 3) eB.symm x).trans e₂

end Wikipedia.HomotopyGroupsOfSpheres
