import Wikipedia.NoExoticSixSphere.HigherHopfNativeEquivalence
import Wikipedia.HomotopyGroupsOfSpheres.SphereThreeSix
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps
import Wikipedia.HopfProblem.OrbitPairNormalSphereConnectivity
import Wikipedia.HopfProblem.OrbitPairMeridianSphereHomology

/-!
# The sixth homotopy group of the two-sphere is cyclic of order twelve

The actual Hopf sphere map induces an isomorphism on native homotopy groups
in every degree at least three. Its sixth-degree specialization, transported
to the literal Euclidean spheres, combines with the unconditional calculation
of the sixth homotopy group of the three-sphere.
-/

open scoped Topology
open Wikipedia.HopfProblem Wikipedia.HopfProblem.OrbitPair
open Wikipedia.HopfProblem.SpecialPeriods
open Wikipedia.HopfProblem.CuspCircleNormalTrivialization

namespace Wikipedia.HomotopyGroupsOfSpheres

/-- Unconditionally, the native sixth homotopy group of `S²` is `ℤ/12ℤ`. -/
noncomputable def pi6_sphere_two_mulEquiv (x : Sphere 2) :
    π_ 6 (Sphere 2) x ≃* Multiplicative (ZMod 12) := by
  let r : ℝ := injectiveRadius / 2
  have hr₀ : 0 < r := half_pos injectiveRadius_pos
  have hr : r < injectiveRadius := half_lt_self injectiveRadius_pos
  let eB := meridianSphereHomeomorph r hr₀
  let eE := normalSphereHomeomorph r hr₀
  let v : NormalSphere r := Classical.choose (sphereHopfMap_surjective r (eB.symm x))
  have hv : sphereHopfMap r v = eB.symm x :=
    Classical.choose_spec (sphereHopfMap_surjective r (eB.symm x))
  let e₃ : π_ 6 (NormalSphere r) v ≃* Multiplicative (ZMod 12) :=
    (homeomorphMulEquiv (N := Fin 6) eE v).trans (pi6_sphere_three_mulEquiv (eE v))
  let e₂ : π_ 6 (MeridianSphere r) (eB.symm x) ≃* Multiplicative (ZMod 12) :=
    (basepointEqMulEquiv hv.symm).trans
      ((NoExoticSixSphere.HigherHopf.piMulEquiv
        (OnePoint.infty : RiemannSphere) r hr₀ hr 3 v).symm.trans e₃)
  exact (homeomorphMulEquiv (N := Fin 6) eB.symm x).trans e₂

end Wikipedia.HomotopyGroupsOfSpheres
