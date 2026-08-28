import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Naturality
import Wikipedia.HomotopyGroupsOfSpheres.SphereSeven

/-! # The native seventh-sphere marking is the actual top-homology degree -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.SingularMayerVietoris

attribute [local irreducible] unitSphereHomologyTopEquiv

private theorem multiplicativeMarking_apply {A : Type} [AddZeroClass A]
    (e : A ≃+ ℤ) (a : Multiplicative A) :
    (e.toMultiplicative a).toAdd = e a.toAdd := rfl

theorem pi7_sphere_seven_coordinate (x : Sphere 7) (a : π_ 7 (Sphere 7) x) :
    (pi7_sphere_seven_mulEquiv x a).toAdd =
      unitSphereHomologyTopEquiv 6 (SeventhHurewicz.hurewiczFunction x a) := by
  unfold pi7_sphere_seven_mulEquiv
  rw [MulEquiv.trans_apply, multiplicativeMarking_apply,
    SeventhHurewicz.hurewiczPi7Equiv_apply, SeventhHurewicz.hurewiczPi7_toAdd]
  exact LinearEquiv.coe_addEquiv_apply (unitSphereHomologyTopEquiv 6) _

def sphereSevenGenerator (x : Sphere 7) : π_ 7 (Sphere 7) x :=
  (pi7_sphere_seven_mulEquiv x).symm (Multiplicative.ofAdd 1)

theorem sphereSevenGenerator_hurewicz (x : Sphere 7) :
    SeventhHurewicz.hurewiczFunction x (sphereSevenGenerator x) = unitSphereTopClass 6 := by
  apply (unitSphereHomologyTopEquiv 6).injective
  rw [unitSphereHomologyTopEquiv_topClass, ← pi7_sphere_seven_coordinate]
  exact congrArg Multiplicative.toAdd ((pi7_sphere_seven_mulEquiv x).apply_symm_apply _)

def sphereSevenDegree (f : C(Sphere 7, Sphere 7)) : ℤ :=
  unitSphereHomologyTopEquiv 6 (singularHomologyMap f 7 (unitSphereTopClass 6))

/-- Actual pointed postcomposition of a generator has the actual homological degree. -/
theorem sphereSevenDegree_pointedMap (f : C(Sphere 7, Sphere 7))
    (x y : Sphere 7) (h : f x = y) :
    (pi7_sphere_seven_mulEquiv y (pointedMap f x y h (sphereSevenGenerator x))).toAdd =
      sphereSevenDegree f := by
  refine (pi7_sphere_seven_coordinate y
    (pointedMap f x y h (sphereSevenGenerator x))).trans ?_
  have hn := SeventhHurewicz.hurewiczFunction_pointed_natural f x y h (sphereSevenGenerator x)
  have hm := congrArg
    (fun c : SingularHomology (Sphere 7) 7 ↦ unitSphereHomologyTopEquiv 6 c) hn.symm
  refine hm.trans ?_
  exact congrArg (fun c ↦ unitSphereHomologyTopEquiv 6 (singularHomologyMap f 7 c))
    (sphereSevenGenerator_hurewicz x)

end Wikipedia.HomotopyGroupsOfSpheres
