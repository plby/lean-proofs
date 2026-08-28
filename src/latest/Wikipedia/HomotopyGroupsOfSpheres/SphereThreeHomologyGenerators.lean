import Wikipedia.HomotopyGroupsOfSpheres.SphereThree
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps
import Wikipedia.HomotopyGroupsOfSpheres.CyclicGenerators
import Wikipedia.HopfProblem.ThirdHurewiczNaturality

/-! # Actual third-sphere generators are preserved by a homology isomorphism -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open Wikipedia.HopfProblem Wikipedia.HopfProblem.SingularMayerVietoris

theorem thirdHurewicz_pointed_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) (a : π_ 3 X x) :
    singularHomologyMap f 3 (ThirdHurewicz.hurewiczFunction x a) =
      ThirdHurewicz.hurewiczFunction y (pointedMap f x y h a) := by
  cases h
  refine Quotient.inductionOn a fun p ↦ ?_
  exact ThirdHurewicz.cubeHomologyClass_natural f x p

theorem sphereThree_hurewicz_bijective (x : Sphere 3) :
    Function.Bijective (ThirdHurewicz.hurewiczFunction x) := by
  let := SphereHomology.unitSphere_piTwo_subsingleton 0 x
  have he (a : π_ 3 (Sphere 3) x) :
      (ThirdHurewicz.hurewiczPi3Equiv x a).toAdd = ThirdHurewicz.hurewiczFunction x a := rfl
  constructor
  · intro a b h
    apply (ThirdHurewicz.hurewiczPi3Equiv x).injective
    have h' : (ThirdHurewicz.hurewiczPi3Equiv x a).toAdd =
        (ThirdHurewicz.hurewiczPi3Equiv x b).toAdd := by rw [he, he, h]
    exact congrArg Multiplicative.ofAdd h'
  · intro a
    refine ⟨(ThirdHurewicz.hurewiczPi3Equiv x).symm (Multiplicative.ofAdd a), ?_⟩
    rw [← he, MulEquiv.apply_symm_apply]
    rfl

theorem sphereThree_pointedMap_bijective_of_homology
    (f : C(Sphere 3, Sphere 3)) (x y : Sphere 3) (h : f x = y)
    (hh : Function.Bijective (singularHomologyMap f 3)) :
    Function.Bijective (pointedMap (N := Fin 3) f x y h) := by
  have hx := sphereThree_hurewicz_bijective x
  have hy := sphereThree_hurewicz_bijective y
  constructor
  · intro a b hab
    apply hx.1
    apply hh.1
    rw [thirdHurewicz_pointed_natural f x y h,
      thirdHurewicz_pointed_natural f x y h, hab]
  · intro a
    obtain ⟨b, hb⟩ := hh.2 (ThirdHurewicz.hurewiczFunction y a)
    obtain ⟨c, hc⟩ := hx.2 b
    refine ⟨c, hy.1 ?_⟩
    rw [← thirdHurewicz_pointed_natural f x y h, hc, hb]

def sphereThreeGenerator (x : Sphere 3) : π_ 3 (Sphere 3) x :=
  (pi3_sphere_three_mulEquiv x).symm (Multiplicative.ofAdd 1)

theorem sphereThreeGenerator_generates (x : Sphere 3) :
    Function.Surjective (fun k : ℤ ↦ sphereThreeGenerator x ^ k) := by
  apply CyclicGenerators.of_coordinate_natAbs (pi3_sphere_three_mulEquiv x)
  change Int.natAbs ((pi3_sphere_three_mulEquiv x)
    ((pi3_sphere_three_mulEquiv x).symm (Multiplicative.ofAdd 1))).toAdd = 1
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem sphereThreeMap_generator_generates_of_homology
    (f : C(Sphere 3, Sphere 3)) (x y : Sphere 3) (h : f x = y)
    (hh : Function.Bijective (singularHomologyMap f 3)) :
    Function.Surjective (fun k : ℤ ↦ (pointedMap f x y h (sphereThreeGenerator x)) ^ k) :=
  (CyclicGenerators.map_generates_iff (pointedMap f x y h)
    (sphereThreeGenerator x) (sphereThreeGenerator_generates x)).mpr
      (sphereThree_pointedMap_bijective_of_homology f x y h hh).2

end Wikipedia.HomotopyGroupsOfSpheres
