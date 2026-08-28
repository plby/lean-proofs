import Wikipedia.HomotopyGroupsOfSpheres.SphereFour
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps
import Wikipedia.HomotopyGroupsOfSpheres.CyclicGenerators
import Wikipedia.HopfProblem.FourthHurewiczNaturality

/-! # Actual fourth-sphere generators are preserved by a homology isomorphism -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open Wikipedia.HopfProblem Wikipedia.HopfProblem.SingularMayerVietoris

theorem fourthHurewicz_pointed_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) (a : π_ 4 X x) :
    singularHomologyMap f 4 (FourthHurewicz.hurewiczFunction x a) =
      FourthHurewicz.hurewiczFunction y (pointedMap f x y h a) := by
  cases h
  refine Quotient.inductionOn a fun p ↦ ?_
  exact FourthHurewicz.cubeHomologyClass_natural f x p

theorem sphereFour_hurewicz_bijective (x : Sphere 4) :
    Function.Bijective (FourthHurewicz.hurewiczFunction x) := by
  have he (a : π_ 4 (Sphere 4) x) :
      (FourthHurewicz.hurewiczPi4Equiv x a).toAdd = FourthHurewicz.hurewiczFunction x a := rfl
  constructor
  · intro a b h
    apply (FourthHurewicz.hurewiczPi4Equiv x).injective
    have h' : (FourthHurewicz.hurewiczPi4Equiv x a).toAdd =
        (FourthHurewicz.hurewiczPi4Equiv x b).toAdd := by rw [he, he, h]
    exact congrArg Multiplicative.ofAdd h'
  · intro a
    refine ⟨(FourthHurewicz.hurewiczPi4Equiv x).symm (Multiplicative.ofAdd a), ?_⟩
    rw [← he, MulEquiv.apply_symm_apply]
    rfl

theorem sphereFour_pointedMap_bijective_of_homology
    (f : C(Sphere 4, Sphere 4)) (x y : Sphere 4) (h : f x = y)
    (hh : Function.Bijective (singularHomologyMap f 4)) :
    Function.Bijective (pointedMap (N := Fin 4) f x y h) := by
  have hx := sphereFour_hurewicz_bijective x
  have hy := sphereFour_hurewicz_bijective y
  constructor
  · intro a b hab
    apply hx.1
    apply hh.1
    rw [fourthHurewicz_pointed_natural f x y h,
      fourthHurewicz_pointed_natural f x y h, hab]
  · intro a
    obtain ⟨b, hb⟩ := hh.2 (FourthHurewicz.hurewiczFunction y a)
    obtain ⟨c, hc⟩ := hx.2 b
    refine ⟨c, hy.1 ?_⟩
    rw [← fourthHurewicz_pointed_natural f x y h, hc, hb]

def sphereFourGenerator (x : Sphere 4) : π_ 4 (Sphere 4) x :=
  (pi4_sphere_four_mulEquiv x).symm (Multiplicative.ofAdd 1)

theorem sphereFourGenerator_generates (x : Sphere 4) :
    Function.Surjective (fun k : ℤ ↦ sphereFourGenerator x ^ k) := by
  apply CyclicGenerators.of_coordinate_natAbs (pi4_sphere_four_mulEquiv x)
  change Int.natAbs ((pi4_sphere_four_mulEquiv x)
    ((pi4_sphere_four_mulEquiv x).symm (Multiplicative.ofAdd 1))).toAdd = 1
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem sphereFourMap_generator_generates_of_homology
    (f : C(Sphere 4, Sphere 4)) (x y : Sphere 4) (h : f x = y)
    (hh : Function.Bijective (singularHomologyMap f 4)) :
    Function.Surjective (fun k : ℤ ↦ (pointedMap f x y h (sphereFourGenerator x)) ^ k) :=
  (CyclicGenerators.map_generates_iff (pointedMap f x y h)
    (sphereFourGenerator x) (sphereFourGenerator_generates x)).mpr
      (sphereFour_pointedMap_bijective_of_homology f x y h hh).2

end Wikipedia.HomotopyGroupsOfSpheres
