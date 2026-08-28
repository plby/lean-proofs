import Wikipedia.HomotopyGroupsOfSpheres.SphereFive
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps
import Wikipedia.HomotopyGroupsOfSpheres.CyclicGenerators
import Wikipedia.HopfProblem.FifthHurewiczNaturality

/-! # Actual fifth-sphere generators are preserved by a homology isomorphism -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open Wikipedia.HopfProblem Wikipedia.HopfProblem.SingularMayerVietoris

theorem fifthHurewicz_pointed_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) (a : π_ 5 X x) :
    singularHomologyMap f 5 (FifthHurewicz.hurewiczFunction x a) =
      FifthHurewicz.hurewiczFunction y (pointedMap f x y h a) := by
  cases h
  refine Quotient.inductionOn a fun p ↦ ?_
  exact FifthHurewicz.cubeHomologyClass_natural f x p

theorem sphereFive_hurewicz_bijective (x : Sphere 5) :
    Function.Bijective (FifthHurewicz.hurewiczFunction x) := by
  have he (a : π_ 5 (Sphere 5) x) :
      (FifthHurewicz.hurewiczPi5Equiv x a).toAdd = FifthHurewicz.hurewiczFunction x a := rfl
  constructor
  · intro a b h
    apply (FifthHurewicz.hurewiczPi5Equiv x).injective
    have h' : (FifthHurewicz.hurewiczPi5Equiv x a).toAdd =
        (FifthHurewicz.hurewiczPi5Equiv x b).toAdd := by rw [he, he, h]
    exact congrArg Multiplicative.ofAdd h'
  · intro a
    refine ⟨(FifthHurewicz.hurewiczPi5Equiv x).symm (Multiplicative.ofAdd a), ?_⟩
    rw [← he, MulEquiv.apply_symm_apply]
    rfl

theorem sphereFive_pointedMap_bijective_of_homology
    (f : C(Sphere 5, Sphere 5)) (x y : Sphere 5) (h : f x = y)
    (hh : Function.Bijective (singularHomologyMap f 5)) :
    Function.Bijective (pointedMap (N := Fin 5) f x y h) := by
  have hx := sphereFive_hurewicz_bijective x
  have hy := sphereFive_hurewicz_bijective y
  constructor
  · intro a b hab
    apply hx.1
    apply hh.1
    rw [fifthHurewicz_pointed_natural f x y h,
      fifthHurewicz_pointed_natural f x y h, hab]
  · intro a
    obtain ⟨b, hb⟩ := hh.2 (FifthHurewicz.hurewiczFunction y a)
    obtain ⟨c, hc⟩ := hx.2 b
    refine ⟨c, hy.1 ?_⟩
    rw [← fifthHurewicz_pointed_natural f x y h, hc, hb]

def sphereFiveGenerator (x : Sphere 5) : π_ 5 (Sphere 5) x :=
  (pi5_sphere_five_mulEquiv x).symm (Multiplicative.ofAdd 1)

theorem sphereFiveGenerator_generates (x : Sphere 5) :
    Function.Surjective (fun k : ℤ ↦ sphereFiveGenerator x ^ k) := by
  apply CyclicGenerators.of_coordinate_natAbs (pi5_sphere_five_mulEquiv x)
  change Int.natAbs ((pi5_sphere_five_mulEquiv x)
    ((pi5_sphere_five_mulEquiv x).symm (Multiplicative.ofAdd 1))).toAdd = 1
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem sphereFiveMap_generator_generates_of_homology
    (f : C(Sphere 5, Sphere 5)) (x y : Sphere 5) (h : f x = y)
    (hh : Function.Bijective (singularHomologyMap f 5)) :
    Function.Surjective (fun k : ℤ ↦ (pointedMap f x y h (sphereFiveGenerator x)) ^ k) :=
  (CyclicGenerators.map_generates_iff (pointedMap f x y h)
    (sphereFiveGenerator x) (sphereFiveGenerator_generates x)).mpr
      (sphereFive_pointedMap_bijective_of_homology f x y h hh).2

end Wikipedia.HomotopyGroupsOfSpheres
