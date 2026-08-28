import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenDegree
import Wikipedia.HomotopyGroupsOfSpheres.CyclicGenerators

/-! # Degree of absolute value one preserves the actual seventh sphere generator -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

theorem sphereSevenGenerator_generates (x : Sphere 7) :
    Function.Surjective (fun k : ℤ ↦ sphereSevenGenerator x ^ k) := by
  apply CyclicGenerators.of_coordinate_natAbs (pi7_sphere_seven_mulEquiv x)
  change Int.natAbs ((pi7_sphere_seven_mulEquiv x)
    ((pi7_sphere_seven_mulEquiv x).symm (Multiplicative.ofAdd 1))).toAdd = 1
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem sphereSevenMap_generator_generates (f : C(Sphere 7, Sphere 7))
    (x y : Sphere 7) (h : f x = y) (hd : Int.natAbs (sphereSevenDegree f) = 1) :
    Function.Surjective (fun k : ℤ ↦ (pointedMap f x y h (sphereSevenGenerator x)) ^ k) := by
  apply CyclicGenerators.of_coordinate_natAbs (pi7_sphere_seven_mulEquiv y)
  rw [sphereSevenDegree_pointedMap]
  exact hd

theorem sphereSevenMap_generates_iff_surjective {X : Type} [TopologicalSpace X]
    (f : C(Sphere 7, X)) (x : Sphere 7) (y : X) (hf : f x = y) :
    Function.Surjective (fun k : ℤ ↦
      (pointedMap (N := Fin 7) f x y hf (sphereSevenGenerator x)) ^ k) ↔
      Function.Surjective (pointedMap (N := Fin 7) f x y hf) :=
  CyclicGenerators.map_generates_iff (pointedMap (N := Fin 7) f x y hf)
    (sphereSevenGenerator x) (sphereSevenGenerator_generates x)

end Wikipedia.HomotopyGroupsOfSpheres
