import Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent

/-! # Based families on a single latitude cylinder -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent

open Wikipedia.HopfProblem.SphereHomology

structure SingleFamily (n : ℕ) (X : Type*) [TopologicalSpace X] (x : X) where
  map : C(I × UnitSphere n, X)
  zero : ∀ z, map (0, z) = x
  one : ∀ z, map (1, z) = x

namespace SingleFamily

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X} (F : SingleFamily n X x)

def toSphereMap : C(UnitSphere (n + 1), X) :=
  sphereLift n F.map
    (fun z w ↦ (F.zero z).trans (F.zero w).symm)
    (fun z w ↦ (F.one z).trans (F.one w).symm)

theorem toSphereMap_point (t : I) (z : UnitSphere n) :
    F.toSphereMap (Latitude.point n t z) = F.map (t, z) :=
  sphereLift_point n _ _ _ t z

end SingleFamily

end Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent
