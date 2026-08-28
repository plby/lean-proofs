import Wikipedia.NoExoticSixSphere.CubicalSuspensionRange
import Wikipedia.HomotopyGroupsOfSpheres.SphereSeven

/-!
# No nontrivial involution in the actual top group of S12

Five original suspension isomorphisms identify pi12(S12) with the
already computed native pi7(S7). Its integral coordinate detects
involutions without a new higher-dimensional Hurewicz construction.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.TwelveSphereTorsion

open NoExoticSixSphere CubicalSphereSuspension

def step (k : ℕ) :
    π_ (k + 7) (Sphere (k + 7)) (spherePole (k + 7)) ≃*
      π_ (k + 7 + 1) (Sphere (k + 7 + 1)) (spherePole (k + 7 + 1)) :=
  MulEquiv.ofBijective (hom (k + 7) (k + 7)) (hom_bijective (by omega))

def integerEquiv : π_ 12 (Sphere 12) (spherePole 12) ≃* Multiplicative ℤ :=
  (((((step 0).trans (step 1)).trans (step 2)).trans (step 3)).trans (step 4)).symm.trans
    (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7))

theorem eq_one_of_eq_inv (a : π_ 12 (Sphere 12) (spherePole 12)) (ha : a = a⁻¹) : a = 1 := by
  have h := congrArg (fun c ↦ (integerEquiv c).toAdd) ha
  change (integerEquiv a).toAdd = (integerEquiv a⁻¹).toAdd at h
  rw [map_inv] at h
  change (integerEquiv a).toAdd = -(integerEquiv a).toAdd at h
  have hz : (integerEquiv a).toAdd = 0 := by omega
  apply integerEquiv.injective
  exact (congrArg Multiplicative.ofAdd hz).trans (map_one integerEquiv).symm

end Wikipedia.HopfProblem.DegreeCollapse.TwelveSphereTorsion

