import Wikipedia.HopfProblem.DegreeCollapseSixthHopfKernel
import Wikipedia.HomotopyGroupsOfSpheres.SphereThreeSix

/-!
# Every composition S9 -> S6 -> S3 vanishes after stabilization

The genuine pi6(S3) has exponent twelve. Its double suspension therefore
has even coordinate in the cyclic third stem. The mixed composition
formula annihilates its pairing with every other third-stem class.
Seven original suspensions of the actual composite are sufficient.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.ThirdTorsionComposition

open NoExoticSixSphere SmoothCube SphereComposition IteratedProductSphere
open CubicalSphereSuspension

theorem composition_eq_one_of_twelfth_power (f g : Based 8 5)
    (hf : sphereClass f ^ 12 = 1) :
    sphereClass (comp (iterate f 5) (iterate g 8)) = 1 := by
  have h := SphereSmashNative.product_eq_one_of_twelfth_power_eq_one_left
    (sphereClass f) (sphereClass g) hf
  rw [MixedSixthComposition.product_eq_inverse_composition, inv_eq_one] at h
  exact h

theorem sphereSixThree_pow_twelve (c : π_ 6 (Sphere 3) (spherePole 3)) : c ^ 12 = 1 := by
  let e := Wikipedia.HomotopyGroupsOfSpheres.pi6_sphere_three_mulEquiv (spherePole 3)
  apply e.injective
  rw [map_pow, map_one]
  have hc : Nat.card (Multiplicative (ZMod 12)) = 12 := by simp
  simpa only [hc] using
    (show e c ^ Nat.card (Multiplicative (ZMod 12)) = 1 from pow_card_eq_one')

theorem twice_suspended_pow_twelve (f : Based 6 3) :
    sphereClass (iterate f 2) ^ 12 = 1 := by
  have h1 : sphereClass (productBasedMap f) ^ 12 = 1 := by
    rw [← hom_sphereClass, ← map_pow, sphereSixThree_pow_twelve, map_one]
  change sphereClass (productBasedMap (productBasedMap f)) ^ 12 = 1
  rw [← hom_sphereClass, ← map_pow, h1, map_one]

theorem basedLift_composition (f : Based 6 3) (g : Based 8 5) :
    CubicalStableSix.basedLift (by decide : 1 ≤ 8) (comp f (productBasedMap g)) =
      comp (iterate (iterate f 2) 5) (iterate g 8) := by
  change iterate (comp f (productBasedMap g)) 7 = _
  rw [SixthHopfKernel.iterate_comp]
  rfl

theorem transition_map_eq_one (f : Based 6 3)
    (c : π_ 9 (Sphere 6) (spherePole 6)) :
    CubicalStableSix.transition 1 8 (by decide) (mapHom f 9 c) = 1 := by
  obtain ⟨g, hg⟩ := sphereClass_surjective (by decide : 0 < 8)
    ((StableThirdAttaching.stepEquiv 0).symm c)
  have hc : sphereClass (productBasedMap g) = c := by
    rw [← hom_sphereClass, hg]
    exact (StableThirdAttaching.stepEquiv 0).apply_symm_apply c
  rw [← hc, mapHom_sphereClass, CubicalStableSix.transition_sphereClass,
    basedLift_composition]
  exact composition_eq_one_of_twelfth_power (iterate f 2) g (twice_suspended_pow_twelve f)

theorem stable_map_eq_one (f : Based 6 3) (c : π_ 9 (Sphere 6) (spherePole 6)) :
    CubicalStableSix.ofNative (k := 1) (mapHom f 9 c) = 1 := by
  have h := CubicalStableSix.ofNative_transition (by decide : 1 ≤ 8) (mapHom f 9 c)
  rw [transition_map_eq_one, CubicalStableSix.ofNative_one] at h
  exact h.symm

end Wikipedia.HopfProblem.DegreeCollapse.ThirdTorsionComposition
