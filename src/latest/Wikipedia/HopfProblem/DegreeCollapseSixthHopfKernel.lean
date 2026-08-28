import Wikipedia.HopfProblem.DegreeCollapseMixedSixthComposition
import Wikipedia.NoExoticSixSphere.QuaternionicHopfBaseExactness

/-!
# The stabilized quaternionic Hopf kernel has at most two values

The actual pi10(S7) is a third-stem stage, so every element is the
double suspension of an actual pi8(S5) class. Six further original
suspensions turn postcomposition by any S7-to-S4 map into the mixed
composition already computed. Thus its stable image is contained in
the identity and the actual third-stem square.

Apply the original Hopf-fibration exactness to its connecting kernel
in pi10(S4). No sixth-stem generation or Arf detection is assumed or
concluded: desuspension and classes outside this kernel remain open.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SixthHopfKernel

open NoExoticSixSphere SmoothCube SphereComposition IteratedProductSphere
open CubicalSphereSuspension

theorem iterate_comp {l m n : ℕ} (f : Based m n) (g : Based l m) (r : ℕ) :
    iterate (comp f g) r = comp (iterate f r) (iterate g r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change productBasedMap (iterate (comp f g) r) =
      comp (productBasedMap (iterate f r)) (productBasedMap (iterate g r))
    rw [ih, productBasedMap_comp]

theorem third_class_iterate_two (g : Based 8 5) :
    sphereClass (iterate g 2) = StableThirdAttaching.fromFirst 2 (sphereClass g) := by
  change sphereClass (productBasedMap (productBasedMap g)) =
    StableThirdAttaching.stepHom 1 (StableThirdAttaching.stepHom 0 (sphereClass g))
  rw [← hom_sphereClass, ← hom_sphereClass]
  rfl

theorem basedLift_composition (f : Based 7 4) (g : Based 8 5) :
    CubicalStableSix.basedLift (by decide : 2 ≤ 8) (comp f (iterate g 2)) =
      comp (iterate (productBasedMap f) 5) (iterate g 8) := by
  change iterate (comp f (iterate g 2)) 6 = _
  rw [iterate_comp]
  rfl

theorem stable_map_eq_late_composition (f : Based 7 4) (g : Based 8 5) :
    CubicalStableSix.ofNative (k := 2) (mapHom f 10 (sphereClass (iterate g 2))) =
      CubicalStableSix.ofNative (k := 8)
        (sphereClass (comp (iterate (productBasedMap f) 5) (iterate g 8))) := by
  rw [mapHom_sphereClass]
  have h := CubicalStableSix.ofNative_transition (by decide : 2 ≤ 8)
    (sphereClass (comp f (iterate g 2)))
  rw [CubicalStableSix.transition_sphereClass, basedLift_composition] at h
  exact h.symm

theorem stable_map_eq_one_or_square (f : Based 7 4)
    (c : π_ 10 (Sphere 7) (spherePole 7)) :
    CubicalStableSix.ofNative (k := 2) (mapHom f 10 c) = 1 ∨
      CubicalStableSix.ofNative (k := 2) (mapHom f 10 c) =
        StableThirdComposition.stableSquare := by
  obtain ⟨g, hg⟩ := sphereClass_surjective (by decide : 0 < 8)
    ((StableThirdAttaching.fromFirst 2).symm c)
  have hc : sphereClass (iterate g 2) = c := by
    rw [third_class_iterate_two, hg, MulEquiv.apply_symm_apply]
  rw [← hc, stable_map_eq_late_composition]
  exact MixedSixthComposition.stable_composition_eq_one_or_square (productBasedMap f) g

theorem stable_map_pow_two (f : Based 7 4) (c : π_ 10 (Sphere 7) (spherePole 7)) :
    CubicalStableSix.ofNative (k := 2) (mapHom f 10 c) ^ 2 = 1 := by
  rcases stable_map_eq_one_or_square f c with h | h
  · rw [h, one_pow]
  · rw [h, StableThirdComposition.stableSquare_pow_two]

theorem stable_hopf_kernel_eq_one_or_square
    (x : π_ 10 (Sphere 4) (spherePole 4)) (hx : QuaternionicHopf.connecting 9 x = 1) :
    CubicalStableSix.ofNative (k := 2) x = 1 ∨
      CubicalStableSix.ofNative (k := 2) x = StableThirdComposition.stableSquare := by
  obtain ⟨c, rfl⟩ := (QuaternionicHopf.projectionMap_range_eq_connecting_kernel x).mpr hx
  exact stable_map_eq_one_or_square QuaternionicHopf.basedMap c

theorem stable_hopf_kernel_pow_two
    (x : π_ 10 (Sphere 4) (spherePole 4)) (hx : QuaternionicHopf.connecting 9 x = 1) :
    CubicalStableSix.ofNative (k := 2) x ^ 2 = 1 := by
  rcases stable_hopf_kernel_eq_one_or_square x hx with h | h
  · rw [h, one_pow]
  · rw [h, StableThirdComposition.stableSquare_pow_two]

end Wikipedia.HopfProblem.DegreeCollapse.SixthHopfKernel

