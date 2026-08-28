import Wikipedia.HopfProblem.DegreeCollapseQuaternionicClutching
import Wikipedia.HopfProblem.DegreeCollapseThirdTorsionComposition

/-!
# Every original pi9(S3) class has zero stable sixth-stem image

The actual two-frame clutching factorization and the mixed composition
calculation together kill every class after seven product suspensions.
There is no numerical pi9(S3) hypothesis and no stable-vanishing input.
This removes that unstable contribution, but does not complete the
sixth-stem generation or the geometric Arf comparison.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.NinthSphereStableVanishing

open NoExoticSixSphere SmoothCube SphereComposition

theorem transition_eq_one (x : π_ 9 (Sphere 3) (spherePole 3)) :
    CubicalStableSix.transition 1 8 (by decide) x = 1 := by
  obtain ⟨g, rfl⟩ := QuaternionicClutching.sphere_class_factorization x
  exact ThirdTorsionComposition.transition_map_eq_one
    QuaternionicClutching.sphereClutching (sphereClass g)

theorem stable_eq_one (x : π_ 9 (Sphere 3) (spherePole 3)) :
    CubicalStableSix.ofNative (k := 1) x = 1 := by
  have h := CubicalStableSix.ofNative_transition (by decide : 1 ≤ 8) x
  rw [transition_eq_one, CubicalStableSix.ofNative_one] at h
  exact h.symm

theorem product_iterate_nullhomotopic (f : Based 9 3) :
    (IteratedProductSphere.iterate f 7).val.Nullhomotopic := by
  apply (sphereClass_eq_one_iff_nullhomotopic (by decide : 0 < 16) _).mp
  have h := transition_eq_one (sphereClass f)
  rw [CubicalStableSix.transition_sphereClass] at h
  exact h

end Wikipedia.HopfProblem.DegreeCollapse.NinthSphereStableVanishing

