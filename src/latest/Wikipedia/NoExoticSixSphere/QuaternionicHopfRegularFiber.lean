import Wikipedia.NoExoticSixSphere.QuaternionicHopfTransverseDifferential
import Wikipedia.NoExoticSixSphere.SphereAmbientSubmersion

/-!
# The north pole is an actual regular value of the quaternionic Hopf map

The explicit second-coordinate differential has a right inverse,
and its source directions are tangent to the original seven-sphere.
The ambient-to-native chain rule proves surjectivity of the actual
manifold derivative at every point of the entire north fiber.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace NoExoticSixSphere.QuaternionicHopf

theorem first_mul_star (x : Sphere 7) (hx : second x.val = 0) :
    first x.val * star (first x.val) = 1 := by
  have hs := normSq_sum x.val
  rw [hx, map_zero, add_zero, mem_sphere_zero_iff_norm.mp x.property, one_pow] at hs
  rw [Quaternion.self_mul_star, hs]
  rfl

theorem transverse_right_inverse (a w : ℍ) (ha : a * star a = 1) :
    (2 : ℝ) • (a * star ((1 / 2 : ℝ) • (star w * a))) = w := by
  rw [Quaternion.star_smul, star_mul, star_star, mul_smul_comm,
    ← mul_assoc, ha, one_mul, smul_smul]
  norm_num

theorem pole_inner_head (z : V 5) : inner ℝ (spherePole 4).val z = z 0 := by
  simp [spherePole, EuclideanSpace.inner_single_left]

theorem join_zero_tail (z : V 5) (hz : z 0 = 0) :
    SphereCylinder.join 3 (0, SphereCylinder.tail 3 z) = z := by
  have h : SphereCylinder.join 3 (z 0, SphereCylinder.tail 3 z) = z :=
    (SphereCylinder.join 3).apply_symm_apply z
  simpa only [hz] using h

theorem polynomial_tangent_surjective (x : Sphere 7) (hx : second x.val = 0)
    (z : V 5) (hz : z 0 = 0) :
    ∃ v : V 8, inner ℝ x.val v = 0 ∧ fderiv ℝ polynomial x.val v = z := by
  let w := Quaternion.linearIsometryEquivTuple.symm (SphereCylinder.tail 3 z)
  let v := (1 / 2 : ℝ) • (star w * first x.val)
  refine ⟨secondAxis v, inner_secondAxis x.val hx v, ?_⟩
  rw [polynomial_fderiv_second x.val hx]
  have ht := transverse_right_inverse (first x.val) w (first_mul_star x hx)
  change (2 : ℝ) • (first x.val * star v) = w at ht
  rw [ht]
  change SphereCylinder.join 3 (0, Quaternion.linearIsometryEquivTuple
    (Quaternion.linearIsometryEquivTuple.symm (SphereCylinder.tail 3 z))) = z
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact join_zero_tail z hz

theorem north_regular (x : Sphere 7) (hx : sphereMap x = spherePole 4) :
    Function.Surjective (mfderiv (𝓡 7) (𝓡 4) sphereMap x) := by
  apply sphereMap_mfderiv_surjective_of_ambient polynomial sphereMap contDiff_polynomial
    contMDiff_sphereMap sphereMap_val x
  intro z hz
  rw [hx, pole_inner_head] at hz
  exact polynomial_tangent_surjective x ((sphereMap_eq_pole_iff x).mp hx) z hz

end NoExoticSixSphere.QuaternionicHopf
