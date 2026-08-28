import Wikipedia.NoExoticSixSphere.EquatorDimension
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups
import Wikipedia.NoExoticSixSphere.OrthogonalRotations
import Mathlib.Analysis.Quaternion

/-!
# Actual unit quaternions and the reflection-square identity

The unit quaternion space has its original norm-subspace topology and is
homeomorphic to the standard three-sphere by the actual quaternion coordinate
isometry. Multiplication and squaring are continuous maps of this sphere.
Squaring is exactly the negative reflection of the real unit vector.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.QuaternionSphere

abbrev Space := UnitSphere ℍ

def one : Space := ⟨1, by simp⟩

def sphereHomeomorph : Space ≃ₜ Sphere 3 :=
  unitSphereCongr Quaternion.linearIsometryEquivTuple

instance simplyConnected : SimplyConnectedSpace Space :=
  sphereHomeomorph.toHomotopyEquiv.simplyConnectedSpace

instance piTwoSubsingleton : Subsingleton (HomotopyGroup (Fin 2) Space one) :=
  subsingleton_homotopyGroup_of_homeomorph_sphere (by decide) sphereHomeomorph one

def multiply : C(Space × Space, Space) where
  toFun p := ⟨p.1.val * p.2.val, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_mul, ClosedHemisphere.unit_norm, mul_one]⟩
  continuous_toFun := by
    have h : Continuous (fun p : Space × Space ↦ p.1.val * p.2.val) :=
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
    exact h.subtype_mk (fun p ↦ by
      simp only [Metric.mem_sphere, dist_zero_right, norm_mul,
        ClosedHemisphere.unit_norm, mul_one])

theorem multiply_one_left (x : Space) : multiply (one, x) = x := Subtype.ext (one_mul _)

theorem multiply_one_right (x : Space) : multiply (x, one) = x := Subtype.ext (mul_one _)

def diagonal : C(Space, Space × Space) := (ContinuousMap.id Space).prodMk (ContinuousMap.id Space)

def square : C(Space, Space) := multiply.comp diagonal

theorem square_apply (x : Space) : (square x).val = x.val ^ 2 := by
  change x.val * x.val = x.val ^ 2
  rw [pow_two]

theorem normSq_unit (x : Space) : Quaternion.normSq x.val = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self, ClosedHemisphere.unit_norm, mul_one]

theorem square_vector (x : Space) : x.val ^ 2 = (2 * x.val.re) • x.val - 1 := by
  have h := Quaternion.star_mul_self x.val
  rw [Quaternion.star_eq_two_re_sub, sub_mul, Quaternion.coe_mul_eq_smul,
    ← sq, normSq_unit] at h
  change (2 * x.val.re) • x.val - x.val ^ 2 = 1 at h
  calc
    x.val ^ 2 = (2 * x.val.re) • x.val - ((2 * x.val.re) • x.val - x.val ^ 2) := by abel
    _ = (2 * x.val.re) • x.val - 1 := by rw [h]

theorem square_reflection (x : Space) :
    (square x).val = -hyperplaneReflectionOperator x.val (1 : ℍ) := by
  rw [square_apply, square_vector, hyperplaneReflectionOperator_apply]
  simp only [ClosedHemisphere.unit_norm, one_pow, inv_one, mul_one,
    Quaternion.inner_def, star_one, neg_sub]

end NoExoticSixSphere.QuaternionSphere
