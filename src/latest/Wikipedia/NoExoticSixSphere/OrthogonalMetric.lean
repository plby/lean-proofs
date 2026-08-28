import Wikipedia.NoExoticSixSphere.OrthogonalLieGroup

/-!
# Invariance of the original orthogonal operator metric

Both left and right orthogonal multiplication preserve operator-norm distance.
These identities keep uniform small-increment arguments in the existing
nested-subtype metric, without introducing a new metric on the group.
-/

namespace NoExoticSixSphere.OrthogonalMetric

open GLOrthonormalization OrthogonalPaths OrthogonalSmoothness

variable {n : ℕ}

theorem dist_mul_left (a b c : OrthogonalOperators n) : dist (a * b) (a * c) = dist b c := by
  change dist (mul a b).1.1 (mul a c).1.1 = dist b.1.1 c.1.1
  rw [dist_eq_norm, dist_eq_norm, mul_operator, mul_operator, ← ContinuousLinearMap.comp_sub]
  rw [← toEquiv_operator a]
  exact ContinuousLinearMap.opNorm_linearIsometryEquiv_comp (toEquiv a) _

theorem dist_mul_right (a b c : OrthogonalOperators n) : dist (a * c) (b * c) = dist a b := by
  change dist (mul a c).1.1 (mul b c).1.1 = dist a.1.1 b.1.1
  rw [dist_eq_norm, dist_eq_norm, mul_operator, mul_operator, ← ContinuousLinearMap.sub_comp]
  rw [← toEquiv_operator c]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ (toEquiv c)

theorem dist_inverse (a b : OrthogonalOperators n) : dist a⁻¹ b⁻¹ = dist a b := by
  calc
    dist a⁻¹ b⁻¹ = dist (a * a⁻¹) (a * b⁻¹) := (dist_mul_left a a⁻¹ b⁻¹).symm
    _ = dist 1 (a * b⁻¹) := by rw [mul_inv_cancel]
    _ = dist (1 * b) ((a * b⁻¹) * b) := (dist_mul_right 1 (a * b⁻¹) b).symm
    _ = dist b a := by rw [one_mul, _root_.mul_assoc, inv_mul_cancel, mul_one]
    _ = dist a b := dist_comm _ _

theorem dist_left_increment (a b : OrthogonalOperators n) : dist (a⁻¹ * b) 1 = dist b a := by
  calc
    dist (a⁻¹ * b) 1 = dist (a⁻¹ * b) (a⁻¹ * a) := by rw [inv_mul_cancel]
    _ = dist b a := dist_mul_left _ _ _

end NoExoticSixSphere.OrthogonalMetric
