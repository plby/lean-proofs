import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Group.Int.Units

/-!
# Integral linear automorphisms act by a unit

The image of one determines the whole map, and surjectivity forces that
image to be one or minus one.
-/

namespace NoExoticSixSphere.IntLinearAutomorphism

theorem apply_eq_mul (e : ℤ ≃ₗ[ℤ] ℤ) (k : ℤ) : e k = e 1 * k := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using e.map_smul k 1

theorem apply_one_eq_one_or_neg_one (e : ℤ ≃ₗ[ℤ] ℤ) : e 1 = 1 ∨ e 1 = -1 := by
  apply Int.eq_one_or_neg_one_of_mul_eq_one (v := e.symm 1)
  rw [← apply_eq_mul, e.apply_symm_apply]

end NoExoticSixSphere.IntLinearAutomorphism
