import Wikipedia.NoExoticSixSphere.IntLinearAutomorphism
import Mathlib.Data.Int.Basic

/-!
# Intrinsic primitive direction in an infinite cyclic integral module

Normalize a class using its signed coordinate in any actual integral
marking. An automorphism of the integers multiplies by one or minus one,
and its sign cancels the corresponding generator change. Thus the result
is independent of the marking. For a nonzero input it is an actual
primitive generator, not merely an odd or nonzero multiple of one.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralPrimitiveDirection

open NoExoticSixSphere

variable {G : Type*} [AddCommGroup G] [Module ℤ G]

def normalize (e : G ≃ₗ[ℤ] ℤ) (a : G) : G := e.symm (Int.sign (e a))

theorem marking_normalize (e : G ≃ₗ[ℤ] ℤ) (a : G) :
    e (normalize e a) = Int.sign (e a) := e.apply_symm_apply _

/-- Changing the actual integral marking does not change the normalized class. -/
theorem normalize_independent (e f : G ≃ₗ[ℤ] ℤ) (a : G) : normalize e a = normalize f a := by
  let A := e.symm.trans f
  have hfa : f a = A (e a) := by
    change f a = f (e.symm (e a))
    rw [LinearEquiv.symm_apply_apply]
  apply f.injective
  rw [marking_normalize]
  change A (Int.sign (e a)) = Int.sign (f a)
  rw [hfa, IntLinearAutomorphism.apply_eq_mul A (Int.sign (e a)),
    IntLinearAutomorphism.apply_eq_mul A (e a), Int.sign_mul]
  rcases IntLinearAutomorphism.apply_one_eq_one_or_neg_one A with h | h
  · rw [h, Int.sign_one]
  · rw [h, Int.sign_neg_one]

theorem normalize_eq_sign_smul (e : G ≃ₗ[ℤ] ℤ) (a : G) :
    normalize e a = Int.sign (e a) • e.symm 1 := by
  apply e.injective
  rw [marking_normalize, map_zsmul, LinearEquiv.apply_symm_apply]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

theorem normalize_smul_generator (e : G ≃ₗ[ℤ] ℤ) (k : ℤ) :
    normalize e (k • e.symm 1) = Int.sign k • e.symm 1 := by
  rw [normalize_eq_sign_smul, map_zsmul, LinearEquiv.apply_symm_apply]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

theorem normalize_eq_or_neg (e : G ≃ₗ[ℤ] ℤ) (a : G) (ha : a ≠ 0) :
    normalize e a = e.symm 1 ∨ normalize e a = -e.symm 1 := by
  have hea : e a ≠ 0 := fun he => ha (e.injective (he.trans e.map_zero.symm))
  rcases Int.sign_trichotomy (e a) with h | h | h
  · exact Or.inl (congrArg e.symm h)
  · exact False.elim (hea (Int.eq_zero_of_sign_eq_zero h))
  · exact Or.inr ((congrArg e.symm h).trans (map_neg e.symm 1))

/-- The normalized nonzero direction generates the original integral module. -/
theorem normalize_generates (e : G ≃ₗ[ℤ] ℤ) (a : G) (ha : a ≠ 0) (b : G) :
    ∃ k : ℤ, k • normalize e a = b := by
  rcases normalize_eq_or_neg e a ha with h | h
  · refine ⟨e b, e.injective ?_⟩
    rw [h, map_zsmul, LinearEquiv.apply_symm_apply]
    simp only [zsmul_eq_mul, Int.cast_id, mul_one]
  · refine ⟨-(e b), e.injective ?_⟩
    rw [h, map_zsmul, map_neg, LinearEquiv.apply_symm_apply]
    simp only [zsmul_eq_mul, Int.cast_id, mul_neg, mul_one, neg_neg]

end Wikipedia.HopfProblem.DegreeCollapse.IntegralPrimitiveDirection
