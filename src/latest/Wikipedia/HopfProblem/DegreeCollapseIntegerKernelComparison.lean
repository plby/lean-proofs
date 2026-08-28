import Wikipedia.HopfProblem.DegreeCollapsePrimitiveClassSplit
import Mathlib.Algebra.Group.Int.Units

/-!
# Comparing actual integral functionals from one kernel containment

A functional with a specified value-one class determines every functional
vanishing on its kernel up to an integral scalar. If the second functional
is onto, that scalar is a unit. Thus the two actual kernels agree, without
choosing an orientation or identifying the functionals without their sign.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegerKernelComparison

variable {H : Type*} [AddCommGroup H] [Module ℤ H]
  (p q : H →ₗ[ℤ] ℤ) (a : H) (ha : p a = 1)
  (hker : LinearMap.ker p ≤ LinearMap.ker q)

include ha hker in
theorem functional_eq_mul (x : H) : q x = p x * q a := by
  have hz : q (PrimitiveSplitting.projection p a x) = 0 :=
    hker (PrimitiveSplitting.projection_coordinate p a ha x)
  rw [PrimitiveSplitting.projection_apply, map_sub, map_zsmul] at hz
  exact sub_eq_zero.mp hz

include ha hker in
theorem coefficient_unit (hq : Surjective q) : IsUnit (q a) := by
  obtain ⟨b, hb⟩ := hq 1
  have h : p b * q a = 1 := (functional_eq_mul p q a ha hker b).symm.trans hb
  exact IsUnit.of_mul_eq_one (p b) (by rwa [mul_comm])

include ha hker in
theorem kernel_eq (hq : Surjective q) : LinearMap.ker p = LinearMap.ker q := by
  apply le_antisymm hker
  intro x hx
  change q x = 0 at hx
  change p x = 0
  rw [functional_eq_mul p q a ha hker x] at hx
  exact (mul_eq_zero.mp hx).resolve_right (coefficient_unit p q a ha hker hq).ne_zero

include ha hker in
theorem equal_or_negative (hq : Surjective q) : q = p ∨ q = -p := by
  rcases Int.isUnit_iff.mp (coefficient_unit p q a ha hker hq) with hp | hn
  · left
    ext x
    rw [functional_eq_mul p q a ha hker x, hp, mul_one]
  · right
    ext x
    rw [functional_eq_mul p q a ha hker x, hn, mul_neg_one]
    rfl

theorem kernel_eq_of_surjective (hp : Surjective p) (hq : Surjective q)
    (h : LinearMap.ker p ≤ LinearMap.ker q) : LinearMap.ker p = LinearMap.ker q := by
  obtain ⟨a, ha⟩ := hp 1
  exact kernel_eq p q a ha h hq

end Wikipedia.HopfProblem.DegreeCollapse.IntegerKernelComparison
