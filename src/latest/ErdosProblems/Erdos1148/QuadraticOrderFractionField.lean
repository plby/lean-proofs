import ErdosProblems.Erdos1148.FormFractionalIdeal

/-! # The rational quadratic field is the fraction field of its discriminant order -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

theorem exists_int_multiple_mem_quadraticOrder (d : ℤ) (w : QuadraticDiscrAlgebra d) :
    ∃ a : ℤ, a ≠ 0 ∧ (a : QuadraticDiscrAlgebra d) * w ∈ quadraticOrder d := by
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite ℤ⁰
    (![w.re, w.im] : Fin 2 → ℚ)
  obtain ⟨x, hx⟩ := ha 0
  obtain ⟨y, hy⟩ := ha 1
  change (x : ℚ) = (a : ℤ) • w.re at hx
  change (y : ℚ) = (a : ℤ) • w.im at hy
  rw [zsmul_eq_mul] at hx hy
  refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp a.2, ?_⟩
  have heq : ((a : ℤ) : QuadraticDiscrAlgebra d) * w =
      ((x - d * y : ℤ) : QuadraticDiscrAlgebra d) +
        ((2 * y : ℤ) : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d := by
    ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
        quadraticOrderGenerator, zero_mul, mul_zero, add_zero]
      push_cast
      linear_combination -hx
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_add,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
        quadraticOrderGenerator, zero_mul, mul_zero, add_zero, zero_add]
      push_cast
      linear_combination -hy
  rw [heq]
  exact int_combination_mem_quadraticOrder _ _ _

instance quadraticOrder_isFractionRing (d : ℤ) [Fact (¬IsSquare d)] :
    IsFractionRing (quadraticOrder d) (QuadraticDiscrAlgebra d) := by
  apply IsFractionRing.of_field
  intro w
  obtain ⟨a, ha, haw⟩ := exists_int_multiple_mem_quadraticOrder d w
  refine ⟨⟨(a : QuadraticDiscrAlgebra d) * w, haw⟩, (a : quadraticOrder d), ?_⟩
  change w = ((a : QuadraticDiscrAlgebra d) * w) / (a : QuadraticDiscrAlgebra d)
  exact (mul_div_cancel_left₀ w (Int.cast_ne_zero.mpr ha)).symm

instance quadraticDiscrAlgebra_numberField (d : ℤ) [Fact (¬IsSquare d)] :
    NumberField (QuadraticDiscrAlgebra d) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

end Erdos1148.DukeArithmetic
