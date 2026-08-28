import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.Ring

/-!
# The square of a six-coefficient exterior two-form

This is an identity in Mathlib's actual exterior algebra over an arbitrary
commutative ring.  The four vectors need not be independent.  In the ordered
pairs `01, 02, 03, 12, 13, 23`, the coefficient of their volume product in the
square is twice the Pfaffian.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The ordered exterior product of four vectors. -/
def volumeProduct (v : Fin 4 → M) : ExteriorAlgebra R M :=
  ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ι R (v 1) *
    ExteriorAlgebra.ι R (v 2) * ExteriorAlgebra.ι R (v 3)

/-- A two-form whose six coefficients are ordered `01, 02, 03, 12, 13, 23`. -/
def sixCoefficientExterior (E : Fin 6 → R) (v : Fin 4 → M) : ExteriorAlgebra R M :=
  E 0 • (ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ι R (v 1)) +
  E 1 • (ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ι R (v 2)) +
  E 2 • (ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ι R (v 3)) +
  E 3 • (ExteriorAlgebra.ι R (v 1) * ExteriorAlgebra.ι R (v 2)) +
  E 4 • (ExteriorAlgebra.ι R (v 1) * ExteriorAlgebra.ι R (v 3)) +
  E 5 • (ExteriorAlgebra.ι R (v 2) * ExteriorAlgebra.ι R (v 3))

private theorem generator_swap (a b : M) :
    ExteriorAlgebra.ι R a * ExteriorAlgebra.ι R b =
      -(ExteriorAlgebra.ι R b * ExteriorAlgebra.ι R a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a b)

private theorem generator_swap_assoc (a b : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R a * (ExteriorAlgebra.ι R b * x) =
      -(ExteriorAlgebra.ι R b * (ExteriorAlgebra.ι R a * x)) := by
  rw [← mul_assoc, generator_swap a b, neg_mul, mul_assoc]

private theorem generator_repeat (a : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R a * (ExteriorAlgebra.ι R a * x) = 0 := by
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- The universal Pfaffian identity in the actual exterior algebra. -/
theorem sixCoefficientExterior_sq (E : Fin 6 → R) (v : Fin 4 → M) :
    sixCoefficientExterior E v * sixCoefficientExterior E v =
      (2 * (E 0 * E 5 - E 1 * E 4 + E 2 * E 3)) • volumeProduct v := by
  simp only [sixCoefficientExterior, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, smul_smul, mul_assoc,
    generator_swap_assoc (v 1) (v 0), generator_swap_assoc (v 2) (v 0),
    generator_swap_assoc (v 3) (v 0), generator_swap_assoc (v 2) (v 1),
    generator_swap_assoc (v 3) (v 1), generator_swap_assoc (v 3) (v 2),
    generator_swap (v 2) (v 1),
    generator_swap (v 3) (v 1), generator_swap (v 3) (v 2),
    generator_repeat, ExteriorAlgebra.ι_sq_zero,
    mul_neg, neg_neg, neg_zero, mul_zero, smul_zero, zero_add, add_zero]
  simp only [volumeProduct, mul_assoc, smul_neg, ← neg_smul, ← add_smul]
  congr 1
  ring

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
