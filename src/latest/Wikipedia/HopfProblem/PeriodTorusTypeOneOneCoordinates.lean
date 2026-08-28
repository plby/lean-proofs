import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Genuine alternating forms in the six source coordinates

The coordinates are `γu, γw, γδ, uw, uδ, wδ`. They define an actual
bilinear alternating form on the four-dimensional coefficient module,
over any commutative ring. In particular integral coefficients define
an integral alternating form, not an asserted cohomology class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

variable {R : Type*} [CommRing R]

/-- Evaluation of the six genuine exterior-pair coefficients. -/
def coordinateValue (E : Fin 6 → R) (x y : Fin 4 → R) : R :=
  E 0 * (x 0 * y 1 - x 1 * y 0) +
  E 1 * (x 0 * y 2 - x 2 * y 0) +
  E 2 * (x 0 * y 3 - x 3 * y 0) +
  E 3 * (x 1 * y 2 - x 2 * y 1) +
  E 4 * (x 1 * y 3 - x 3 * y 1) +
  E 5 * (x 2 * y 3 - x 3 * y 2)

/-- The actual bilinear form determined by those coefficients. -/
def coordinateForm (E : Fin 6 → R) : LinearMap.BilinForm R (Fin 4 → R) :=
  LinearMap.mk₂ R (coordinateValue E)
    (by intros; simp only [coordinateValue, Pi.add_apply]; ring)
    (by intros; simp only [coordinateValue, Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [coordinateValue, Pi.add_apply]; ring)
    (by intros; simp only [coordinateValue, Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem coordinateForm_apply (E : Fin 6 → R) (x y : Fin 4 → R) :
    coordinateForm E x y = coordinateValue E x y := rfl

theorem coordinateForm_self (E : Fin 6 → R) (x : Fin 4 → R) :
    coordinateForm E x x = 0 := by
  simp only [coordinateForm_apply, coordinateValue]
  ring

theorem coordinateForm_swap (E : Fin 6 → R) (x y : Fin 4 → R) :
    coordinateForm E x y = -coordinateForm E y x := by
  simp only [coordinateForm_apply, coordinateValue]
  ring

/-- Ordered pairs underlying the source's six-coordinate convention. -/
def coefficientPair : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- Each displayed coefficient is exactly evaluation on its named lattice basis pair. -/
theorem coordinateForm_basis_pair (E : Fin 6 → R) (k : Fin 6) :
    coordinateForm E (Pi.single (coefficientPair k).1 1)
      (Pi.single (coefficientPair k).2 1) = E k := by
  fin_cases k <;> simp [coordinateForm_apply, coordinateValue, coefficientPair]

theorem coordinateForm_smul (r : R) (E : Fin 6 → R) :
    coordinateForm (r • E) = r • coordinateForm E := by
  ext x y
  simp only [coordinateForm_apply, coordinateValue, Pi.smul_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
