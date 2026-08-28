import Wikipedia.HopfProblem.PeriodTorusAppellHumbertSemicharacter
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCocycleAlgebra

/-!
# A smooth logarithmic model for every integral alternating form

This model is defined before a type `(1,1)` condition has been proved.
Its logarithmic defect is an actual integer cocycle, and its commutator
has the prescribed sign. No holomorphicity is asserted for this smooth
model.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusAppellHumbert PeriodTorusTypeOneOne
open scoped ContDiff

/-- The strictly upper-triangular part of the marked coefficient pairing. -/
def coordinateUpper (E : Fin 6 → ℤ) (x y : Fin 4 → ℤ) : ℤ :=
  E 0 * x 0 * y 1 + E 1 * x 0 * y 2 + E 2 * x 0 * y 3 +
  E 3 * x 1 * y 2 + E 4 * x 1 * y 3 + E 5 * x 2 * y 3

theorem coordinateUpper_sub_swap (E : Fin 6 → ℤ) (x y : Fin 4 → ℤ) :
    coordinateUpper E x y - coordinateUpper E y x = coordinateForm E x y := by
  simp only [coordinateUpper, coordinateForm_apply, coordinateValue]
  ring

theorem coordinateQuadratic_add_upper (E : Fin 6 → ℤ) (x y : Fin 4 → ℤ) :
    coordinateQuadratic E (x + y) - coordinateQuadratic E x - coordinateQuadratic E y -
      coordinateForm E y x = 2 * coordinateUpper E x y := by
  simp only [coordinateQuadratic, coordinateUpper, coordinateForm_apply, coordinateValue,
    Pi.add_apply]
  ring

/-- Evaluation on two genuine lattice elements agrees with the integer marking. -/
theorem tangentForm_lattice_pair (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) :
    tangentForm p E l m = (coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) : ℝ) := by
  simpa only [periodEquiv_integer_eq_periodVector, p.periodVector_latticeEquiv] using
    tangentForm_integer_periods p E (p.latticeEquiv l) (p.latticeEquiv m)

/-- A real-smooth logarithmic model, with the actual positive lattice translation. -/
def realModelLog (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l : p.lattice) (z : ComplexPlane₂) : ℂ :=
  (Real.pi : ℂ) * I * (coordinateQuadratic E (p.latticeEquiv l) : ℂ) +
    (Real.pi : ℂ) * I * (tangentForm p E z l : ℂ)

def realModelIntegerCocycle (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) : ℤ :=
  coordinateUpper E (p.latticeEquiv l) (p.latticeEquiv m)

@[simp]
theorem realModelLog_zero (p : PeriodDomain) (E : Fin 6 → ℤ) (z : ComplexPlane₂) :
    realModelLog p E 0 z = 0 := by
  simp only [realModelLog, map_zero, coordinateQuadratic_zero, Submodule.coe_zero,
    Complex.ofReal_zero, Int.cast_zero, mul_zero, add_zero]

theorem realModelLog_contDiff (p : PeriodDomain) (E : Fin 6 → ℤ) (l : p.lattice) :
    ContDiff ℝ ∞ (realModelLog p E l) :=
  contDiff_const.add (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp ((tangentForm p E).flip l).toContinuousLinearMap.contDiff))

/-- The actual logarithmic defect, with no regularity or type condition assumed. -/
theorem realModelLog_hasIntegerLogDefect (p : PeriodDomain) (E : Fin 6 → ℤ) :
    HasIntegerLogDefect p (realModelLog p E) (realModelIntegerCocycle p E) := by
  intro l m z
  have hq := coordinateQuadratic_add_upper E (p.latticeEquiv l) (p.latticeEquiv m)
  have hqC :
      (coordinateQuadratic E (p.latticeEquiv l + p.latticeEquiv m) : ℂ) -
        (coordinateQuadratic E (p.latticeEquiv l) : ℂ) -
        (coordinateQuadratic E (p.latticeEquiv m) : ℂ) -
        (coordinateForm E (p.latticeEquiv m) (p.latticeEquiv l) : ℂ) =
      2 * (coordinateUpper E (p.latticeEquiv l) (p.latticeEquiv m) : ℂ) := by
    exact_mod_cast hq
  simp only [realModelLog, realModelIntegerCocycle, map_add, Submodule.coe_add,
    LinearMap.add_apply, tangentForm_lattice_pair, Complex.ofReal_add,
    Complex.ofReal_intCast]
  linear_combination (Real.pi : ℂ) * I * hqC

theorem realModelIntegerCocycle_commutator (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) :
    integerLogCommutator (realModelIntegerCocycle p E) l m =
      coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) :=
  coordinateUpper_sub_swap E _ _

@[simp]
theorem realModelLog_alternatingForm (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) :
    integerLogAlternatingForm (realModelLog_hasIntegerLogDefect p E) l m =
      coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) :=
  realModelIntegerCocycle_commutator p E l m

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
