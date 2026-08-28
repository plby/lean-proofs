import Wikipedia.HopfProblem.PeriodTorusFundamentalGroup

/-!
# Four ordered coordinates for full-period matrices

The pair `(m,n)` of two-coordinate period vectors is identified with the
four-vector `(m₀,m₁,n₀,n₁)`. The equivalence is linear over an arbitrary
semiring, and its integral and real instances commute with the coordinate
cast from integers to reals in both directions.
-/

namespace Wikipedia.HopfProblem.FullPeriodMatrix

open scoped Matrix

/-- Concatenate the two ordered coordinate pairs into the ordered four-vector. -/
def pairCoordinatesEquiv (R : Type*) [Semiring R] :
    ((Fin 2 → R) × (Fin 2 → R)) ≃ₗ[R] (Fin 4 → R) where
  toFun c := ![c.1 0, c.1 1, c.2 0, c.2 1]
  invFun v := (![v 0, v 1], ![v 2, v 3])
  left_inv c := by ext i <;> fin_cases i <;> rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' c d := by ext i; fin_cases i <;> rfl
  map_smul' a c := by ext i; fin_cases i <;> rfl

@[simp] theorem pairCoordinatesEquiv_apply (R : Type*) [Semiring R]
    (c : (Fin 2 → R) × (Fin 2 → R)) :
    pairCoordinatesEquiv R c = ![c.1 0, c.1 1, c.2 0, c.2 1] := rfl

@[simp] theorem pairCoordinatesEquiv_symm_apply (R : Type*) [Semiring R] (v : Fin 4 → R) :
    (pairCoordinatesEquiv R).symm v = (![v 0, v 1], ![v 2, v 3]) := rfl

/-- The four integral coordinates of the actual ordered period lattice. -/
def integerCoordinatesEquiv : IntegerPeriods ≃ₗ[ℤ] (Fin 4 → ℤ) := pairCoordinatesEquiv ℤ

/-- The corresponding real-coordinate equivalence. -/
def realCoordinatesEquiv : RealPair₂ ≃ₗ[ℝ] (Fin 4 → ℝ) := pairCoordinatesEquiv ℝ

@[simp] theorem integerCoordinatesEquiv_apply (c : IntegerPeriods) :
    integerCoordinatesEquiv c = ![c.1 0, c.1 1, c.2 0, c.2 1] := rfl

@[simp] theorem integerCoordinatesEquiv_symm_apply (v : Fin 4 → ℤ) :
    integerCoordinatesEquiv.symm v = (![v 0, v 1], ![v 2, v 3]) := rfl

@[simp] theorem realCoordinatesEquiv_apply (c : RealPair₂) :
    realCoordinatesEquiv c = ![c.1 0, c.1 1, c.2 0, c.2 1] := rfl

@[simp] theorem realCoordinatesEquiv_symm_apply (v : Fin 4 → ℝ) :
    realCoordinatesEquiv.symm v = (![v 0, v 1], ![v 2, v 3]) := rfl

/-- Concatenating period coordinates commutes with the actual integer-to-real cast. -/
theorem realCoordinatesEquiv_intCast (c : IntegerPeriods) :
    realCoordinatesEquiv ((fun i => (c.1 i : ℝ)), (fun i => (c.2 i : ℝ))) =
      fun k => (integerCoordinatesEquiv c k : ℝ) := by
  ext k
  fin_cases k <;> rfl

/-- Splitting four coordinates likewise commutes with the integer-to-real cast. -/
theorem realCoordinatesEquiv_symm_intCast (v : Fin 4 → ℤ) :
    realCoordinatesEquiv.symm (fun k => (v k : ℝ)) =
      ((fun i => ((integerCoordinatesEquiv.symm v).1 i : ℝ)),
        (fun i => ((integerCoordinatesEquiv.symm v).2 i : ℝ))) := by
  ext i <;> fin_cases i <;> rfl

end Wikipedia.HopfProblem.FullPeriodMatrix
