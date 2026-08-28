import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalAlgebraBasic

/-!
# Literal low-degree Alexander--Whitney products in the total ring complex

The sign in the mixed component is the Koszul sign from interchanging
the horizontal degree of the first factor with the vertical degree of
the second. The degree `(2,1)` and `(1,2)` formulas are used to prove the
actual Leibniz identity for the degree-one product.
-/

universe u

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
  [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

/-- The actual signed total Alexander--Whitney product of degree-one cochains. -/
def cupOne (a b : R10 × R01) : R20 × R11 × R02 :=
  (D.v10 2 a.1 * D.v10 0 b.1,
    D.h10 1 a.1 * D.v01 0 b.2 - D.v01 1 a.2 * D.h10 0 b.1,
    D.h01 2 a.2 * D.h01 0 b.2)

/-- The literal degree `(2,1)` product occurring in the Leibniz identity. -/
def cupTwoOne (c : R20 × R11 × R02) (a : R10 × R01) : R30 × R21 × R12 × R03 :=
  (D.v20 3 c.1 * D.v20 0 (D.v10 0 a.1),
    D.h20 1 c.1 * D.v11 0 (D.v01 0 a.2) -
      D.v11 2 c.2.1 * D.h20 0 (D.v10 0 a.1),
    D.h11 2 c.2.1 * D.v02 0 (D.h01 0 a.2) +
      D.v02 1 c.2.2 * D.h11 0 (D.h10 0 a.1),
    D.h02 3 c.2.2 * D.h02 0 (D.h01 0 a.2))

/-- The literal degree `(1,2)` product occurring in the Leibniz identity. -/
def cupOneTwo (a : R10 × R01) (c : R20 × R11 × R02) : R30 × R21 × R12 × R03 :=
  (D.v20 3 (D.v10 2 a.1) * D.v20 0 c.1,
    D.h20 1 (D.v10 2 a.1) * D.v11 0 c.2.1 +
      D.v11 2 (D.v01 1 a.2) * D.h20 0 c.1,
    D.h11 2 (D.h10 1 a.1) * D.v02 0 c.2.2 -
      D.v02 1 (D.h01 2 a.2) * D.h11 0 c.2.1,
    D.h02 3 (D.h01 2 a.2) * D.h02 0 c.2.2)

@[simp] theorem cupOne_zero_left (a : R10 × R01) : D.cupOne 0 a = 0 := by
  simp [cupOne]

@[simp] theorem cupOne_zero_right (a : R10 × R01) : D.cupOne a 0 = 0 := by
  simp [cupOne]

theorem cupOne_add_left (a b c : R10 × R01) :
    D.cupOne (a + b) c = D.cupOne a c + D.cupOne b c := by
  apply Prod.ext
  · simp only [cupOne, Prod.fst_add, map_add, add_mul]
  · apply Prod.ext
    · simp only [cupOne, Prod.fst_add, Prod.snd_add, map_add, add_mul]
      ring
    · simp only [cupOne, Prod.fst_add, Prod.snd_add, map_add, add_mul]

theorem cupOne_add_right (a b c : R10 × R01) :
    D.cupOne a (b + c) = D.cupOne a b + D.cupOne a c := by
  apply Prod.ext
  · simp only [cupOne, Prod.fst_add, map_add, mul_add]
  · apply Prod.ext
    · simp only [cupOne, Prod.fst_add, Prod.snd_add, map_add, mul_add]
      ring
    · simp only [cupOne, Prod.fst_add, Prod.snd_add, map_add, mul_add]

@[simp] theorem cupTwoOne_zero_left (a : R10 × R01) : D.cupTwoOne 0 a = 0 := by
  simp [cupTwoOne]

@[simp] theorem cupOneTwo_zero_right (a : R10 × R01) : D.cupOneTwo a 0 = 0 := by
  simp [cupOneTwo]

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data
