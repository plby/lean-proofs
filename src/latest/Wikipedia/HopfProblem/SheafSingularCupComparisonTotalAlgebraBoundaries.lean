import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalAlgebraLeibniz

/-!
# Literal primitives for products with total coboundaries

The primitives use the front or back degree-zero cofaces in each
direction. The mixed identities are actual ring computations using the
commuting square at `(0,0)`. A cocycle in the other argument therefore
makes each product with a coboundary an actual total coboundary.
-/

universe u

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
  [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

def leftPrimitive (r : R00) (a : D.One) : D.One :=
  (D.v00 1 r * a.1, D.h00 1 r * a.2)

def rightPrimitive (a : D.One) (r : R00) : D.One :=
  (-(a.1 * D.v00 0 r), -(a.2 * D.h00 0 r))

def leftWeight (r : R00) : D.Two :=
  (D.v10 2 (D.v00 1 r), D.h10 1 (D.v00 1 r), D.h01 2 (D.h00 1 r))

def rightWeight (r : R00) : D.Two :=
  (D.v10 0 (D.v00 0 r), D.h10 0 (D.v00 0 r), D.h01 0 (D.h00 0 r))

theorem d1_leftPrimitive11 (r : R00) (a : D.One) :
    (D.d1 (D.leftPrimitive r a)).2.1 =
      (D.cupOne (D.d0 r) a + D.leftWeight r * D.d1 a).2.1 := by
  change -D.dh10 (D.v00 1 r * a.1) + D.dv01 (D.h00 1 r * a.2) =
    (D.h10 1 (D.dv00 r) * D.v01 0 a.2 - D.v01 1 (D.dh00 r) * D.h10 0 a.1) +
      D.h10 1 (D.v00 1 r) * (-D.dh10 a.1 + D.dv01 a.2)
  simp only [dh10, dv01, dv00, dh00, alternating0_apply, map_mul, map_sub]
  simp only [D.mixed00_apply]
  ring

/-- The exact total identity for a front-vertex degree-zero factor. -/
theorem d1_leftPrimitive (r : R00) (a : D.One) :
    D.d1 (D.leftPrimitive r a) = D.cupOne (D.d0 r) a + D.leftWeight r * D.d1 a := by
  apply Prod.ext
  · exact D.vertical.d1_leftPrimitive r a.1
  · apply Prod.ext
    · exact D.d1_leftPrimitive11 r a
    · exact D.horizontal.d1_leftPrimitive r a.2

theorem d1_rightPrimitive11 (a : D.One) (r : R00) :
    (D.d1 (D.rightPrimitive a r)).2.1 =
      (D.cupOne a (D.d0 r) - D.d1 a * D.rightWeight r).2.1 := by
  change -D.dh10 (-(a.1 * D.v00 0 r)) + D.dv01 (-(a.2 * D.h00 0 r)) =
    (D.h10 1 a.1 * D.v01 0 (D.dh00 r) - D.v01 1 a.2 * D.h10 0 (D.dv00 r)) -
      (-D.dh10 a.1 + D.dv01 a.2) * D.h10 0 (D.v00 0 r)
  simp only [dh10, dv01, dv00, dh00, alternating0_apply, map_mul, map_sub, map_neg]
  simp only [D.mixed00_apply]
  ring

/-- The exact total identity with the degree-one sign in the primitive. -/
theorem d1_rightPrimitive (a : D.One) (r : R00) :
    D.d1 (D.rightPrimitive a r) = D.cupOne a (D.d0 r) - D.d1 a * D.rightWeight r := by
  apply Prod.ext
  · exact D.vertical.d1_rightPrimitive a.1 r
  · apply Prod.ext
    · exact D.d1_rightPrimitive11 a r
    · exact D.horizontal.d1_rightPrimitive a.2 r

theorem cupOne_d0_left (r : R00) {a : D.One} (ha : D.d1 a = 0) :
    D.cupOne (D.d0 r) a = D.d1 (D.leftPrimitive r a) := by
  have h := D.d1_leftPrimitive r a
  rw [ha, mul_zero, add_zero] at h
  exact h.symm

theorem cupOne_d0_right {a : D.One} (ha : D.d1 a = 0) (r : R00) :
    D.cupOne a (D.d0 r) = D.d1 (D.rightPrimitive a r) := by
  have h := D.d1_rightPrimitive a r
  rw [ha, zero_mul, sub_zero] at h
  exact h.symm

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data
