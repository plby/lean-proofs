import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalAlgebraComplex
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalAlgebraProduct

/-!
# The actual Leibniz identity for the signed total cup product

The two mixed components are proved by expanding the literal ring
cofaces, commuting the mixed squares, and applying the ordinary coface
relations. The pure components are the already proved one-directional
Alexander--Whitney identities. Thus cocycle closure is a theorem.
-/

universe u

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
  [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

theorem d2_cupOne21 (a b : D.One) :
    (D.d2 (D.cupOne a b)).2.1 =
      (D.cupTwoOne (D.d1 a) b - D.cupOneTwo a (D.d1 b)).2.1 := by
  change D.dh20 (D.v10 2 a.1 * D.v10 0 b.1) +
      D.dv11 (D.h10 1 a.1 * D.v01 0 b.2 - D.v01 1 a.2 * D.h10 0 b.1) =
    (D.h20 1 (D.dv10 a.1) * D.v11 0 (D.v01 0 b.2) -
      D.v11 2 (-D.dh10 a.1 + D.dv01 a.2) * D.h20 0 (D.v10 0 b.1)) -
    (D.h20 1 (D.v10 2 a.1) * D.v11 0 (-D.dh10 b.1 + D.dv01 b.2) +
      D.v11 2 (D.v01 1 a.2) * D.h20 0 (D.dv10 b.1))
  simp only [dh20, dv11, dv10, dh10, dv01, alternating0_apply, alternating1_apply,
    map_add, map_sub, map_mul, map_neg]
  simp only [D.mixed10_apply, D.cofaceV01.low00, D.cofaceV01.low01, D.cofaceV01.low11]
  ring

theorem d2_cupOne12 (a b : D.One) :
    (D.d2 (D.cupOne a b)).2.2.1 =
      (D.cupTwoOne (D.d1 a) b - D.cupOneTwo a (D.d1 b)).2.2.1 := by
  change -D.dh11 (D.h10 1 a.1 * D.v01 0 b.2 - D.v01 1 a.2 * D.h10 0 b.1) +
      D.dv02 (D.h01 2 a.2 * D.h01 0 b.2) =
    (D.h11 2 (-D.dh10 a.1 + D.dv01 a.2) * D.v02 0 (D.h01 0 b.2) +
      D.v02 1 (D.dh01 a.2) * D.h11 0 (D.h10 0 b.1)) -
    (D.h11 2 (D.h10 1 a.1) * D.v02 0 (D.dh01 b.2) -
      D.v02 1 (D.h01 2 a.2) * D.h11 0 (-D.dh10 b.1 + D.dv01 b.2))
  simp only [dh11, dv02, dh10, dv01, dh01, alternating0_apply, alternating1_apply,
    map_add, map_sub, map_mul, map_neg]
  simp only [D.mixed01_apply, D.cofaceH10.low00, D.cofaceH10.low01, D.cofaceH10.low11]
  ring

/-- The actual Leibniz identity for the total Alexander--Whitney product. -/
theorem d2_cupOne (a b : D.One) :
    D.d2 (D.cupOne a b) = D.cupTwoOne (D.d1 a) b - D.cupOneTwo a (D.d1 b) := by
  apply Prod.ext
  · exact D.vertical.d2_cupOne a.1 b.1
  · apply Prod.ext
    · exact D.d2_cupOne21 a b
    · apply Prod.ext
      · exact D.d2_cupOne12 a b
      · exact D.horizontal.d2_cupOne a.2 b.2

/-- The literal total product of two genuine degree-one cocycles is a cocycle. -/
theorem cupOne_isCocycle {a b : D.One} (ha : D.d1 a = 0) (hb : D.d1 b = 0) :
    D.d2 (D.cupOne a b) = 0 := by
  rw [D.d2_cupOne, ha, hb, D.cupTwoOne_zero_left, D.cupOneTwo_zero_right, sub_self]

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data
