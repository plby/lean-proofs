import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraClosed

/-!
# Literal primitives for products with total coboundaries

The two primitives are actual zero--one multiplication, with the
negative sign for the right incoming boundary. Their differential is
computed from the original derivation and coface formulas.
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : Data R0 R1 R2 R3)

theorem left_mixed_boundary (j : Fin 2) (u : R0) {a : R1} {b : R0}
    (h : D.deriv1 j a = D.cofaces.d0 b) :
    -D.deriv1 j (D.cofaces.leftPrimitive u a) + D.cofaces.d0 (u * b) =
      D.mixedCup (D.cofaces.d0 u) (D.deriv0 j u) a b := by
  simp only [SheafCupProduct.Coface.Data.leftPrimitive, D.leibniz1, D.coface0, h,
    mixedCup, SheafCupProduct.Coface.Data.d0_apply, map_mul]
  ring

theorem right_mixed_boundary (j : Fin 2) (u : R0) {a : R1} {b : R0}
    (h : D.deriv1 j a = D.cofaces.d0 b) :
    -D.deriv1 j (D.cofaces.rightPrimitive a u) + D.cofaces.d0 (-(b * u)) =
      D.mixedCup a b (D.cofaces.d0 u) (D.deriv0 j u) := by
  simp only [SheafCupProduct.Coface.Data.rightPrimitive, map_neg, D.leibniz1,
    D.coface0, h, mixedCup, SheafCupProduct.Coface.Data.d0_apply, map_mul]
  ring

theorem left_horizontal_boundary (u : R0) (b : R0 × R0)
    (hb : D.deriv0 0 b.2 = D.deriv0 1 b.1) :
    D.curl0 (u * b.1, u * b.2) = D.wedge (D.gradient0 u) b := by
  simp only [curl_apply, wedge, gradient_apply, D.leibniz0, hb]
  ring

theorem right_horizontal_boundary (u : R0) (b : R0 × R0)
    (hb : D.deriv0 0 b.2 = D.deriv0 1 b.1) :
    D.curl0 (-(b.1 * u), -(b.2 * u)) = D.wedge b (D.gradient0 u) := by
  simp only [curl_apply, wedge, gradient_apply, map_neg, D.leibniz0, hb]
  ring

/-- An incoming boundary on the left has the literal left multiplication primitive. -/
theorem cupOne_d0_left (u : R0) {x : D.One} (hx : D.d1 x = 0) :
    D.cupOne (D.d0 u) x = D.d1 (D.leftPrimitive u x) := by
  apply Prod.ext
  · exact D.cofaces.cupOne_d0_left u (D.closed_vertical hx)
  · apply Prod.ext
    · apply Prod.ext
      · exact (D.left_mixed_boundary 0 u (D.closed_mixed0 hx)).symm
      · exact (D.left_mixed_boundary 1 u (D.closed_mixed1 hx)).symm
    · exact (D.left_horizontal_boundary u x.2 (D.closed_horizontal_eq hx)).symm

/-- An incoming boundary on the right has the literal negative right multiplication primitive. -/
theorem cupOne_d0_right {x : D.One} (hx : D.d1 x = 0) (u : R0) :
    D.cupOne x (D.d0 u) = D.d1 (D.rightPrimitive x u) := by
  apply Prod.ext
  · exact D.cofaces.cupOne_d0_right (D.closed_vertical hx) u
  · apply Prod.ext
    · apply Prod.ext
      · exact (D.right_mixed_boundary 0 u (D.closed_mixed0 hx)).symm
      · exact (D.right_mixed_boundary 1 u (D.closed_mixed1 hx)).symm
    · exact (D.right_horizontal_boundary u x.2 (D.closed_horizontal_eq hx)).symm

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data
