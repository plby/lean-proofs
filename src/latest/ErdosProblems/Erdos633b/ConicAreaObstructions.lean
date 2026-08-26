import ErdosProblems.Erdos633b.ConicBoundaryObstructions

/-! The shared-angle area obstruction for the third group-2 shape,
and the cubic boundary obstruction for the doubled shape. -/

namespace Erdos633b

theorem conic_third_shape_obstruction (x y : ℝ) (m : Fin 3 → Fin 3 → ℕ) (n : ℕ)
    (hpos : 0 < conicBoundaryRow (m 1) x y)
    (hX : conicBoundaryRow (m 0) x y = x * conicBoundaryRow (m 1) x y)
    (hZ : conicBoundaryRow (m 2) x y = conicBoundaryRow (m 1) x y * (x + y))
    (harea : (n : ℝ) * y = conicBoundaryRow (m 1) x y * conicBoundaryRow (m 2) x y)
    (hi : QuadraticConicIndependent x y) : False := by
  let a : Fin 5 → ℚ := ![-(m 0 2 : ℚ), (m 1 2 : ℚ) - m 0 0,
    -(m 0 1 : ℚ), (m 1 0 : ℚ), (m 1 1 : ℚ)]
  have ha : (a 0 : ℝ) + a 1 * x + a 2 * y + a 3 * x ^ 2 + a 4 * x * y = 0 := by
    dsimp [a]
    push_cast
    dsimp only [conicBoundaryRow] at hX
    linear_combination -hX
  have hz := hi a ha
  have hp : m 1 0 = 0 := by exact_mod_cast (show (m 1 0 : ℚ) = 0 from hz 3)
  have hq : m 1 1 = 0 := by exact_mod_cast (show (m 1 1 : ℚ) = 0 from hz 4)
  simp only [conicBoundaryRow, hp, hq, Nat.cast_zero, zero_mul, zero_add] at hpos hZ harea
  rw [hZ] at harea
  let b : Fin 5 → ℚ := ![0, -(m 1 2 : ℚ) ^ 2, (n : ℚ) - (m 1 2 : ℚ) ^ 2, 0, 0]
  have hb : (b 0 : ℝ) + b 1 * x + b 2 * y + b 3 * x ^ 2 + b 4 * x * y = 0 := by
    dsimp [b]
    push_cast
    linear_combination harea
  have hh : -(m 1 2 : ℚ) ^ 2 = 0 := hi b hb 1
  have hr : m 1 2 = 0 := by
    exact_mod_cast (sq_eq_zero_iff.mp (neg_eq_zero.mp hh))
  simp only [hr, Nat.cast_zero, lt_self_iff_false] at hpos

theorem conic_fourth_shape_obstruction (x y : ℝ) (hc : x ^ 2 + x * y + y ^ 2 = 1)
    (m : Fin 3 → Fin 3 → ℕ) (hpos : 0 < conicBoundaryRow (m 2) x y)
    (hX : conicBoundaryRow (m 0) x y = conicBoundaryRow (m 2) x y * x * (x + 2 * y))
    (hi : CubicConicIndependent x y) : False := by
  let a : Fin 7 → ℚ := ![-(m 0 2 : ℚ), 2 * (m 2 1 : ℚ) - m 0 0, -(m 0 1 : ℚ),
    (m 2 2 : ℚ), 2 * (m 2 2 : ℚ), (m 2 0 : ℚ) - 2 * m 2 1,
    2 * (m 2 0 : ℚ) - m 2 1]
  have ha : (a 0 : ℝ) + a 1 * x + a 2 * y + a 3 * x ^ 2 + a 4 * x * y +
      a 5 * x ^ 3 + a 6 * x ^ 2 * y = 0 := by
    dsimp [a]
    push_cast
    dsimp only [conicBoundaryRow] at hX
    linear_combination -hX - 2 * (m 2 1 : ℝ) * x * hc
  have hz := hi a ha
  have h5 : (m 2 0 : ℚ) - 2 * m 2 1 = 0 := hz 5
  have h6 : 2 * (m 2 0 : ℚ) - m 2 1 = 0 := hz 6
  have hp : m 2 0 = 0 := by exact_mod_cast (show (m 2 0 : ℚ) = 0 by linarith)
  have hq : m 2 1 = 0 := by exact_mod_cast (show (m 2 1 : ℚ) = 0 by linarith)
  have hr : m 2 2 = 0 := by exact_mod_cast (show (m 2 2 : ℚ) = 0 from hz 3)
  simp only [conicBoundaryRow, hp, hq, hr, Nat.cast_zero, zero_mul, zero_add] at hpos
  exact (lt_irrefl 0) hpos

end Erdos633b
