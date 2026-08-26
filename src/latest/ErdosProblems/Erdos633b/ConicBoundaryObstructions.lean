import ErdosProblems.Erdos633b.ConicIndependence

/-! Nonnegative actual boundary rows are incompatible with quadratic
conic independence in the first two group-2 shapes. -/

namespace Erdos633b

noncomputable def conicBoundaryRow (m : Fin 3 → ℕ) (x y : ℝ) : ℝ :=
  (m 0 : ℝ) * x + m 1 * y + m 2

theorem conic_first_shape_obstruction (x y : ℝ) (hc : x ^ 2 + x * y + y ^ 2 = 1)
    (m : Fin 3 → Fin 3 → ℕ) (hpos : 0 < conicBoundaryRow (m 0) x y)
    (hY : conicBoundaryRow (m 1) x y = conicBoundaryRow (m 0) x y * (x + 2 * y))
    (hZ : conicBoundaryRow (m 2) x y = 3 * conicBoundaryRow (m 0) x y * (1 - x ^ 2))
    (hi : QuadraticConicIndependent x y) : False := by
  let a : Fin 5 → ℚ := ![2 * (m 0 1 : ℚ) - m 1 2, (m 0 2 : ℚ) - m 1 0,
    2 * (m 0 2 : ℚ) - m 1 1, (m 0 0 : ℚ) - 2 * m 0 1, 2 * (m 0 0 : ℚ) - m 0 1]
  have ha : (a 0 : ℝ) + a 1 * x + a 2 * y + a 3 * x ^ 2 + a 4 * x * y = 0 := by
    dsimp [a]
    push_cast
    dsimp only [conicBoundaryRow] at hY
    linear_combination -hY - 2 * (m 0 1 : ℝ) * hc
  have hz := hi a ha
  have h3 : (m 0 0 : ℚ) - 2 * m 0 1 = 0 := hz 3
  have h4 : 2 * (m 0 0 : ℚ) - m 0 1 = 0 := hz 4
  have hp : m 0 0 = 0 := by exact_mod_cast (show (m 0 0 : ℚ) = 0 by linarith)
  have hq : m 0 1 = 0 := by exact_mod_cast (show (m 0 1 : ℚ) = 0 by linarith)
  simp only [conicBoundaryRow, hp, hq, Nat.cast_zero, zero_mul, zero_add] at hZ hpos
  let b : Fin 5 → ℚ := ![3 * (m 0 2 : ℚ) - m 2 2, -(m 2 0 : ℚ),
    -(m 2 1 : ℚ), -3 * (m 0 2 : ℚ), 0]
  have hb : (b 0 : ℝ) + b 1 * x + b 2 * y + b 3 * x ^ 2 + b 4 * x * y = 0 := by
    dsimp [b]
    push_cast
    linear_combination -hZ
  have hh : -3 * (m 0 2 : ℚ) = 0 := hi b hb 3
  have hr : m 0 2 = 0 := by exact_mod_cast (show (m 0 2 : ℚ) = 0 by linarith)
  simp only [hr, Nat.cast_zero, lt_self_iff_false] at hpos

theorem conic_second_shape_obstruction (x y : ℝ) (hx : 0 < x)
    (hc : x ^ 2 + x * y + y ^ 2 = 1)
    (m : Fin 3 → Fin 3 → ℕ) (hpos : 0 < conicBoundaryRow (m 0) x y)
    (hY : x * conicBoundaryRow (m 1) x y =
      y * (2 * x + y) * conicBoundaryRow (m 0) x y)
    (hZ : x * conicBoundaryRow (m 2) x y = (x + y) * conicBoundaryRow (m 0) x y)
    (hi : QuadraticConicIndependent x y) : False := by
  let a : Fin 5 → ℚ := ![(m 0 1 : ℚ), (m 0 2 : ℚ) - m 2 2, (m 0 2 : ℚ),
    (m 0 0 : ℚ) - m 0 1 - m 2 0, (m 0 0 : ℚ) - m 2 1]
  have ha : (a 0 : ℝ) + a 1 * x + a 2 * y + a 3 * x ^ 2 + a 4 * x * y = 0 := by
    dsimp [a]
    push_cast
    dsimp only [conicBoundaryRow] at hZ
    linear_combination -hZ - (m 0 1 : ℝ) * hc
  have hz := hi a ha
  have hq : m 0 1 = 0 := by exact_mod_cast (show (m 0 1 : ℚ) = 0 from hz 0)
  have hr : m 0 2 = 0 := by exact_mod_cast (show (m 0 2 : ℚ) = 0 from hz 2)
  have hp : m 0 0 ≠ 0 := by
    intro hp
    simp only [conicBoundaryRow, hp, hq, hr, Nat.cast_zero, zero_mul, zero_add] at hpos
    exact (lt_irrefl 0) hpos
  simp only [conicBoundaryRow, hq, hr, Nat.cast_zero, zero_mul, add_zero] at hY
  have hV : conicBoundaryRow (m 1) x y = (m 0 0 : ℝ) * (1 - x ^ 2 + x * y) := by
    apply mul_left_cancel₀ hx.ne'
    dsimp only [conicBoundaryRow]
    linear_combination hY + (m 0 0 : ℝ) * x * hc
  let b : Fin 5 → ℚ := ![(m 0 0 : ℚ) - m 1 2, -(m 1 0 : ℚ), -(m 1 1 : ℚ),
    -(m 0 0 : ℚ), (m 0 0 : ℚ)]
  have hb : (b 0 : ℝ) + b 1 * x + b 2 * y + b 3 * x ^ 2 + b 4 * x * y = 0 := by
    dsimp [b]
    push_cast
    dsimp only [conicBoundaryRow] at hV
    linear_combination -hV
  have hh : -(m 0 0 : ℚ) = 0 := hi b hb 3
  exact hp (by simpa using hh)

namespace Tiling

theorem conic_normalized_boundary {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    T.side i / d.tile.side 2 = conicBoundaryRow (d.boundarySideCount i)
      (d.tile.side 0 / d.tile.side 2) (d.tile.side 1 / d.tile.side 2) := by
  rw [d.side_eq_three_counts i, add_div, add_div, mul_div_assoc, mul_div_assoc,
    mul_div_assoc, div_self (d.tile.side_pos 2).ne', mul_one]
  rfl

theorem conic_boundary_row_pos {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    0 < conicBoundaryRow (d.boundarySideCount i)
      (d.tile.side 0 / d.tile.side 2) (d.tile.side 1 / d.tile.side 2) := by
  rw [← d.conic_normalized_boundary]
  exact div_pos (T.side_pos i) (d.tile.side_pos 2)

end Tiling
end Erdos633b
