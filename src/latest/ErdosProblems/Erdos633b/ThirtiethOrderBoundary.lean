import ErdosProblems.Erdos633b.GroupOneBoundaryQuartic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! Exact exclusion of the thirtieth-order sine parameter by cubic
independence and the two nonnegative boundary equations. -/

namespace Erdos633b
open Polynomial

theorem chebyshev_C_five : Chebyshev.C ℝ 5 = X ^ 5 - 5 * X ^ 3 + 5 * X := by
  rw [show Chebyshev.C ℝ 5 = X * Chebyshev.C ℝ 4 - Chebyshev.C ℝ 3 from
    Chebyshev.C_add_two ℝ 3]
  rw [show Chebyshev.C ℝ 4 = X * Chebyshev.C ℝ 3 - Chebyshev.C ℝ 2 from
    Chebyshev.C_add_two ℝ 2]
  rw [show Chebyshev.C ℝ 3 = X * Chebyshev.C ℝ 2 - Chebyshev.C ℝ 1 from
    Chebyshev.C_add_two ℝ 1]
  rw [show Chebyshev.C ℝ 2 = X * Chebyshev.C ℝ 1 - Chebyshev.C ℝ 0 from
    Chebyshev.C_add_two ℝ 0, Chebyshev.C_one, Chebyshev.C_zero]
  ring

theorem thirtieth_cosine_quartic (s : ℝ)
    (he : s = 2 * Real.cos (2 * Real.pi * 7 / 30)) (hs : s < 1) :
    s ^ 4 + s ^ 3 - 4 * s ^ 2 - 4 * s + 1 = 0 := by
  have hh := Chebyshev.C_two_mul_real_cos (2 * Real.pi * 7 / 30) (5 : ℤ)
  rw [chebyshev_C_five, ← he] at hh
  have ht : (5 : ℝ) * (2 * Real.pi * 7 / 30) = Real.pi / 3 + 2 * Real.pi := by ring
  norm_num only [Int.cast_ofNat, eval_add, eval_sub, eval_mul, eval_pow, eval_X,
    eval_ofNat] at hh
  rw [ht, Real.cos_add_two_pi, Real.cos_pi_div_three] at hh
  have hf : (s - 1) * (s ^ 4 + s ^ 3 - 4 * s ^ 2 - 4 * s + 1) = 0 := by
    linear_combination hh
  exact (mul_eq_zero.mp hf).resolve_left (by linarith)

theorem thirtieth_boundary_impossible (m : Fin 3 → Fin 3 → ℕ) (s : ℝ)
    (he : s = 2 * Real.cos (2 * Real.pi * 7 / 30)) (hs : s < 1)
    (hpos : 0 < groupOneBoundaryRow (m 0) s)
    (hY : groupOneBoundaryRow (m 1) s = groupOneBoundaryRow (m 0) s * (2 - s ^ 2))
    (hZ : groupOneBoundaryRow (m 2) s =
      groupOneBoundaryRow (m 0) s * (1 - s ^ 2) * (3 - s ^ 2)) : False := by
  have hquart := thirtieth_cosine_quartic s he hs
  have hf := groupOne_first_quartic m s hY
  dsimp [groupOneFirstCoeffs] at hf
  push_cast at hf
  let b : Fin 4 → ℚ := ![(m 0 1 : ℚ) + 2 * m 0 2 - m 1 1 - m 1 2,
    2 * (m 0 0 : ℚ) - m 1 0 + 4 * m 0 1,
    (m 1 1 : ℚ) + m 0 1 - m 0 2, -(m 0 0 : ℚ) - m 0 1]
  have hb : (b 0 : ℝ) + b 1 * s + b 2 * s ^ 2 + b 3 * s ^ 3 = 0 := by
    dsimp [b]
    push_cast
    linear_combination hf - (m 0 1 : ℝ) * hquart
  rw [he] at hb
  have hb0 := cubic_cosine_independent 30 7 (by decide) (by decide) (by decide) b hb 3
  have hn : m 0 0 + m 0 1 = 0 := by
    have hq : (m 0 0 : ℚ) + m 0 1 = 0 := by
      dsimp [b] at hb0
      linarith
    exact_mod_cast hq
  have hp : m 0 0 = 0 := by omega
  have hq : m 0 1 = 0 := by omega
  have hg := groupOne_second_quartic m s hp hq hZ
  dsimp [groupOneSecondCoeffs] at hg
  push_cast at hg
  let c : Fin 4 → ℚ := ![2 * (m 0 2 : ℚ) - m 2 1 - m 2 2,
    -(m 2 0 : ℚ) + 4 * m 0 2, (m 2 1 : ℚ), -(m 0 2 : ℚ)]
  have hc : (c 0 : ℝ) + c 1 * s + c 2 * s ^ 2 + c 3 * s ^ 3 = 0 := by
    dsimp [c]
    push_cast
    linear_combination hg - (m 0 2 : ℝ) * hquart
  rw [he] at hc
  have hc0 := cubic_cosine_independent 30 7 (by decide) (by decide) (by decide) c hc 3
  have hr : m 0 2 = 0 := by simpa [c] using hc0
  simp only [groupOneBoundaryRow, hp, hq, hr, Nat.cast_zero, zero_mul, zero_add] at hpos
  exact (lt_irrefl 0) hpos

namespace Tiling

theorem groupOne_first_not_thirtieth {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) : d.tile.angle 0 ≠ 2 * Real.pi / 30 := by
  intro ha
  have hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi := by
    have ht := T.angle_sum
    rw [h0, h1, h2] at ht
    linarith
  obtain ⟨hY, hZ⟩ := d.groupOne_first_boundary_equations h0 h1 h2
  apply thirtieth_boundary_impossible d.boundarySideCount
    (2 * Real.sin (d.tile.angle 0 / 2)) _ (d.tile.groupOne_parameter_bounds hrel).2 _ hY hZ
  · rw [ha, ← Real.cos_pi_div_two_sub]
    congr 2
    ring
  · rw [← d.groupOne_normalized_boundary hrel 0]
    exact div_pos (T.side_pos 0) (d.tile.side_pos 2)

end Tiling
end Erdos633b
