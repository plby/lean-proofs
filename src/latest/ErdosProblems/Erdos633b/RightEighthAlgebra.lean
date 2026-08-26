import ErdosProblems.Erdos633b.RightTileQuartics
import ErdosProblems.Erdos633b.RightEighthTrigonometry

/-! The negative-square obstruction for the pi/8 right tile, using only
irreducibility and transfer of a vanishing rational polynomial. -/

namespace Erdos633b
open Polynomial

theorem eighth_polynomial_square_impossible (n : ℕ) (hn : 0 < n) (q : ℚ[X])
    (h : (aeval (2 * Real.sin (Real.pi / 8)) q) ^ 2 =
      (n : ℝ) / 2 * (2 - (2 * Real.sin (Real.pi / 8)) ^ 2)) : False := by
  let f : ℚ[X] := evenQuartic 4 2
  let g : ℚ[X] := q ^ 2 - C ((n : ℚ) / 2) * (C 2 - X ^ 2)
  have hf : Irreducible f := rightQuarticEight_irreducible
  have ht : aeval (2 * Real.sin (Real.pi / 8)) f = 0 := by
    simpa [f, evenQuartic] using eighth_sine_quartic
  have ht' : aeval (2 * Real.cos (Real.pi / 8)) f = 0 := by
    simpa [f, evenQuartic] using eighth_cosine_quartic
  have hg : aeval (2 * Real.sin (Real.pi / 8)) g = 0 := by
    simpa [g] using sub_eq_zero.mpr h
  have hg' := rational_polynomial_root_transfer f g _ _ hf
    (evenQuartic_monic 4 2) ht ht' hg
  have he : (aeval (2 * Real.cos (Real.pi / 8)) q) ^ 2 =
      (n : ℝ) / 2 * (2 - (2 * Real.cos (Real.pi / 8)) ^ 2) := by
    simpa [g, sub_eq_zero] using hg'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hneg : (n : ℝ) / 2 * (2 - (2 * Real.cos (Real.pi / 8)) ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith [eighth_cosine_parameter_gt_two])
  nlinarith [sq_nonneg (aeval (2 * Real.cos (Real.pi / 8)) q)]

theorem eighth_boundary_square_impossible (n : ℕ) (hn : 0 < n) (m : Fin 3 → ℕ)
    (h : ((m 0 : ℝ) * Real.sin (Real.pi / 8) +
      m 1 * Real.cos (Real.pi / 8) + m 2) ^ 2 = (n : ℝ) / 2 * Real.sqrt 2) : False := by
  let q : ℚ[X] := C ((m 0 : ℚ) / 2) * X +
    C ((m 1 : ℚ) / 2) * (C 3 * X - X ^ 3) + C (m 2 : ℚ)
  have hq : aeval (2 * Real.sin (Real.pi / 8)) q =
      (m 0 : ℝ) * Real.sin (Real.pi / 8) + m 1 * Real.cos (Real.pi / 8) + m 2 := by
    simp only [q, map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X,
      map_div₀, map_natCast, map_ofNat]
    rw [eighth_cosine_polynomial]
    ring
  apply eighth_polynomial_square_impossible n hn q
  rw [hq, eighth_sine_parameter_complement]
  exact h

end Erdos633b
