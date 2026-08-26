import ErdosProblems.Erdos633b.PrimitiveSinePolynomials

/-! Shared-angle geometric area gives an exact polynomial equation in
natural boundary rows and the actual number of congruent pieces. -/

namespace Erdos633b
open Polynomial

noncomputable def rootSharedAreaPoly (M : ℕ) (w : Fin 3 → ℕ)
    (m : Fin 3 → Fin 3 → ℕ) (n : ℕ) : ℚ[X] :=
  rootBoundaryPoly M w (m 1) * rootBoundaryPoly M w (m 2) -
    C (n : ℚ) * rootSinePoly M (w 1) * rootSinePoly M (w 2)

namespace Tiling

theorem boundary_sine_shared_area {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) :
    boundarySineCombination (d.boundarySideCount 1) (fun l => Real.sin (d.tile.angle l)) *
      boundarySineCombination (d.boundarySideCount 2) (fun l => Real.sin (d.tile.angle l)) =
      (n : ℝ) * Real.sin (d.tile.angle 1) * Real.sin (d.tile.angle 2) := by
  have he := (eq_div_iff (div_ne_zero (d.tile.side_pos 1).ne'
    (d.tile.side_pos 2).ne')).mp (d.normalized_count_of_shared_angle h0)
  rw [d.tile.side_ratio_eq_sine_ratio] at he
  have hsg : Real.sin (d.tile.angle 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (d.tile.angle_pos 2) (d.tile.angle_lt_pi 2)).ne'
  have he' : (n : ℝ) * Real.sin (d.tile.angle 1) =
      ((T.side 1 / d.tile.side 2) * (T.side 2 / d.tile.side 2)) *
        Real.sin (d.tile.angle 2) := by
    have hh := congrArg (fun x : ℝ => x * Real.sin (d.tile.angle 2)) he
    simpa only [mul_assoc, div_mul_cancel₀ _ hsg] using hh
  dsimp only [boundarySineCombination]
  rw [← d.boundary_sine_sum 1, ← d.boundary_sine_sum 2]
  linear_combination -Real.sin (d.tile.angle 2) * he'

theorem root_shared_area_aeval_zero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) (N : ℕ) (hN : 0 < N) (w : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (hwb : ∀ i, w i ≤ 2 * N) :
    aeval (Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I))
      (rootSharedAreaPoly (2 * N) w d.boundarySideCount n) = 0 := by
  have hz : Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I) ^ (2 * N) = 1 := by
    simpa only [Nat.cast_one, one_mul] using (primitive_pi_root N 1 hN (by simp)).pow_eq_one
  simp only [rootSharedAreaPoly, map_sub, map_mul, aeval_C]
  rw [rootBoundaryPoly_eval _ _ _ hwb _ hz, rootBoundaryPoly_eval _ _ _ hwb _ hz,
    rootSinePoly_eval _ _ (hwb 1) _ hz, rootSinePoly_eval _ _ (hwb 2) _ hz]
  have hh := d.boundary_sine_shared_area h0
  simp_rw [hw] at hh
  have hc :
      (boundarySineCombination (d.boundarySideCount 1)
        (fun l => Real.sin (w l * (Real.pi / N))) : ℂ) *
      (boundarySineCombination (d.boundarySideCount 2)
        (fun l => Real.sin (w l * (Real.pi / N))) : ℂ) =
      (n : ℂ) * (Real.sin (w 1 * (Real.pi / N)) : ℂ) *
        (Real.sin (w 2 * (Real.pi / N)) : ℂ) := by exact_mod_cast hh
  push_cast at hc ⊢
  linear_combination (2 * Complex.I) ^ 2 * hc

end Tiling
end Erdos633b
