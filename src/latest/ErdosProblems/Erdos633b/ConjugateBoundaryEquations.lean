import ErdosProblems.Erdos633b.RationalTilingSineSigns

/-! Polynomial transfer of each actual boundary cross-product identity. -/

namespace Erdos633b
open Polynomial

noncomputable def boundarySineCombination (m : Fin 3 → ℕ) (x : Fin 3 → ℝ) : ℝ :=
  (m 0 : ℝ) * x 0 + m 1 * x 1 + m 2 * x 2

theorem boundary_sine_combination_pos (m : Fin 3 → ℕ) (x : Fin 3 → ℝ)
    (hm : ∃ i, 0 < m i) (hx : ∀ i, 0 < x i) : 0 < boundarySineCombination m x := by
  have hh : 0 < ∑ i, (m i : ℝ) * x i := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (Nat.cast_nonneg _) (hx i).le
    · obtain ⟨i, hi⟩ := hm
      exact ⟨i, Finset.mem_univ i, mul_pos (by exact_mod_cast hi) (hx i)⟩
  simpa only [Fin.sum_univ_three, boundarySineCombination] using hh

theorem boundary_sine_combination_div (m : Fin 3 → ℕ) (x : Fin 3 → ℝ) (u : ℝ) :
    boundarySineCombination m (fun i => x i / u) = boundarySineCombination m x / u := by
  dsimp only [boundarySineCombination]
  ring

namespace Tiling

theorem boundary_row_positive {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    ∃ j, 0 < d.boundarySideCount i j := by
  by_contra hn
  have hz (j : Fin 3) : d.boundarySideCount i j = 0 := by
    by_contra h
    exact hn ⟨j, Nat.pos_of_ne_zero h⟩
  have hh := d.side_eq_three_counts i
  simp only [hz, Nat.cast_zero, zero_mul, zero_add] at hh
  exact (T.side_pos i).ne' hh

theorem boundary_sine_cross_eq {T : Triangle} {n : ℕ} (d : Tiling T n) (i j : Fin 3) :
    boundarySineCombination (d.boundarySideCount i) (fun l => Real.sin (d.tile.angle l)) *
      Real.sin (T.angle j) =
    boundarySineCombination (d.boundarySideCount j) (fun l => Real.sin (d.tile.angle l)) *
      Real.sin (T.angle i) := by
  dsimp only [boundarySineCombination]
  rw [← d.boundary_sine_sum i, ← d.boundary_sine_sum j]
  have hs := T.sine_law i j
  have hc : d.tile.side 2 ≠ 0 := (d.tile.side_pos 2).ne'
  field_simp [hc]
  linear_combination -Real.sin (d.tile.angle 2) * hs

theorem boundary_sine_cross_scaled_eq {T : Triangle} {n : ℕ} (d : Tiling T n)
    (u : ℝ) (i j : Fin 3) :
    boundarySineCombination (d.boundarySideCount i) (fun l => Real.sin (d.tile.angle l) / u) *
      (Real.sin (T.angle j) / u) =
    boundarySineCombination (d.boundarySideCount j) (fun l => Real.sin (d.tile.angle l) / u) *
      (Real.sin (T.angle i) / u) := by
  rw [boundary_sine_combination_div, boundary_sine_combination_div,
    div_mul_div_comm, div_mul_div_comm, d.boundary_sine_cross_eq i j]

theorem coprime_boundary_sine_cross_eq {T : Triangle} {n : ℕ} (d : Tiling T n)
    (N : ℕ) (hN : 1 < N) (w a : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (ha : ∀ i, T.angle i = (a i : ℝ) * (Real.pi / N))
    (k : ℕ) (hk : k.Coprime (2 * N)) (i j : Fin 3) :
    boundarySineCombination (d.boundarySideCount i) (fun l => Real.sin (k * d.tile.angle l)) *
      Real.sin (k * T.angle j) =
    boundarySineCombination (d.boundarySideCount j) (fun l => Real.sin (k * d.tile.angle l)) *
      Real.sin (k * T.angle i) := by
  let g : ℚ[X] := boundarySinePoly w (d.boundarySideCount i) * sineMultiplePoly (a j) -
    boundarySinePoly w (d.boundarySideCount j) * sineMultiplePoly (a i)
  have hθ := sine_pi_div_ne_zero N hN
  have hψ := sine_coprime_pi_div_ne_zero N k hN
    (Nat.Coprime.of_dvd_right (dvd_mul_left N 2) hk)
  have hg : aeval (2 * Real.cos (Real.pi / N)) g = 0 := by
    dsimp only [g]
    rw [map_sub, map_mul, map_mul,
      eval_boundarySinePoly _ hθ, eval_boundarySinePoly _ hθ,
      eval_sineMultiplePoly _ hθ, eval_sineMultiplePoly _ hθ]
    apply sub_eq_zero.mpr
    simpa only [hw, ha, boundarySineCombination] using
      d.boundary_sine_cross_scaled_eq (Real.sin (Real.pi / N)) i j
  have hg' := cosine_pi_polynomial_transfer N k (by omega) hk g hg
  dsimp only [g] at hg'
  rw [map_sub, map_mul, map_mul,
    eval_boundarySinePoly _ hψ, eval_boundarySinePoly _ hψ,
    eval_sineMultiplePoly _ hψ, eval_sineMultiplePoly _ hψ] at hg'
  have he :
      boundarySineCombination (d.boundarySideCount i)
        (fun l => Real.sin (w l * (k * (Real.pi / N))) / Real.sin (k * (Real.pi / N))) *
        (Real.sin (a j * (k * (Real.pi / N))) / Real.sin (k * (Real.pi / N))) =
      boundarySineCombination (d.boundarySideCount j)
        (fun l => Real.sin (w l * (k * (Real.pi / N))) / Real.sin (k * (Real.pi / N))) *
        (Real.sin (a i * (k * (Real.pi / N))) / Real.sin (k * (Real.pi / N))) :=
    sub_eq_zero.mp hg'
  rw [boundary_sine_combination_div, boundary_sine_combination_div,
    div_mul_div_comm, div_mul_div_comm] at he
  have he' := (div_left_inj' (mul_ne_zero hψ hψ)).mp he
  simpa only [hw, ha, mul_left_comm (k : ℝ)] using he'

end Tiling
end Erdos633b
