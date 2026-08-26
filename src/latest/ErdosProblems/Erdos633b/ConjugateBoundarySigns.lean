import ErdosProblems.Erdos633b.ConjugateBoundaryEquations

/-! Positive tile sines at a coprime conjugate force positive outer sines,
using every actual boundary row as well as the area sign. -/

namespace Erdos633b

theorem three_positive_of_cross_products (H x : Fin 3 → ℝ)
    (hH : ∀ i, 0 < H i) (hx : x 0 ≠ 0)
    (hcross : ∀ i j, H i * x j = H j * x i)
    (hprod : 0 < x 0 * x 1 * x 2) : ∀ i, 0 < x i := by
  have h0 : 0 < x 0 := by
    rcases lt_or_gt_of_ne hx with hn | hp
    · have hneg (i : Fin 3) : x i < 0 := by
        have hh : H 0 * x i < 0 := by
          rw [hcross 0 i]
          exact mul_neg_of_pos_of_neg (hH i) hn
        by_contra h
        have hnon := mul_nonneg (hH 0).le (le_of_not_gt h)
        linarith
      have hh := mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (hneg 0) (hneg 1)) (hneg 2)
      linarith
    · exact hp
  intro i
  have hh : 0 < H 0 * x i := by
    rw [hcross 0 i]
    exact mul_pos (hH i) h0
  by_contra h
  have hnon := mul_nonpos_of_nonneg_of_nonpos (hH 0).le (le_of_not_gt h)
  linarith

namespace Tiling

theorem coprime_positive_outer_sines {T : Triangle} {n : ℕ} (d : Tiling T n)
    (N : ℕ) (hN : 1 < N) (w a : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (ha : ∀ i, T.angle i = (a i : ℝ) * (Real.pi / N))
    (hwp : ∀ i, 0 < w i ∧ w i < N) (hap : ∀ i, 0 < a i ∧ a i < N)
    (k : ℕ) (hk : k.Coprime (2 * N))
    (htile : ∀ i, 0 < Real.sin (k * d.tile.angle i)) :
    ∀ i, 0 < Real.sin (k * T.angle i) := by
  let H : Fin 3 → ℝ := fun i => boundarySineCombination (d.boundarySideCount i)
    (fun l => Real.sin (k * d.tile.angle l))
  have hH (i : Fin 3) : 0 < H i :=
    boundary_sine_combination_pos _ _ (d.boundary_row_positive i) htile
  have hx : Real.sin (k * T.angle 0) ≠ 0 := by
    have hh := sine_weight_coprime_ne_zero N k (a 0) (by omega)
      (Nat.Coprime.of_dvd_right (dvd_mul_left N 2) hk) (hap 0).1 (hap 0).2
    simpa only [ha, mul_left_comm (k : ℝ)] using hh
  have htileprod := mul_pos (mul_pos (htile 0) (htile 1)) (htile 2)
  have hboth := d.coprime_sine_product_positive N hN w a hw ha hwp hap k hk
  have hprod : 0 < Real.sin (k * T.angle 0) * Real.sin (k * T.angle 1) *
      Real.sin (k * T.angle 2) := by
    by_contra h
    have hn := mul_nonpos_of_nonneg_of_nonpos htileprod.le (le_of_not_gt h)
    linarith
  exact three_positive_of_cross_products H (fun i => Real.sin (k * T.angle i)) hH hx
    (d.coprime_boundary_sine_cross_eq N hN w a hw ha k hk) hprod

end Tiling
end Erdos633b
