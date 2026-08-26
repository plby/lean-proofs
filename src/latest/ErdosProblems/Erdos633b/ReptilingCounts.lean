import ErdosProblems.Erdos633b.ReptilingDiagonalZero
import ErdosProblems.Erdos633b.ReptilingCaseAlgebra
import ErdosProblems.Erdos633b.RightGeometry

/-! The two possible counts for a scalene ordered nonsquare reptiling,
obtained from its actual boundary matrix. -/

namespace Erdos633b.Tiling

theorem reptiling_cross_counts_pos {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    0 < d.boundaryMatrix 1 2 ∧ 0 < d.boundaryMatrix 2 1 := by
  have hmin (j : Fin 3) (hj : j ≠ 0) : d.tile.angle 0 < d.tile.angle j := by
    fin_cases j
    · exact False.elim (hj rfl)
    · exact h01
    · exact h01.trans h12
  have hd := d.reptiling_diagonal_zero hn h h01 h12
  rcases d.minimum_corner_matrix_counts h hmin with hc | hc
  · have hz : d.boundarySideCount 1 1 = 0 := by
      have hz := hd 1
      unfold boundaryMatrix at hz
      exact_mod_cast hz
    exact False.elim (by omega)
  · unfold boundaryMatrix
    exact_mod_cast hc

theorem reptiling_matrix_alternatives {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    d.boundaryMatrix 0 2 = 0 ∨
      d.boundaryMatrix 0 1 = 0 ∧ d.boundaryMatrix 1 0 = 0 := by
  have hd := d.reptiling_diagonal_zero hn h h01 h12
  have h0 := d.boundaryMatrix_three_equation h 0
  have h1 := d.boundaryMatrix_three_equation h 1
  simp only [hd, Int.cast_zero, zero_mul, zero_add, add_zero] at h0 h1
  exact right_rows_alternatives _ _ _ _ (d.boundaryMatrix_nonneg 0 1)
    (d.reptiling_cross_counts_pos hn h h01 h12).1 (d.boundaryMatrix_nonneg 1 0)
    (d.tile.side_pos 2).ne' (Real.sq_sqrt (Nat.cast_nonneg n))
    (irrational_sqrt_natCast_iff.mpr hn)
    (d.tile.right_pythagoras (d.reptiling_right_angle hn h h01 h12)).symm h0 h1

theorem reptiling_biquadratic {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (h01z : d.boundaryMatrix 0 1 = 0) (h10z : d.boundaryMatrix 1 0 = 0) :
    0 < d.boundarySideCount 0 2 ∧ 0 < d.boundarySideCount 1 2 ∧
      n = d.boundarySideCount 0 2 ^ 2 + d.boundarySideCount 1 2 ^ 2 ∧
      T.side 0 / T.side 1 =
        (d.boundarySideCount 0 2 : ℝ) / d.boundarySideCount 1 2 := by
  have hd := d.reptiling_diagonal_zero hn h h01 h12
  have h0 := d.boundaryMatrix_three_equation h 0
  have h1 := d.boundaryMatrix_three_equation h 1
  simp only [hd, h01z, h10z, Int.cast_zero, zero_mul, zero_add, add_zero] at h0 h1
  have hL : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr d.positive)
  have he : 0 < d.boundaryMatrix 0 2 := by
    have hp : 0 < (d.boundaryMatrix 0 2 : ℝ) * d.tile.side 2 :=
      h0 ▸ mul_pos hL (d.tile.side_pos 0)
    exact_mod_cast (pos_of_mul_pos_left hp (d.tile.side_pos 2).le)
  have hf := (d.reptiling_cross_counts_pos hn h h01 h12).1
  have hcount := biquadratic_rows_count _ _ (d.tile.side_pos 2).ne'
    (Real.sq_sqrt (Nat.cast_nonneg n))
    (d.tile.right_pythagoras (d.reptiling_right_angle hn h h01 h12)).symm h0 h1
  have hratio := biquadratic_rows_ratio _ _ (d.tile.side_pos 1).ne'
    (d.tile.side_pos 2).ne' hf.ne' h0 h1
  unfold boundaryMatrix at he hf hcount
  refine ⟨by exact_mod_cast he, by exact_mod_cast hf, by exact_mod_cast hcount, ?_⟩
  rw [d.side_eq_sqrt_mul_of_angles h 0, d.side_eq_sqrt_mul_of_angles h 1,
    mul_div_mul_left _ _ hL.ne', hratio]
  simp only [boundaryMatrix, Int.cast_natCast]

theorem reptiling_triple_square {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (he : d.boundaryMatrix 0 2 = 0) :
    d.tile.angle 0 = Real.pi / 6 ∧ d.tile.angle 1 = Real.pi / 3 ∧
      n = 3 * d.boundarySideCount 0 1 ^ 2 := by
  have hd := d.reptiling_diagonal_zero hn h h01 h12
  have hright := d.reptiling_right_angle hn h h01 h12
  obtain ⟨hf, hl⟩ := d.reptiling_cross_counts_pos hn h h01 h12
  have h0 := d.boundaryMatrix_three_equation h 0
  simp only [hd, he, Int.cast_zero, zero_mul, zero_add, add_zero] at h0
  have hL : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr d.positive)
  have hdp : 0 < d.boundaryMatrix 0 1 := by
    have hp : 0 < (d.boundaryMatrix 0 1 : ℝ) * d.tile.side 1 :=
      h0 ▸ mul_pos hL (d.tile.side_pos 0)
    exact_mod_cast (pos_of_mul_pos_left hp (d.tile.side_pos 1).le)
  have hh : d.boundaryMatrix 2 0 = 0 := by
    have hz := (d.boundaryMatrix_zero_diagonal_identities hn h hd).1
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hdp.ne' hf.ne')
  have h2 := d.boundaryMatrix_three_equation h 2
  simp only [hd, hh, Int.cast_zero, zero_mul, zero_add, add_zero] at h2
  have hcross : d.tile.side 0 * (d.boundaryMatrix 2 1 : ℝ) =
      (d.boundaryMatrix 0 1 : ℝ) * d.tile.side 2 := by
    apply mul_right_cancel₀ (d.tile.side_pos 1).ne'
    linear_combination d.tile.side 2 * h0 - d.tile.side 0 * h2
  obtain ⟨a, ha⟩ := d.smallest_corner_at_second_endpoint_on_edge h h12 0 (by decide) (hd 0) he
  obtain ⟨u, hu⟩ := d.second_angle_multiple_of_smallest_corner (h 1) h12 a ha
  have hs := d.tile.angle_sum
  have hrat : IsRational (d.tile.angle 0 / Real.pi) := by
    refine ⟨1 / (2 * ((u : ℚ) + 1)), ?_⟩
    push_cast
    apply (div_eq_div_iff (by positivity : (2 : ℝ) * ((u : ℝ) + 1) ≠ 0)
      Real.pi_ne_zero).mpr
    rw [hu, hright] at hs
    nlinarith
  obtain ⟨hsin, hcos⟩ := d.tile.right_sine_cosine_sides hright
  have hsinl : Real.sin (d.tile.angle 0) * (d.boundaryMatrix 2 1 : ℝ) =
      d.boundaryMatrix 0 1 := by
    apply mul_right_cancel₀ (d.tile.side_pos 2).ne'
    linear_combination hcross + (d.boundaryMatrix 2 1 : ℝ) * hsin
  have hsinrat : IsRational (Real.sin (d.tile.angle 0)) := by
    refine ⟨(d.boundaryMatrix 0 1 : ℚ) / d.boundaryMatrix 2 1, ?_⟩
    push_cast
    exact (div_eq_iff (by exact_mod_cast hl.ne')).mpr hsinl.symm
  have hcosrat : IsRational (Real.cos (d.tile.angle 0) ^ 2) := by
    obtain ⟨q, hq⟩ := hsinrat
    refine ⟨1 - q ^ 2, ?_⟩
    push_cast
    rw [hq]
    nlinarith [Real.sin_sq_add_cos_sq (d.tile.angle 0)]
  have ha4 : d.tile.angle 0 < Real.pi / 4 := by rw [hright] at hs; linarith
  have ha6 := angle_eq_pi_six_of_rational_cos_sq (d.tile.angle_pos 0) ha4 hrat hcosrat
  have hb3 : d.tile.angle 1 = Real.pi / 3 := by rw [hright, ha6] at hs; linarith
  rw [ha6, Real.sin_pi_div_six] at hsin
  rw [ha6, Real.cos_pi_div_six] at hcos
  have hba : d.tile.side 1 = Real.sqrt 3 * d.tile.side 0 := by
    linear_combination Real.sqrt 3 * hsin - hcos
  have hscale : Real.sqrt (n : ℝ) = (d.boundaryMatrix 0 1 : ℝ) * Real.sqrt 3 := by
    apply mul_right_cancel₀ (d.tile.side_pos 0).ne'
    linear_combination h0 + (d.boundaryMatrix 0 1 : ℝ) * hba
  have hcount : (n : ℝ) = 3 * (d.boundaryMatrix 0 1 : ℝ) ^ 2 := by
    have hs2 := congrArg (fun x : ℝ => x ^ 2) hscale
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  refine ⟨ha6, hb3, ?_⟩
  unfold boundaryMatrix at hcount
  exact_mod_cast hcount

end Erdos633b.Tiling
