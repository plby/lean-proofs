import ErdosProblems.Erdos633b.ReptilingMatrix
import ErdosProblems.Erdos633b.ThreeMatrixGraph
import ErdosProblems.Erdos633b.MinimumCornerEdges

/-! The minimum corner reduces the spectral alternative to zero diagonal or
one explicit exceptional matrix. Its exclusion still requires boundary-point geometry. -/

namespace Erdos633b

open Matrix

namespace NonnegativeMatrix

theorem three_corner_alternative {D : Matrix (Fin 3) (Fin 3) ℝ}
    (hD : ∀ i j, 0 ≤ D i j) {v w : Fin 3 → ℝ} {L : ℝ}
    (hv : ∀ i, 0 < v i) (hL : 0 < L) (hw : w ≠ 0)
    (hpos : D *ᵥ v = L • v) (hneg : D *ᵥ w = -L • w)
    (hcorner : (0 < D 1 1 ∧ 0 < D 2 2) ∨ (0 < D 1 2 ∧ 0 < D 2 1)) :
    (∀ i, D i i = 0) ∨
      (0 < D 0 0 ∧ 0 < D 1 2 ∧ 0 < D 2 1 ∧
        D 1 0 = 0 ∧ D 1 1 = 0 ∧ D 2 0 = 0 ∧ D 2 2 = 0) := by
  rcases three_diagonal_alternative hD hv hL hw hpos hneg with hd | ⟨i, j, k,
    hij, hik, hjk, hkk, hijpos, hjipos, hrowi, hrowj⟩
  · exact Or.inl hd
  right
  have hii := hrowi i hij
  have hjj := hrowj j hij.symm
  rcases hcorner with ⟨h11, h22⟩ | ⟨h12, h21⟩
  · have hi1 : i ≠ 1 := by intro h; rw [h] at hii; exact h11.ne' hii
    have hi2 : i ≠ 2 := by intro h; rw [h] at hii; exact h22.ne' hii
    have hj1 : j ≠ 1 := by intro h; rw [h] at hjj; exact h11.ne' hjj
    have hj2 : j ≠ 2 := by intro h; rw [h] at hjj; exact h22.ne' hjj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    exact False.elim (hij (hi0.trans hj0.symm))
  · have hi0 : i ≠ 0 := by
      intro hi0
      by_cases hj1 : j = 1
      · have hz := hrowj 2 (by omega)
        rw [hj1] at hz
        exact h12.ne' hz
      · have hj2 : j = 2 := by omega
        have hz := hrowj 1 (by omega)
        rw [hj2] at hz
        exact h21.ne' hz
    have hj0 : j ≠ 0 := by
      intro hj0
      by_cases hi1 : i = 1
      · have hz := hrowi 2 (by omega)
        rw [hi1] at hz
        exact h12.ne' hz
      · have hi2 : i = 2 := by omega
        have hz := hrowi 1 (by omega)
        rw [hi2] at hz
        exact h21.ne' hz
    have hk0 : k = 0 := by omega
    subst k
    by_cases hi1 : i = 1
    · have hj2 : j = 2 := by omega
      subst i
      subst j
      exact ⟨hkk, h12, h21, hrowi 0 (by decide), hrowi 1 (by decide),
        hrowj 0 (by decide), hrowj 2 (by decide)⟩
    · have hi2 : i = 2 := by omega
      have hj1 : j = 1 := by omega
      subst i
      subst j
      exact ⟨hkk, h12, h21, hrowj 0 (by decide), hrowj 1 (by decide),
        hrowi 0 (by decide), hrowi 2 (by decide)⟩

end NonnegativeMatrix

namespace Tiling

theorem minimum_corner_matrix_counts {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ∀ i, d.tile.angle i = T.angle i)
    (hmin : ∀ j, j ≠ 0 → d.tile.angle 0 < d.tile.angle j) :
    (0 < d.boundarySideCount 1 1 ∧ 0 < d.boundarySideCount 2 2) ∨
      (0 < d.boundarySideCount 1 2 ∧ 0 < d.boundarySideCount 2 1) := by
  have hmin' (j : Fin 3) : T.angle 0 ≤ d.tile.angle j := by
    rw [← h 0]
    by_cases hj : j = 0
    · rw [hj]
    · exact (hmin j hj).le
  obtain ⟨k, j, hj⟩ := d.outer_vertex_is_tile_vertex 0
  let e : d.CornerPiece 0 := ⟨(k, j), hj⟩
  have he := d.angle_cornerPiece_of_min 0 hmin' e
  have hj0 : e.val.2 = 0 := by
    by_contra hn
    have hl := hmin e.val.2 hn
    rw [he, h 0] at hl
    exact lt_irrefl _ hl
  have hc := d.adjacent_counts_pos_of_min 0 hmin' e
  simp only [hj0, zero_add] at hc
  exact hc.imp (fun h => ⟨h.2, h.1⟩) id

theorem boundaryMatrix_corner_alternative {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (hmin : ∀ j, j ≠ 0 → d.tile.angle 0 < d.tile.angle j) :
    (∀ i, d.boundaryMatrix i i = 0) ∨
      (0 < d.boundaryMatrix 0 0 ∧ 0 < d.boundaryMatrix 1 2 ∧ 0 < d.boundaryMatrix 2 1 ∧
        d.boundaryMatrix 1 0 = 0 ∧ d.boundaryMatrix 1 1 = 0 ∧
        d.boundaryMatrix 2 0 = 0 ∧ d.boundaryMatrix 2 2 = 0) := by
  obtain ⟨w, hw, he⟩ := d.boundaryMatrix_negative_eigenvector hn h
  have hD (i j : Fin 3) : 0 ≤ ThreeMatrix.toReal d.boundaryMatrix i j := by
    unfold ThreeMatrix.toReal
    exact_mod_cast d.boundaryMatrix_nonneg i j
  have hL : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr d.positive)
  have hcorner :
      (0 < ThreeMatrix.toReal d.boundaryMatrix 1 1 ∧ 0 < ThreeMatrix.toReal d.boundaryMatrix 2 2) ∨
      (0 < ThreeMatrix.toReal d.boundaryMatrix 1 2 ∧
        0 < ThreeMatrix.toReal d.boundaryMatrix 2 1) := by
    unfold ThreeMatrix.toReal boundaryMatrix
    exact_mod_cast d.minimum_corner_matrix_counts h hmin
  have result := NonnegativeMatrix.three_corner_alternative hD d.tile.side_pos hL hw
    (d.boundaryMatrix_mul_side h) he hcorner
  unfold ThreeMatrix.toReal at result
  exact_mod_cast result


theorem boundaryMatrix_zero_diagonal_identities {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (hd : ∀ i, d.boundaryMatrix i i = 0) :
    d.boundaryMatrix 0 1 * d.boundaryMatrix 1 2 * d.boundaryMatrix 2 0 = 0 ∧
      d.boundaryMatrix 0 2 * d.boundaryMatrix 1 0 * d.boundaryMatrix 2 1 = 0 ∧
      (n : ℤ) = d.boundaryMatrix 0 1 * d.boundaryMatrix 1 0 +
        d.boundaryMatrix 0 2 * d.boundaryMatrix 2 0 +
        d.boundaryMatrix 1 2 * d.boundaryMatrix 2 1 := by
  obtain ⟨hs, hdet⟩ := d.boundaryMatrix_nonsquare_coefficients hn h
  have ht : ThreeMatrix.traceInt d.boundaryMatrix = 0 := by
    simp only [ThreeMatrix.traceInt, hd, add_zero]
  rw [ht, neg_zero, zero_mul] at hdet
  simp only [Matrix.det_fin_three, hd, zero_mul, mul_zero, sub_zero, zero_add] at hdet
  have ha := mul_nonneg (mul_nonneg (d.boundaryMatrix_nonneg 0 1)
    (d.boundaryMatrix_nonneg 1 2)) (d.boundaryMatrix_nonneg 2 0)
  have hb := mul_nonneg (mul_nonneg (d.boundaryMatrix_nonneg 0 2)
    (d.boundaryMatrix_nonneg 1 0)) (d.boundaryMatrix_nonneg 2 1)
  refine ⟨by linarith, by linarith, ?_⟩
  simp only [ThreeMatrix.secondInt, hd, mul_zero, add_zero, zero_sub] at hs
  omega

theorem boundaryMatrix_exception_count {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (h10 : d.boundaryMatrix 1 0 = 0) (h11 : d.boundaryMatrix 1 1 = 0)
    (h20 : d.boundaryMatrix 2 0 = 0) (h22 : d.boundaryMatrix 2 2 = 0) :
    (n : ℤ) = d.boundaryMatrix 1 2 * d.boundaryMatrix 2 1 := by
  have hs := (d.boundaryMatrix_nonsquare_coefficients hn h).1
  simp only [ThreeMatrix.secondInt, h10, h11, h20, h22, mul_zero,
    add_zero, sub_zero, zero_sub] at hs
  omega

end Tiling

end Erdos633b
