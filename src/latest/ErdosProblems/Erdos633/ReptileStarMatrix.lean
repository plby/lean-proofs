import ErdosProblems.Erdos633.ReptileMatrixSigns

/-!
# The star matrix forced by the two acute corners

Two possible corner matchings, together with the negative eigenvalue, force
the bipartite star matrix. The Pythagorean side identity then gives the exact
sum-of-two-squares count and rational leg ratio.
-/

namespace Erdos633

open scoped BigOperators

theorem positive_product_of_two_negative_products (x y z : ℝ)
    (hy : x * y < 0) (hz : x * z < 0) : 0 < y * z := by
  by_cases hx : x < 0
  · have hypos : 0 < y := by
      by_contra h
      have hprod := mul_nonneg_of_nonpos_of_nonpos hx.le (le_of_not_gt h)
      linarith
    have hzpos : 0 < z := by
      by_contra h
      have hprod := mul_nonneg_of_nonpos_of_nonpos hx.le (le_of_not_gt h)
      linarith
    exact mul_pos hypos hzpos
  · have hyn : y < 0 := by
      by_contra h
      have hprod := mul_nonneg (le_of_not_gt hx) (le_of_not_gt h)
      linarith
    have hzn : z < 0 := by
      by_contra h
      have hprod := mul_nonneg (le_of_not_gt hx) (le_of_not_gt h)
      linarith
    exact mul_pos_of_neg_of_neg hyn hzn

theorem star_matrix_zeros_of_eigenvectors
    (D : Fin 3 → Fin 3 → ℕ) (v w : Fin 3 → ℝ) (x : ℝ)
    (hv : ∀ i, 0 < v i) (hw : w ≠ 0)
    (hpos : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i)
    (hneg : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * w j = -x * w i)
    (h02 : 0 < D 0 2) (h12 : 0 < D 1 2) (h20 : 0 < D 2 0) (h21 : 0 < D 2 1) :
    D 0 0 = 0 ∧ D 0 1 = 0 ∧ D 1 0 = 0 ∧ D 1 1 = 0 ∧ D 2 2 = 0 := by
  obtain ⟨M, hM, i, hi, hb⟩ := exists_positive_maximum_ratio v w hv hw
  have h2 : |w 2| = M * v 2 := by
    have hic : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hic with rfl | rfl | rfl
    · exact (negative_eigenvector_extreme_step D v w x M hv hM hpos hneg hb 0 hi 2 h02).1
    · exact (negative_eigenvector_extreme_step D v w x M hv hM hpos hneg hb 1 hi 2 h12).1
    · exact hi
  obtain ⟨h0, hs0⟩ := negative_eigenvector_extreme_step D v w x M hv hM hpos hneg hb 2 h2 0 h20
  obtain ⟨h1, hs1⟩ := negative_eigenvector_extreme_step D v w x M hv hM hpos hneg hb 2 h2 1 h21
  have hs01 : 0 < w 0 * w 1 := positive_product_of_two_negative_products _ _ _ hs0 hs1
  have hz01 : D 0 1 = 0 := by
    by_contra h
    have hn := (negative_eigenvector_extreme_step D v w x M hv hM hpos hneg hb 0 h0 1
      (Nat.pos_of_ne_zero h)).2
    linarith
  have hz10 : D 1 0 = 0 := by
    by_contra h
    have hn := (negative_eigenvector_extreme_step D v w x M hv hM hpos hneg hb 1 h1 0
      (Nat.pos_of_ne_zero h)).2
    rw [mul_comm] at hn
    linarith
  exact ⟨negative_eigenvector_extreme_diagonal_zero D v w x M hv hM hpos hneg hb 0 h0,
    hz01, hz10,
    negative_eigenvector_extreme_diagonal_zero D v w x M hv hM hpos hneg hb 1 h1,
    negative_eigenvector_extreme_diagonal_zero D v w x M hv hM hpos hneg hb 2 h2⟩

theorem two_zero_diagonals_exclude_two_positive
    (D : Fin 3 → Fin 3 → ℕ)
    (hzero : ∃ i j : Fin 3, i ≠ j ∧ D i i = 0 ∧ D j j = 0)
    (k l : Fin 3) (hkl : k ≠ l) (hk : 0 < D k k) (hl : 0 < D l l) : False := by
  obtain ⟨i, j, hij, hi, hj⟩ := hzero
  have hik : i ≠ k := by intro h; subst k; omega
  have hil : i ≠ l := by intro h; subst l; omega
  have hjk : j ≠ k := by intro h; subst k; omega
  have hjl : j ≠ l := by intro h; subst l; omega
  omega

theorem natural_star_matrix_right_ratio
    (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (x : ℝ) (N : ℕ)
    (hv : ∀ i, 0 < v i) (hx : 0 < x) (hsq : x ^ 2 = N)
    (hpos : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i)
    (hpyth : v 0 ^ 2 + v 1 ^ 2 = v 2 ^ 2)
    (h00 : D 0 0 = 0) (h01 : D 0 1 = 0) (h10 : D 1 0 = 0) (h11 : D 1 1 = 0)
    (h12 : 0 < D 1 2) :
    N = D 0 2 ^ 2 + D 1 2 ^ 2 ∧ v 0 / v 1 = (D 0 2 : ℝ) / D 1 2 := by
  have h0 : (D 0 2 : ℝ) * v 2 = x * v 0 := by
    simpa [Fin.sum_univ_succ, h00, h01] using hpos 0
  have h1 : (D 1 2 : ℝ) * v 2 = x * v 1 := by
    simpa [Fin.sum_univ_succ, h10, h11] using hpos 1
  have hcount : ((D 0 2 : ℝ) ^ 2 + (D 1 2 : ℝ) ^ 2) * v 2 ^ 2 = (N : ℝ) * v 2 ^ 2 := by
    calc
      _ = ((D 0 2 : ℝ) * v 2) ^ 2 + ((D 1 2 : ℝ) * v 2) ^ 2 := by ring
      _ = (x * v 0) ^ 2 + (x * v 1) ^ 2 := by rw [h0, h1]
      _ = x ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by ring
      _ = _ := by rw [hsq, hpyth]
  have hcount' := mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt (hv 2))) hcount
  refine ⟨by exact_mod_cast hcount'.symm, ?_⟩
  apply (div_eq_div_iff (ne_of_gt (hv 1)) (by exact_mod_cast Nat.ne_zero_of_lt h12)).mpr
  apply mul_left_cancel₀ (ne_of_gt hx)
  calc
    _ = (x * v 0) * (D 1 2 : ℝ) := by ring
    _ = ((D 0 2 : ℝ) * v 2) * (D 1 2 : ℝ) := by rw [h0]
    _ = (D 0 2 : ℝ) * ((D 1 2 : ℝ) * v 2) := by ring
    _ = (D 0 2 : ℝ) * (x * v 1) := by rw [h1]
    _ = _ := by ring

theorem natural_matrix_right_necessity_of_corner_alternatives
    (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (x : ℝ) (N : ℕ)
    (hv : ∀ i, 0 < v i) (hx : 0 < x) (hsq : x ^ 2 = N) (hN : ¬ IsSquare N)
    (hpos : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i)
    (hpyth : v 0 ^ 2 + v 1 ^ 2 = v 2 ^ 2)
    (hA : (0 < D 1 1 ∧ 0 < D 2 2) ∨ (0 < D 1 2 ∧ 0 < D 2 1))
    (hB : (0 < D 0 0 ∧ 0 < D 2 2) ∨ (0 < D 0 2 ∧ 0 < D 2 0)) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ N = p ^ 2 + q ^ 2 ∧ v 0 / v 1 = (p : ℝ) / q := by
  have hvne : v ≠ 0 := by intro h; exact (ne_of_gt (hv 0)) (congrFun h 0)
  obtain ⟨w, hw, hneg⟩ := natural_matrix_three_negative_eigenvector D N x hN hsq v hvne hpos
  have hzero := positive_negative_eigenvectors_two_zero_diagonals D v w x hv hw hx hpos hneg
  have hAswap : 0 < D 1 2 ∧ 0 < D 2 1 := hA.resolve_left (fun h =>
    two_zero_diagonals_exclude_two_positive D hzero 1 2 (by decide) h.1 h.2)
  have hBswap : 0 < D 0 2 ∧ 0 < D 2 0 := hB.resolve_left (fun h =>
    two_zero_diagonals_exclude_two_positive D hzero 0 2 (by decide) h.1 h.2)
  obtain ⟨h00, h01, h10, h11, _⟩ := star_matrix_zeros_of_eigenvectors D v w x hv hw hpos hneg
    hBswap.1 hAswap.1 hBswap.2 hAswap.2
  exact ⟨D 0 2, D 1 2, hBswap.1, hAswap.1,
    natural_star_matrix_right_ratio D v x N hv hx hsq hpos hpyth h00 h01 h10 h11 hAswap.1⟩

end Erdos633
