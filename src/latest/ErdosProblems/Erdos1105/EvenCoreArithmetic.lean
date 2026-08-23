import ErdosProblems.Erdos1105.PathFormulaArithmetic

namespace Erdos1105

lemma even_extremal_two_le_formula (n d : ℕ) (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n) :
    pathExtremalEdges n (2 * d + 1) 2 ≤ pathFormula n (2 * d + 2) := by
  rw [pathFormula_even]
  have h₂ := pathExtremalEdges_twice n (2 * d + 1) 2 (by omega) (by omega)
  have hD := pathExtremalEdges_twice n (2 * d + 1) (d - 1) (by omega) (by omega)
  have hC := Nat.cast_choose_two ℚ (2 * d)
  have hd' : (4 : ℚ) ≤ d := by exact_mod_cast hd
  have hn' : (2 : ℚ) * d + 2 ≤ n := by exact_mod_cast hn
  have hp : ((d - 1 : ℕ) : ℚ) = d - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h₂ hD hC
  rw [hp] at hD
  by_cases hsmall : n ≤ 3 * d - 1
  · have hnsmall : (n : ℚ) ≤ 3 * d - 1 := by
      have : (n : ℚ) + 1 ≤ 3 * d := by exact_mod_cast (show n + 1 ≤ 3 * d by omega)
      linarith
    have h : (pathExtremalEdges n (2 * d + 1) 2 : ℚ) ≤ ((2 * d).choose 2 : ℚ) + 1 := by
      nlinarith
    exact (by exact_mod_cast h : pathExtremalEdges n (2 * d + 1) 2 ≤
      (2 * d).choose 2 + 1).trans (le_max_left _ _)
  · have hnlarge : (3 : ℚ) * d ≤ n := by exact_mod_cast (show 3 * d ≤ n by omega)
    have hm := mul_nonneg (show (0 : ℚ) ≤ d - 3 by linarith) (show (0 : ℚ) ≤ n - 3 * d by linarith)
    have hmD := mul_nonneg (show (0 : ℚ) ≤ d - 4 by linarith) (show (0 : ℚ) ≤ d + 1 by positivity)
    have h : pathExtremalEdges n (2 * d + 1) 2 + 1 ≤ pathExtremalEdges n (2 * d + 1) (d - 1) := by
      have h' : (pathExtremalEdges n (2 * d + 1) 2 : ℚ) + 1 ≤
          pathExtremalEdges n (2 * d + 1) (d - 1) := by nlinarith
      exact_mod_cast h'
    rw [even_path_linear_term n d (by omega) (by omega)] at h
    exact (by omega : pathExtremalEdges n (2 * d + 1) 2 ≤
      (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2).trans (le_max_right _ _)

lemma even_extremal_penultimate_le_formula (n d : ℕ) (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n) :
    pathExtremalEdges n (2 * d + 1) (d - 2) ≤ pathFormula n (2 * d + 2) := by
  by_cases hd4 : d = 4
  · subst d
    exact even_extremal_two_le_formula n 4 (by omega) hn
  have hd5 : 5 ≤ d := by omega
  have h₂ := pathExtremalEdges_twice n (2 * d + 1) (d - 2) (by omega) (by omega)
  have h₁ := pathExtremalEdges_twice n (2 * d + 1) (d - 1) (by omega) (by omega)
  have hp₁ : ((d - 1 : ℕ) : ℚ) = d - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hp₂ : ((d - 2 : ℕ) : ℚ) = d - 2 := by rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h₁ h₂
  rw [hp₁] at h₁
  rw [hp₂] at h₂
  have hn' : (d : ℚ) + 7 ≤ n := by exact_mod_cast (show d + 7 ≤ n by omega)
  have h : pathExtremalEdges n (2 * d + 1) (d - 2) + 1 ≤
      pathExtremalEdges n (2 * d + 1) (d - 1) := by
    have h' : (pathExtremalEdges n (2 * d + 1) (d - 2) : ℚ) + 1 ≤
        pathExtremalEdges n (2 * d + 1) (d - 1) := by nlinarith
    exact_mod_cast h'
  rw [even_path_linear_term n d (by omega) (by omega)] at h
  rw [pathFormula_even]
  exact (by omega : pathExtremalEdges n (2 * d + 1) (d - 2) ≤
    (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2).trans (le_max_right _ _)

lemma even_extremal_interior_le_formula (n d a : ℕ) (ha : 2 ≤ a) (had : a ≤ d - 2)
    (hn : 2 * d + 2 ≤ n) : pathExtremalEdges n (2 * d + 1) a ≤ pathFormula n (2 * d + 2) := by
  have hd : 4 ≤ d := by omega
  exact (pathExtremalEdges_le_max n (2 * d + 1) 2 a (d - 2) ha had (by omega) (by omega)).trans
    (max_le (even_extremal_two_le_formula n d hd hn) (even_extremal_penultimate_le_formula n d hd hn))

lemma even_small_core_count_le_formula (n d q : ℕ) (hd : 2 ≤ d) (hn : 2 * d + 2 ≤ n)
    (hq : q + n ≤ (d + 2).choose 2 + d * (n + 1 - (d + 2))) :
    q ≤ pathFormula n (2 * d + 2) := by
  have hsharp := cone_nonempty_count n (2 * d + 2) (d + 3) (by omega) (by omega) hn
  have hc : (d + 3).choose 2 = (d + 2).choose 2 + (d + 2) := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ (d + 2) 1
  have hrest : n + 1 - (d + 2) = n + 1 - (d + 3) + 1 := by omega
  rw [show 2 * d + 2 + 1 - (d + 3) = d by omega, hc,
    show 2 * d + 2 - 1 = 2 * d + 1 by omega,
    show 2 * d + 2 - (d + 3) = d - 1 by omega,
    even_path_linear_term n d (by omega) (by omega)] at hsharp
  rw [hrest] at hq
  rw [pathFormula_even]
  apply le_trans ?_ (le_max_right _ _)
  nlinarith

lemma even_empty_core_count_le_formula (n d q : ℕ) (hd : 2 ≤ d) (hn : 2 * d + 2 ≤ n)
    (hq : q + n ≤ d.choose 2 + d * (n + 1 - d)) : q ≤ pathFormula n (2 * d + 2) := by
  apply even_small_core_count_le_formula n d q hd hn
  have hc₁ : (d + 1).choose 2 = d.choose 2 + d := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ d 1
  have hc₂ : (d + 2).choose 2 = (d + 1).choose 2 + (d + 1) := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ (d + 1) 1
  have hrest : n + 1 - d = n + 1 - (d + 2) + 2 := by omega
  rw [hrest] at hq
  nlinarith

end Erdos1105

#print axioms Erdos1105.even_extremal_interior_le_formula
