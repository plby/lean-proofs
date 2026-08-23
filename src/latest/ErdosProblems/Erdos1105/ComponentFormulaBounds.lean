import ErdosProblems.Erdos1105.ComponentCliqueArithmetic

namespace Erdos1105

lemma componentCliqueTerm_one_le_clique {n k : ℕ} (hk : 5 ≤ k)
    (hn : k ≤ n) (hsmall : n ≤ 2 * k - 4) :
    componentCliqueTerm n k 1 ≤ (k - 2).choose 2 + 1 := by
  have hpred : k - 3 + 1 = k - 2 := by omega
  have hc := Nat.choose_succ_succ (k - 3) 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hpred, Nat.choose_one_right] at hc
  have hsub : k - 1 - 2 = k - 3 := by omega
  simp only [componentCliqueTerm, hsub, show (1 : ℕ).choose 2 = 0 by decide, add_zero, one_mul]
  omega

lemma odd_componentCliqueTerm_top {n l : ℕ} (hl : 2 ≤ l) (hn : 2 * l + 1 ≤ n) :
    componentCliqueTerm n (2 * l + 1) (l - 1) + l.choose 2 + 1 =
      pathExtremalEdges n (2 * l) (l - 1) := by
  have hA := componentCliqueTerm_twice n (2 * l + 1) (l - 1) (by omega) hn
  have hH := pathExtremalEdges_twice n (2 * l) (l - 1) (by omega) (by omega)
  have hc := Nat.cast_choose_two ℚ l
  have hpred : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, hpred] at hA hH
  have h : (componentCliqueTerm n (2 * l + 1) (l - 1) : ℚ) + l.choose 2 + 1 =
      pathExtremalEdges n (2 * l) (l - 1) := by nlinarith
  exact_mod_cast h

lemma even_componentCliqueTerm_top {n l : ℕ} (hl : 2 ≤ l) (hn : 2 * l + 2 ≤ n) :
    componentCliqueTerm n (2 * l + 2) (l - 1) + l.choose 2 + 1 =
      (l - 1).choose 2 + (l - 1) * (n - l + 1) + 2 := by
  have hA := componentCliqueTerm_twice n (2 * l + 2) (l - 1) (by omega) hn
  have hH := pathExtremalEdges_twice n (2 * l + 1) (l - 1) (by omega) (by omega)
  have hc := Nat.cast_choose_two ℚ l
  have hpred : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, hpred] at hA hH
  have h : (componentCliqueTerm n (2 * l + 2) (l - 1) : ℚ) + l.choose 2 + 2 =
      pathExtremalEdges n (2 * l + 1) (l - 1) := by nlinarith
  have hNat : componentCliqueTerm n (2 * l + 2) (l - 1) + l.choose 2 + 2 =
      pathExtremalEdges n (2 * l + 1) (l - 1) := by exact_mod_cast h
  rw [even_path_linear_term n l (by omega) (by omega)] at hNat
  omega

lemma odd_componentCliqueTerm_one_large {n l : ℕ} (hl : 2 ≤ l)
    (hn : 2 * l + 1 ≤ n) (hlarge : 4 * l - 2 ≤ n) :
    componentCliqueTerm n (2 * l + 1) 1 ≤ pathExtremalEdges n (2 * l) (l - 1) := by
  have hA := componentCliqueTerm_twice n (2 * l + 1) 1 (by omega) hn
  have hH := pathExtremalEdges_twice n (2 * l) (l - 1) (by omega) (by omega)
  have hpred : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, hpred] at hA hH
  have hl' : (2 : ℚ) ≤ l := by exact_mod_cast hl
  have hn' : (4 : ℚ) * l - 2 ≤ n := by
    have h : 4 * l ≤ n + 2 := by omega
    have h' : (4 : ℚ) * l ≤ n + 2 := by exact_mod_cast h
    linarith
  have hm₁ := mul_nonneg (show (0 : ℚ) ≤ l - 2 by linarith)
    (show (0 : ℚ) ≤ n - (4 * l - 2) by linarith)
  have hm₂ := mul_nonneg (show (0 : ℚ) ≤ 3 * l - 1 by linarith)
    (show (0 : ℚ) ≤ l - 2 by linarith)
  have h : (componentCliqueTerm n (2 * l + 1) 1 : ℚ) ≤
      pathExtremalEdges n (2 * l) (l - 1) := by nlinarith
  exact_mod_cast h

lemma even_componentCliqueTerm_one_large {n l : ℕ} (hl : 2 ≤ l)
    (hn : 2 * l + 2 ≤ n) (hlarge : 4 * l ≤ n) :
    componentCliqueTerm n (2 * l + 2) 1 ≤
      (l - 1).choose 2 + (l - 1) * (n - l + 1) + 2 := by
  have hA := componentCliqueTerm_twice n (2 * l + 2) 1 (by omega) hn
  have hH := pathExtremalEdges_twice n (2 * l + 1) (l - 1) (by omega) (by omega)
  have hpred : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, hpred] at hA hH
  have hl' : (2 : ℚ) ≤ l := by exact_mod_cast hl
  have hn' : (4 : ℚ) * l ≤ n := by exact_mod_cast hlarge
  have hm₁ := mul_nonneg (show (0 : ℚ) ≤ l - 2 by linarith)
    (show (0 : ℚ) ≤ n - 4 * l by linarith)
  have hm₂ := mul_nonneg (show (0 : ℚ) ≤ 3 * l - 2 by linarith)
    (show (0 : ℚ) ≤ l - 1 by linarith)
  have h : (componentCliqueTerm n (2 * l + 2) 1 : ℚ) + 1 ≤
      pathExtremalEdges n (2 * l + 1) (l - 1) := by nlinarith
  have hNat : componentCliqueTerm n (2 * l + 2) 1 + 1 ≤
      pathExtremalEdges n (2 * l + 1) (l - 1) := by exact_mod_cast h
  rw [even_path_linear_term n l (by omega) (by omega)] at hNat
  omega

theorem componentCliqueTerm_le_pathFormula {n k b : ℕ} (hk : 5 ≤ k) (hn : k ≤ n)
    (hb : 1 ≤ b) (hbtop : b ≤ (k - 1) / 2 - 1) :
    componentCliqueTerm n k b ≤ pathFormula n k := by
  let l := (k - 1) / 2
  have hl : 2 ≤ l := by dsimp [l]; omega
  have hkcases : k = 2 * l + 1 ∨ k = 2 * l + 2 := by dsimp [l]; omega
  apply (componentCliqueTerm_le_max hb hbtop (by omega) hn).trans
  apply max_le
  · by_cases hsmall : n ≤ 2 * k - 4
    · exact (componentCliqueTerm_one_le_clique hk hn hsmall).trans (le_max_left _ _)
    · rcases hkcases with hk' | hk'
      · rw [hk', pathFormula_odd n l (by omega) (by omega)]
        exact (odd_componentCliqueTerm_one_large hl (by omega) (by omega)).trans (le_max_right _ _)
      · rw [hk', pathFormula_even]
        exact (even_componentCliqueTerm_one_large hl (by omega) (by omega)).trans (le_max_right _ _)
  · change componentCliqueTerm n k (l - 1) ≤ _
    rcases hkcases with hk' | hk'
    · rw [hk', pathFormula_odd n l (by omega) (by omega)]
      have h := odd_componentCliqueTerm_top hl (show 2 * l + 1 ≤ n by omega)
      exact (show componentCliqueTerm n (2 * l + 1) (l - 1) ≤
        pathExtremalEdges n (2 * l) (l - 1) by omega).trans (le_max_right _ _)
    · rw [hk', pathFormula_even]
      have h := even_componentCliqueTerm_top hl (show 2 * l + 2 ≤ n by omega)
      exact (show componentCliqueTerm n (2 * l + 2) (l - 1) ≤
        (l - 1).choose 2 + (l - 1) * (n - l + 1) + 2 by omega).trans (le_max_right _ _)

end Erdos1105

#print axioms Erdos1105.componentCliqueTerm_le_pathFormula
