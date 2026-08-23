import ErdosProblems.Erdos1105.ComponentFormulaBounds

namespace Erdos1105

lemma pathExtremal_one_le_componentCliqueTerm {n k : ℕ} (hk : 5 ≤ k) (hn : k ≤ n) :
    pathExtremalEdges (n - 1) (k - 3) 1 ≤ componentCliqueTerm n k 1 := by
  have hpred : k - 4 + 1 = k - 3 := by omega
  have hc := Nat.choose_succ_succ (k - 4) 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hpred, Nat.choose_one_right] at hc
  have h₁ : k - 3 - 1 = k - 4 := by omega
  have h₂ : k - 1 - 2 = k - 3 := by omega
  have h₃ : n - 1 - (k - 3) + 1 = n - k + 3 := by omega
  simp only [pathExtremalEdges, componentCliqueTerm, h₁, h₂, h₃,
    show (1 : ℕ).choose 2 = 0 by decide, add_zero, one_mul]
  omega

lemma odd_smaller_path_top {n l : ℕ} (hl : 3 ≤ l) (hn : 2 * l + 1 ≤ n) :
    pathExtremalEdges (n - 1) (2 * l - 2) (l - 2) + (n - 1) =
      pathExtremalEdges n (2 * l) (l - 1) := by
  have h₁ := pathExtremalEdges_twice (n - 1) (2 * l - 2) (l - 2) (by omega) (by omega)
  have h₂ := pathExtremalEdges_twice n (2 * l) (l - 1) (by omega) (by omega)
  have hc₁ : ((n - 1 : ℕ) : ℚ) = n - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hc₂ : ((2 * l - 2 : ℕ) : ℚ) = 2 * l - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
  have hc₃ : ((l - 2 : ℕ) : ℚ) = l - 2 := by rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
  have hc₄ : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [hc₁, hc₂, hc₃, hc₄, Nat.cast_mul, Nat.cast_ofNat] at h₁ h₂
  have h : (pathExtremalEdges (n - 1) (2 * l - 2) (l - 2) : ℚ) + (n - 1 : ℕ) =
      pathExtremalEdges n (2 * l) (l - 1) := by rw [hc₁]; nlinarith
  exact_mod_cast h

lemma even_smaller_path_top {n l : ℕ} (hl : 2 ≤ l) (hn : 2 * l + 2 ≤ n) :
    pathExtremalEdges (n - 1) (2 * l - 1) (l - 1) + (l + 1) =
      (l - 1).choose 2 + (l - 1) * (n - l + 1) + 2 := by
  have h₁ := pathExtremalEdges_twice (n - 1) (2 * l - 1) (l - 1) (by omega) (by omega)
  have h₂ := pathExtremalEdges_twice n (2 * l + 1) (l - 1) (by omega) (by omega)
  have hc₁ : ((n - 1 : ℕ) : ℚ) = n - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hc₂ : ((2 * l - 1 : ℕ) : ℚ) = 2 * l - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hc₃ : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [hc₁, hc₂, hc₃, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h₁ h₂
  have h : (pathExtremalEdges (n - 1) (2 * l - 1) (l - 1) : ℚ) + l + 2 =
      pathExtremalEdges n (2 * l + 1) (l - 1) := by nlinarith
  have hNat : pathExtremalEdges (n - 1) (2 * l - 1) (l - 1) + l + 2 =
      pathExtremalEdges n (2 * l + 1) (l - 1) := by exact_mod_cast h
  rw [even_path_linear_term n l (by omega) (by omega)] at hNat
  omega

theorem smaller_pathExtremal_le_pathFormula {n k j a : ℕ}
    (hj : 4 ≤ j) (hjk : j + 2 ≤ k) (hn : k ≤ n) (ha : 1 ≤ a) (haj : 2 * a ≤ j - 2) :
    pathExtremalEdges (n - 1) (j - 1) a ≤ pathFormula n k := by
  let l := (k - 1) / 2
  let t := (k - 4) / 2
  have hl : 2 ≤ l := by dsimp [l]; omega
  have hat : a ≤ t := by dsimp [t]; omega
  have hkcases : k = 2 * l + 1 ∨ k = 2 * l + 2 := by dsimp [l]; omega
  apply (pathExtremalEdges_mono_clique (by omega) (by omega : j - 1 ≤ k - 3)
    (by omega : k - 3 ≤ n - 1)).trans
  apply (pathExtremalEdges_le_max (n - 1) (k - 3) 1 a t ha hat (by dsimp [t]; omega)
    (by omega)).trans
  apply max_le
  · exact (pathExtremal_one_le_componentCliqueTerm (by omega) hn).trans
      (componentCliqueTerm_le_pathFormula (by omega) hn le_rfl (by omega))
  · rcases hkcases with hk' | hk'
    · have ht : t = l - 2 := by dsimp [t]; omega
      have hK : k - 3 = 2 * l - 2 := by omega
      rw [ht, hK, hk', pathFormula_odd n l (by omega) (by omega)]
      have h := odd_smaller_path_top (show 3 ≤ l by omega) (show 2 * l + 1 ≤ n by omega)
      exact (show pathExtremalEdges (n - 1) (2 * l - 2) (l - 2) ≤
        pathExtremalEdges n (2 * l) (l - 1) by omega).trans (le_max_right _ _)
    · have ht : t = l - 1 := by dsimp [t]; omega
      have hK : k - 3 = 2 * l - 1 := by omega
      rw [ht, hK, hk', pathFormula_even]
      have h := even_smaller_path_top hl (show 2 * l + 2 ≤ n by omega)
      exact (show pathExtremalEdges (n - 1) (2 * l - 1) (l - 1) ≤
        (l - 1).choose 2 + (l - 1) * (n - l + 1) + 2 by omega).trans (le_max_right _ _)

end Erdos1105

#print axioms Erdos1105.smaller_pathExtremal_le_pathFormula
