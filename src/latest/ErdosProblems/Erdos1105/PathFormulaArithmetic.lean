import ErdosProblems.Erdos1105.PathExtremalArithmetic

namespace Erdos1105

/-- The proposed exact anti-Ramsey value, with paths counted by vertices. -/
def pathFormula (n k : ℕ) : ℕ :=
  let l := (k - 1) / 2
  max ((k - 2).choose 2 + 1)
    ((l - 1).choose 2 + (l - 1) * (n - l + 1) + if Odd k then 1 else 2)

lemma pathFormula_mono {n m : ℕ} (hnm : n ≤ m) (k : ℕ) :
    pathFormula n k ≤ pathFormula m k := by
  dsimp [pathFormula]
  gcongr

lemma odd_path_linear_term (n l : ℕ) (hl : 1 ≤ l) (hn : 2 * l ≤ n) :
    pathExtremalEdges n (2 * l) (l - 1) =
      (l - 1).choose 2 + (l - 1) * (n - l + 1) + 1 := by
  have hpred : l - 1 + 1 = l := by omega
  have hc₁ := Nat.choose_succ_succ (l - 1) 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hpred, Nat.choose_one_right] at hc₁
  have hc₂ := Nat.choose_succ_succ l 1
  simp only [Nat.choose_one_right] at hc₂
  change (l + 1).choose 2 = l + l.choose 2 at hc₂
  have hsub : 2 * l - (l - 1) = l + 1 := by omega
  have hrest : n - 2 * l + (l - 1) + 2 = n - l + 1 := by omega
  simp only [pathExtremalEdges, hsub]
  rw [← hrest]
  nlinarith

lemma even_path_linear_term (n l : ℕ) (hl : 1 ≤ l) (hn : 2 * l + 1 ≤ n) :
    pathExtremalEdges n (2 * l + 1) (l - 1) =
      (l - 1).choose 2 + (l - 1) * (n - l + 1) + 3 := by
  have hpred : l - 1 + 1 = l := by omega
  have hc₁ := Nat.choose_succ_succ (l - 1) 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hpred, Nat.choose_one_right] at hc₁
  have hc₂ := Nat.choose_succ_succ l 1
  simp only [Nat.choose_one_right] at hc₂
  change (l + 1).choose 2 = l + l.choose 2 at hc₂
  have hc₃ := Nat.choose_succ_succ (l + 1) 1
  simp only [Nat.choose_one_right] at hc₃
  change (l + 2).choose 2 = l + 1 + (l + 1).choose 2 at hc₃
  have hsub : 2 * l + 1 - (l - 1) = l + 2 := by omega
  have hrest : n - (2 * l + 1) + (l - 1) + 3 = n - l + 1 := by omega
  simp only [pathExtremalEdges, hsub]
  rw [← hrest]
  nlinarith

lemma pathFormula_even (n l : ℕ) :
    pathFormula n (2 * l + 2) = max ((2 * l).choose 2 + 1)
      ((l - 1).choose 2 + (l - 1) * (n - l + 1) + 2) := by
  have hdiv : (2 * l + 2 - 1) / 2 = l := by omega
  have hsub : 2 * l + 2 - 2 = 2 * l := by omega
  have hodd : ¬Odd (2 * l + 2) := by rintro ⟨a, ha⟩; omega
  simp only [pathFormula, hdiv, hsub, if_neg hodd]

lemma pathFormula_odd (n l : ℕ) (hl : 1 ≤ l) (hn : 2 * l ≤ n) :
    pathFormula n (2 * l + 1) =
      max ((2 * l - 1).choose 2 + 1) (pathExtremalEdges n (2 * l) (l - 1)) := by
  have hdiv : (2 * l + 1 - 1) / 2 = l := by omega
  have hsub : 2 * l + 1 - 2 = 2 * l - 1 := by omega
  have hodd : Odd (2 * l + 1) := ⟨l, rfl⟩
  simp only [pathFormula, hdiv, hsub, if_pos hodd, odd_path_linear_term n l hl hn]

/-- The non-endpoint stability threshold lies below the conjectured
anti-Ramsey value for odd paths of order at least nine. -/
lemma odd_path_stability_threshold (n l : ℕ) (hl : 4 ≤ l) (hn : 2 * l + 1 ≤ n) :
    max (pathExtremalEdges n (2 * l) 2) (pathExtremalEdges n (2 * l) (l - 1)) ≤
      pathFormula n (2 * l + 1) := by
  rw [pathFormula_odd n l (by omega) (by omega)]
  apply max_le ?_ (le_max_right _ _)
  have h₂ := pathExtremalEdges_twice n (2 * l) 2 (by omega) (by omega)
  have hd := pathExtremalEdges_twice n (2 * l) (l - 1) (by omega) (by omega)
  have hC := Nat.cast_choose_two ℚ (2 * l - 1)
  have hl' : (4 : ℚ) ≤ l := by exact_mod_cast hl
  have hn' : (2 : ℚ) * l + 1 ≤ n := by exact_mod_cast hn
  have hpred : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hpred₂ : ((2 * l - 1 : ℕ) : ℚ) = 2 * l - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  simp only [Nat.cast_mul, Nat.cast_ofNat, hpred, hpred₂] at h₂ hd hC
  by_cases hsmall : n ≤ 3 * l - 3
  · apply le_trans ?_ (le_max_left _ _)
    have hsmall' : (n : ℚ) ≤ 3 * l - 3 := by
      have h : n + 3 ≤ 3 * l := by omega
      have h' : (n : ℚ) + 3 ≤ 3 * l := by exact_mod_cast h
      linarith
    have hb : (pathExtremalEdges n (2 * l) 2 : ℚ) ≤
        (2 * l - 1).choose 2 + 1 := by nlinarith
    exact_mod_cast hb
  · apply le_trans ?_ (le_max_right _ _)
    have hlarge : (3 : ℚ) * l - 2 ≤ n := by
      have h : 3 * l ≤ n + 2 := by omega
      have h' : (3 : ℚ) * l ≤ n + 2 := by exact_mod_cast h
      linarith
    have hm₁ := mul_nonneg (show (0 : ℚ) ≤ l - 3 by linarith)
      (show (0 : ℚ) ≤ n - (3 * l - 2) by linarith)
    have hm₂ := mul_nonneg (show (0 : ℚ) ≤ l by positivity)
      (show (0 : ℚ) ≤ l - 3 by linarith)
    have hb : (pathExtremalEdges n (2 * l) 2 : ℚ) ≤
        pathExtremalEdges n (2 * l) (l - 1) := by nlinarith
    exact_mod_cast hb

lemma odd_pendant_order_bound (n l q : ℕ) (hl : 4 ≤ l) (hn : 2 * l + 1 ≤ n)
    (hq : pathFormula n (2 * l + 1) < q)
    (hupper : q ≤ pathExtremalEdges n (2 * l) 1) : n ≤ 3 * l - 2 := by
  have hlin : pathExtremalEdges n (2 * l) (l - 1) < pathExtremalEdges n (2 * l) 1 := by
    rw [pathFormula_odd n l (by omega) (by omega)] at hq
    exact (lt_of_le_of_lt (le_max_right _ _) hq).trans_le hupper
  have h₁ := pathExtremalEdges_twice n (2 * l) 1 (by omega) (by omega)
  have hd := pathExtremalEdges_twice n (2 * l) (l - 1) (by omega) (by omega)
  have hl' : (4 : ℚ) ≤ l := by exact_mod_cast hl
  have hlin' : (pathExtremalEdges n (2 * l) (l - 1) : ℚ) <
      pathExtremalEdges n (2 * l) 1 := by exact_mod_cast hlin
  have hpred : ((l - 1 : ℕ) : ℚ) = l - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hpred] at h₁ hd
  by_contra! hlarge
  have hn' : (3 : ℚ) * l - 1 ≤ n := by
    have h : 3 * l ≤ n + 1 := by omega
    have h' : (3 : ℚ) * l ≤ n + 1 := by exact_mod_cast h
    linarith
  have hm₁ := mul_nonneg (show (0 : ℚ) ≤ l - 2 by linarith)
    (show (0 : ℚ) ≤ n - (3 * l - 1) by linarith)
  have hm₂ := mul_nonneg (show (0 : ℚ) ≤ l - 1 by linarith)
    (show (0 : ℚ) ≤ l - 2 by linarith)
  nlinarith

end Erdos1105

#print axioms Erdos1105.odd_path_stability_threshold
