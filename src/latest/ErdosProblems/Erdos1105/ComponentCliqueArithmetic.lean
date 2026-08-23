import ErdosProblems.Erdos1105.PathFormulaArithmetic
import ErdosProblems.Erdos1105.CappedEdges

namespace Erdos1105

lemma quadratic_le_max (A B C l x u : ℚ) (hA : 0 ≤ A) (hlx : l ≤ x) (hxu : x ≤ u) :
    A * x ^ 2 + B * x + C ≤ max (A * l ^ 2 + B * l + C) (A * u ^ 2 + B * u + C) := by
  by_contra! h
  have hleft := lt_of_le_of_lt (le_max_left _ _) h
  have hright := lt_of_le_of_lt (le_max_right _ _) h
  have hslope : 0 < A * (x + l) + B := by
    by_contra! hs
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlx) hs
    nlinarith
  have hm := mul_nonneg hA (show 0 ≤ u - l by linarith)
  have hslope' : 0 ≤ A * (u + x) + B := by nlinarith
  have hm' := mul_nonneg (sub_nonneg.mpr hxu) hslope'
  nlinarith

/-- The endpoint count with a largest complete component and a
degeneracy bound for all other components. -/
def componentCliqueTerm (n k b : ℕ) : ℕ :=
  (k - b - 2).choose 2 + b.choose 2 + b * (n - k + 2)

lemma componentCliqueTerm_twice (n k b : ℕ) (hb : b + 2 ≤ k) (hn : k ≤ n) :
    2 * (componentCliqueTerm n k b : ℚ) =
      2 * (b : ℚ) ^ 2 + (2 * n - 4 * k + 8) * b + ((k : ℚ) - 2) * (k - 3) := by
  simp only [componentCliqueTerm, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
    Nat.cast_sub (show 2 ≤ k - b by omega), Nat.cast_sub (show b ≤ k by omega),
    Nat.cast_sub hn, Nat.cast_ofNat]
  ring

lemma componentCliqueTerm_le_max {n k b s : ℕ}
    (hb : 1 ≤ b) (hbs : b ≤ s) (hs : s + 2 ≤ k) (hn : k ≤ n) :
    componentCliqueTerm n k b ≤ max (componentCliqueTerm n k 1) (componentCliqueTerm n k s) := by
  have h := quadratic_le_max 2 (2 * n - 4 * k + 8) (((k : ℚ) - 2) * (k - 3))
    1 b s (by norm_num) (by exact_mod_cast hb) (by exact_mod_cast hbs)
  have h₁ := componentCliqueTerm_twice n k 1 (by omega) hn
  have hb' := componentCliqueTerm_twice n k b (by omega) hn
  have hs' := componentCliqueTerm_twice n k s hs hn
  norm_num only [Nat.cast_one] at h₁ h
  rw [← h₁, ← hb', ← hs'] at h
  rcases le_max_iff.mp h with h | h
  · apply le_trans ?_ (le_max_left _ _)
    have hh : (componentCliqueTerm n k b : ℚ) ≤ componentCliqueTerm n k 1 := by linarith
    exact_mod_cast hh
  · apply le_trans ?_ (le_max_right _ _)
    have hh : (componentCliqueTerm n k b : ℚ) ≤ componentCliqueTerm n k s := by linarith
    exact_mod_cast hh

lemma clique_plus_capped_eq_componentTerm {n k₁ k₂ : ℕ} (hk₂ : 3 ≤ k₂)
    (hn : k₁ + k₂ - 1 ≤ n) (hk₁ : 1 ≤ k₁) :
    (k₁ - 1).choose 2 + cappedEdgeBound (n - k₁ + 1) (k₂ - 2) =
      componentCliqueTerm n (k₁ + k₂ - 1) (k₂ - 2) := by
  rw [cappedEdgeBound_eq_linear (by omega)]
  have h₁ : k₁ + k₂ - 1 - (k₂ - 2) - 2 = k₁ - 1 := by omega
  have h₂ : n - k₁ + 1 - (k₂ - 2) = n - (k₁ + k₂ - 1) + 2 := by omega
  simp only [componentCliqueTerm, h₁, h₂]
  omega

end Erdos1105

#print axioms Erdos1105.componentCliqueTerm_le_max
