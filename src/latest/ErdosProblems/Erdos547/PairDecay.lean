import ErdosProblems.Erdos547.PairChoices

/-!
# A uniform contraction factor for repeated pair choices
-/

namespace Erdos547

/-- A common upper bound for the contraction factor while at most `k/2`
vertices have been used. -/
noncomputable def pairDecay (N k : ℕ) : ℝ := 1 - (k : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2)

theorem pairDecay_nonneg {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) : 0 ≤ pairDecay N k := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsq : (k : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hden : 0 < 8 * (N : ℝ) ^ 2 := by positivity
  have hfrac : (k : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2) ≤ 1 :=
    (div_le_one hden).mpr (by nlinarith)
  exact sub_nonneg.mpr hfrac

theorem pairDecay_le_one (N k : ℕ) : pairDecay N k ≤ 1 := by
  unfold pairDecay
  have h : 0 ≤ (k : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2) := by positivity
  linarith

theorem pair_factor_le_pairDecay {N k s : ℕ} (hN : 0 < N) (hs : 2 * s ≤ k) :
    1 - (((k - s : ℕ) : ℝ) ^ 2 / (N : ℝ) ^ 2) / 2 ≤ pairDecay N k := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsr : 2 * (s : ℝ) ≤ k := by exact_mod_cast hs
  have hsub : ((k - s : ℕ) : ℝ) = (k : ℝ) - s := Nat.cast_sub (by omega)
  have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsn : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hsquare : (k : ℝ) ^ 2 ≤ 4 * ((k : ℝ) - s) ^ 2 := by
    nlinarith [sq_nonneg ((k : ℝ) - 2 * s)]
  unfold pairDecay
  rw [hsub]
  have hden : 0 < 8 * (N : ℝ) ^ 2 := by positivity
  apply le_of_mul_le_mul_left (a := 8 * (N : ℝ) ^ 2) ?_ hden
  field_simp [ne_of_gt hNr]
  nlinarith only [hsquare]

end Erdos547

#print axioms Erdos547.pair_factor_le_pairDecay
