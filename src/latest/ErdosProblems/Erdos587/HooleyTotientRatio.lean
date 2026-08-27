import ErdosProblems.Erdos360.TotientStep

/-!
# A uniform maximal-order bound for the slope's totient ratio

The proved eventual estimate from the 360 development extends to all
integer cutoffs by absorbing finitely many small values. A squared
ambient cutoff costs only a fixed factor in the log-log bound.
-/

namespace Erdos587

theorem exists_delta_totient_ratio_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N b : ℕ, 0 < b → b ≤ N →
      (b : ℝ) / b.totient ≤ C * max 1 (Real.log (Real.log (N : ℝ))) := by
  obtain ⟨C₀, hC₀, hratio⟩ := Erdos360.exists_eventually_totientRatio_le_loglog
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hratio
  refine ⟨C₀ + N₀ + 1, by positivity, ?_⟩
  intro N b hb hbN
  have hL : (1 : ℝ) ≤ max 1 (Real.log (Real.log (N : ℝ))) := le_max_left _ _
  by_cases hN : N₀ ≤ N
  · calc
      _ ≤ C₀ * Real.log (Real.log (N : ℝ)) := hN₀ N hN b hb hbN
      _ ≤ C₀ * max 1 (Real.log (Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hC₀.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by have := Nat.cast_nonneg (α := ℝ) N₀; linarith : C₀ ≤ C₀ + (N₀ : ℝ) + 1)
        (zero_le_one.trans hL)
  · have ht : (1 : ℝ) ≤ b.totient := by exact_mod_cast Nat.totient_pos.mpr hb
    have hbsmall : (b : ℝ) ≤ N₀ := by exact_mod_cast (hbN.trans (le_of_lt (lt_of_not_ge hN)))
    calc
      _ ≤ (b : ℝ) := div_le_self (by positivity) ht
      _ ≤ (N₀ : ℝ) := hbsmall
      _ ≤ C₀ + (N₀ : ℝ) + 1 := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hL

lemma delta_loglog_square_le {N : ℕ} (hN : 2 ≤ N) :
    max 1 (Real.log (Real.log ((N ^ 2 : ℕ) : ℝ))) ≤
      2 * max 1 (Real.log (Real.log (N : ℝ))) := by
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogN.ne']
  apply max_le
  · have h := le_max_left (1 : ℝ) (Real.log (Real.log (N : ℝ)))
    linarith
  · have h₁ := le_max_left (1 : ℝ) (Real.log (Real.log (N : ℝ)))
    have h₂ := le_max_right (1 : ℝ) (Real.log (Real.log (N : ℝ)))
    linarith

theorem exists_delta_totient_ratio_square_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N b : ℕ, 2 ≤ N → 0 < b → b ≤ N ^ 2 →
      (b : ℝ) / b.totient ≤ C * max 1 (Real.log (Real.log (N : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_totient_ratio_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro N b hN hb hbN
  calc
    _ ≤ C * max 1 (Real.log (Real.log ((N ^ 2 : ℕ) : ℝ))) := hbound _ b hb hbN
    _ ≤ C * (2 * max 1 (Real.log (Real.log (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left (delta_loglog_square_le hN) hC.le
    _ = _ := by ring

end Erdos587
