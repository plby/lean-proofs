import ErdosProblems.Erdos421.LogarithmicRoughAsymptotic

/-! # Explicit error decay at an inverse-logarithmic reference width -/

namespace Erdos421

theorem reference_delta_bounds {l L : ℝ} (hl : 1 ≤ l) (hL : 2 ≤ L) :
    0 < l ^ (-L) ∧ l ^ (-L) ≤ 1 / l ^ (2 : ℕ) ∧ l ^ (-L) ≤ 1 := by
  have hlp : 0 < l := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hl hL
  norm_num only [Real.rpow_ofNat] at hpow
  have hδ : l ^ (-L) ≤ 1 / l ^ (2 : ℕ) := by
    rw [Real.rpow_neg hlp.le, one_div]
    exact inv_anti₀ (sq_pos_of_pos hlp) hpow
  refine ⟨Real.rpow_pos_of_pos hlp _, hδ, hδ.trans ?_⟩
  exact (div_le_one (sq_pos_of_pos hlp)).mpr (by nlinarith)

theorem reference_log_error_le {l R L β C D : ℝ} (hl : 1 ≤ l) (hL : 2 ≤ L)
    (hβ : 0 < β) (hR : β * l ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    C / (l ^ (-L) * R ^ (L + 2)) + C * D * l ^ (-L) / R ^ (2 : ℕ) ≤
      (C / β ^ (L + 2) + C * D / β ^ (2 : ℕ)) / l ^ (2 : ℕ) := by
  have hlp : 0 < l := by linarith
  have hRp : 0 < R := (mul_pos hβ hlp).trans_le hR
  have hA : 0 ≤ L + 2 := by linarith
  obtain ⟨hδ, _, hδ1⟩ := reference_delta_bounds hl hL
  have hcancel : l ^ (-L) * l ^ (L + 2) = l ^ (2 : ℕ) := by
    rw [← Real.rpow_add hlp, show -L + (L + 2) = 2 by ring]
    norm_num only [Real.rpow_ofNat]
  have hp := Real.rpow_le_rpow (mul_pos hβ hlp).le hR hA
  rw [Real.mul_rpow hβ.le hlp.le] at hp
  have hden : β ^ (L + 2) * l ^ (2 : ℕ) ≤ l ^ (-L) * R ^ (L + 2) := by
    calc
      _ = l ^ (-L) * (β ^ (L + 2) * l ^ (L + 2)) := by rw [← hcancel]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hδ.le
  have hmain : C / (l ^ (-L) * R ^ (L + 2)) ≤ C / (β ^ (L + 2) * l ^ (2 : ℕ)) :=
    div_le_div_of_nonneg_left hC (by positivity) hden
  have hden2 : β ^ (2 : ℕ) * l ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_pos hβ hlp).le hR 2
  have hquad : C * D * l ^ (-L) / R ^ (2 : ℕ) ≤ C * D / (β ^ (2 : ℕ) * l ^ (2 : ℕ)) := by
    calc
      _ ≤ C * D / R ^ (2 : ℕ) := div_le_div_of_nonneg_right
        (mul_le_of_le_one_right (mul_nonneg hC hD) hδ1) (sq_nonneg R)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hC hD) (by positivity) hden2
  exact (add_le_add hmain hquad).trans_eq (by ring)

end Erdos421
