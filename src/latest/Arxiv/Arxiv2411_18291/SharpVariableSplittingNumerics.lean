import Arxiv.Arxiv2411_18291.VariableSplittingNumerics

/-! # Sharper variable splitting from the capped decoder density -/

noncomputable section

namespace Arxiv2411_18291

theorem variable_splitting_output_factor_paper_threshold {q r n M : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hM : M ≤ (4 * q) ^ (2 * q)) :
    (1 + M * (16 * (r + 1).factorial) : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 15) := by
  have hq : 2 ≤ q := by omega
  have hb : 1 ≤ 4 * q := by omega
  have hf : (r + 1).factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hqr.le).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  have hprod : M * (16 * (r + 1).factorial) ≤ (4 * q) ^ (3 * q + 2) := by
    calc
      _ ≤ (4 * q) ^ (2 * q) * ((4 * q) ^ 2 * (4 * q) ^ q) :=
        Nat.mul_le_mul hM (Nat.mul_le_mul (by nlinarith only [hq]) hf)
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hc : 1 + M * (16 * (r + 1).factorial) ≤ (4 * q) ^ (6 * q) := by
    have hp : 1 ≤ (4 * q) ^ (3 * q + 2) := one_le_pow₀ hb
    calc
      _ ≤ (4 * q) ^ (3 * q + 3) := by
        rw [show 3 * q + 3 = (3 * q + 2) + 1 by omega, pow_succ]
        nlinarith only [hprod, hp, show 2 ≤ 4 * q by omega]
      _ ≤ _ := Nat.pow_le_pow_right hb (by omega)
  have hcoef : (1 + M * (16 * (r + 1).factorial) : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 15) := by
    have hcR : (1 + M * (16 * (r + 1).factorial) : ℝ) ≤
        (4 * q : ℝ) ^ (6 * q) := by exact_mod_cast hc
    have hg := paper_threshold_alpha_rpow_lower (s := 6 * q) hqr hn
      (by norm_num : (0 : ℝ) ≤ 1 / 15) (by push_cast; linarith)
    exact hcR.trans (by simpa only [div_eq_mul_inv, one_mul] using hg)
  exact hcoef

theorem variable_splitting_finite_conditions_at_exponent {q r n w M : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : w ≤ (4 * q) ^ (2 * q)) (hM : M ≤ (4 * q) ^ (2 * q))
    {s : ℝ} (hs : 2 * paperAlpha q (r + 1) / 5 ≤ s) (hshalf : s ≤ 1 / 2) :
    let θ := (n : ℝ) ^ (-s)
    ∃ d : ℕ, (q.choose r : ℝ) * (2 * θ * n) ≤ d ∧
      0 < n ∧ 4 * w ^ 2 ≤ n ∧ 4 * w * (d * w) ≤ n ∧
      (M : ℝ) * (2 * θ + M * (8 * (r + 1).factorial * (2 * θ))) ≤ 1 / 4 ∧
      (M : ℝ) * n.choose r * Real.exp (-(4 * (r + 1).factorial * (2 * θ) * n / 3)) < 1 := by
  dsimp only
  have hα := paperAlpha_pos hqr
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hscale : (n : ℝ) ^ (-s) ≤
      (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hs)
  have hAb : (2 : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) := by
    calc
      _ ≤ (4 * q : ℝ) ^ 1 := by rw [pow_one]; exact_mod_cast (show 2 ≤ 4 * q by omega)
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)) (by omega)
  obtain ⟨hn0, hsize, _, hsmall, hfailure⟩ := small_pattern_separated_greedy_numerics
    hqr hn hw hM (d := 0) (Nat.zero_le _) (A := 2) (by norm_num) hAb
    (by linarith only [hs, hα] : paperAlpha q (r + 1) / 3 ≤ s) hshalf
  let d : ℕ := ⌈(q.choose r : ℝ) * (2 * (n : ℝ) ^ (-s) * n)⌉₊
  have hd : d ≤ ⌈(q.choose r : ℝ) *
      (2 * (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) * n)⌉₊ := by
    apply Nat.ceil_mono
    gcongr
  have hfree : 4 * w * (d * w) ≤ n :=
    (Nat.mul_le_mul_left (4 * w) (Nat.mul_le_mul_right w hd)).trans
      (variable_splitting_conflict_size hqr hn hw)
  exact ⟨d, Nat.le_ceil _, hn0, hsize, hfree, hsmall, hfailure⟩

theorem sharp_variable_splitting_output_density {q r n M : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hM : M ≤ (4 * q) ^ (2 * q)) :
    (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30)) +
      M * (16 * (r + 1).factorial * (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30))) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  calc
    _ = (1 + M * (16 * (r + 1).factorial)) *
        (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30)) := by ring
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 15) *
        (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30)) :=
      mul_le_mul_of_nonneg_right (variable_splitting_output_factor_paper_threshold hqr hn hM)
        (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem sharp_variable_splitting_clique_density {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    2 * (q - r : ℕ) * (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30)) +
      2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) ≤
        (n : ℝ) ^ (-(89 * paperAlpha q (r + 1) / 180)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hα := paperAlpha_pos hqr
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hscale : (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα])
  have hcoef : (2 * (q - r : ℕ) + 2 : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 180) := by
    have hnat : 2 * (q - r) + 2 ≤ 4 * q := by omega
    have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 1)
      (t := (1 / 180 : ℝ)) (by norm_num) (by linarith only [hq])
    exact (by exact_mod_cast hnat : (2 * (q - r : ℕ) + 2 : ℝ) ≤ 4 * q).trans
      (by simpa only [pow_one, div_eq_mul_inv, one_mul] using hg)
  calc
    _ ≤ 2 * (q - r : ℕ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) +
        2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) := by gcongr
    _ = (2 * (q - r : ℕ) + 2) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) := by ring
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 180) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
