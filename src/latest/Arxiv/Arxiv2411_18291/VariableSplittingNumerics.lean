import Arxiv.Arxiv2411_18291.SmallPatternGreedyNumerics

/-! # Splitting with a conflict count depending on the ambient size

The rounded conflict cap is proportional to `theta*n`. Its contribution to
the forbidden free vertices is bounded directly, without pretending that
the cap is a constant depending only on the clique parameters.
-/

noncomputable section

namespace Arxiv2411_18291

theorem variable_splitting_conflict_size {q r n w : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hw : w ≤ (4 * q) ^ (2 * q)) :
    4 * w * (⌈(q.choose r : ℝ) *
      (2 * (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) * n)⌉₊ * w) ≤ n := by
  have hq : 2 ≤ q := by omega
  have hb : 1 ≤ 4 * q := by omega
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  let θ := (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5))
  have hθ : 0 ≤ θ := by dsimp only [θ]; positivity
  have hK : q.choose r ≤ (4 * q) ^ q :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hc : 16 * w ^ 2 * q.choose r ≤ (4 * q) ^ (5 * q + 2) := by
    calc
      _ ≤ (4 * q) ^ 2 * ((4 * q) ^ (2 * q)) ^ 2 * (4 * q) ^ q :=
        Nat.mul_le_mul (Nat.mul_le_mul (by nlinarith only [hq])
          (Nat.pow_le_pow_left hw 2)) hK
      _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
  have hcoef : (16 * w ^ 2 * q.choose r : ℝ) ≤
      (n : ℝ) ^ (2 * paperAlpha q (r + 1) / 5) := by
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hg := paper_threshold_alpha_rpow_lower (s := 5 * q + 2) hqr hn
      (by norm_num : (0 : ℝ) ≤ 2 / 5) (by push_cast; linarith only [hqR])
    have hcR : (16 * w ^ 2 * q.choose r : ℝ) ≤ (4 * q : ℝ) ^ (5 * q + 2) := by
      exact_mod_cast hc
    apply hcR.trans
    simpa only [show paperAlpha q (r + 1) * (2 / 5) =
      2 * paperAlpha q (r + 1) / 5 by ring] using hg
  have hcoefθ : (16 * w ^ 2 * q.choose r : ℝ) * θ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hcoef hθ
    dsimp only [θ] at hh
    rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hh
    exact hh
  have hsize : 8 * w ^ 2 ≤ n := by
    calc
      _ ≤ (4 * q) ^ 1 * ((4 * q) ^ (2 * q)) ^ 2 :=
        Nat.mul_le_mul (by simp only [pow_one]; omega) (Nat.pow_le_pow_left hw 2)
      _ = (4 * q) ^ (4 * q + 1) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ ≤ (4 * q) ^ (90 * q) := Nat.pow_le_pow_right hb (by omega)
      _ ≤ n := (boost_threshold_le_paper_threshold hqr).trans hn
  let d : ℕ := ⌈(q.choose r : ℝ) * (2 * θ * n)⌉₊
  have hd : (d : ℝ) ≤ (q.choose r : ℝ) * (2 * θ * n) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hdw := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 4 * w ^ 2)
  have hcofn := mul_le_mul_of_nonneg_right hcoefθ hn0.le
  have hsizeR : (8 * w ^ 2 : ℝ) ≤ n := by exact_mod_cast hsize
  have hfinal : (4 * w * (d * w) : ℝ) ≤ n := by
    nlinarith only [hdw, hcofn, hsizeR]
  exact_mod_cast hfinal

theorem variable_splitting_paper_numerics {q r n w M : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : w ≤ (4 * q) ^ (2 * q)) (hM : M ≤ (4 * q) ^ (2 * q)) :
    let θ := (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5))
    ∃ d : ℕ, (q.choose r : ℝ) * (2 * θ * n) ≤ d ∧
      0 < n ∧ 4 * w ^ 2 ≤ n ∧ 4 * w * (d * w) ≤ n ∧
      (M : ℝ) * (2 * θ + M * (8 * (r + 1).factorial * (2 * θ))) ≤ 1 / 4 ∧
      (M : ℝ) * n.choose r * Real.exp (-(4 * (r + 1).factorial * (2 * θ) * n / 3)) < 1 := by
  dsimp only
  have hα := paperAlpha_pos hqr
  have hαmax := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hAb : (2 : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) := by
    calc
      _ ≤ (4 * q : ℝ) ^ 1 := by
        rw [pow_one]
        exact_mod_cast (show 2 ≤ 4 * q by omega)
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)) (by omega)
  obtain ⟨hn0, hsize, _, hsmall, hfailure⟩ := small_pattern_separated_greedy_numerics
    hqr hn hw hM (d := 0) (Nat.zero_le _) (A := 2) (by norm_num) hAb
    (ρ := 2 * paperAlpha q (r + 1) / 5) (by linarith only [hα])
    (by linarith only [hαmax])
  refine ⟨⌈(q.choose r : ℝ) *
    (2 * (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) * n)⌉₊,
      Nat.le_ceil _, hn0, hsize, variable_splitting_conflict_size hqr hn hw, hsmall, hfailure⟩

theorem variable_splitting_output_density {q r n M : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hM : M ≤ (4 * q) ^ (2 * q)) :
    (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) +
      M * (16 * (r + 1).factorial * (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5))) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) := by
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
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  calc
    _ = (1 + M * (16 * (r + 1).factorial)) *
        (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) := by ring
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 15) *
        (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
