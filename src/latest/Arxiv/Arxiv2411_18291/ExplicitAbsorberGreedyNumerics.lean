import Arxiv.Arxiv2411_18291.PaperAlphaGrowth
import Arxiv.Arxiv2411_18291.ExplicitAbsorberGreedyTail

/-! # Uniform finite numerics at the absorber's working density -/

namespace Arxiv2411_18291

theorem absorber_greedy_coefficient_le {q r M : ℕ} (hq : 2 ≤ q) (hr : r ≤ q)
    (hMb : M ≤ (4 * q) ^ (8 * q)) :
    4 * M * (1 + 4 * M * r.factorial) ≤ (4 * q) ^ (17 * q + 2) := by
  have hfac : 1 ≤ r.factorial := Nat.factorial_pos r
  have hMM : M ≤ M ^ 2 := Nat.le_self_pow two_ne_zero M
  have hMMf : M ≤ M ^ 2 * r.factorial :=
    hMM.trans (by simpa using Nat.mul_le_mul_left (M ^ 2) hfac)
  have htwenty : 20 ≤ (4 * q) ^ 2 := by nlinarith only [hq]
  have hfacb : r.factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hr).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  calc
    _ ≤ 20 * M ^ 2 * r.factorial := by nlinarith only [hMMf]
    _ ≤ (4 * q) ^ 2 * ((4 * q) ^ (8 * q)) ^ 2 * (4 * q) ^ q :=
      Nat.mul_le_mul (Nat.mul_le_mul htwenty (Nat.pow_le_pow_left hMb 2)) hfacb
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega

theorem absorber_greedy_numerics {q r n w M : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : w ≤ (4 * q) ^ (8 * q)) (hMb : M ≤ (4 * q) ^ (8 * q))
    {A : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (8 * q)) :
    let θ := A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))
    0 < n ∧ 4 * w ^ 2 ≤ n ∧
      (M : ℝ) * (θ + M * (4 * (r + 1).factorial * θ)) ≤ 1 / 4 ∧
      (M : ℝ) * n.choose r * Real.exp (-(2 * (r + 1).factorial * θ * n / 3)) < 1 := by
  dsimp only
  let α := paperAlpha q (r + 1)
  have hq : 2 ≤ q := by omega
  have hboost := (boost_threshold_le_paper_threshold hqr).trans hn
  have hnNat : 0 < n := Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hMsize : M ≤ n := hMb.trans
    ((Nat.pow_le_pow_right (by omega) (by omega : 8 * q ≤ 90 * q)).trans hboost)
  refine ⟨hnNat, ?_, ?_, ?_⟩
  · calc
      _ ≤ (4 * q) ^ 1 * ((4 * q) ^ (8 * q)) ^ 2 :=
        Nat.mul_le_mul (by simp only [pow_one]; omega) (Nat.pow_le_pow_left hw 2)
      _ = (4 * q) ^ (1 + (8 * q) * 2) := by rw [← pow_mul, ← pow_add]
      _ ≤ (4 * q) ^ (90 * q) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := hboost
  · have hC : (4 * M * (1 + 4 * M * (r + 1).factorial) : ℝ) ≤
        (4 * q : ℝ) ^ (17 * q + 2) := by
      exact_mod_cast absorber_greedy_coefficient_le hq hqr.le hMb
    have hcoef : (4 * M * (1 + 4 * M * (r + 1).factorial) : ℝ) * A ≤
        (n : ℝ) ^ (α / 3) := by
      calc
        _ ≤ (4 * q : ℝ) ^ (17 * q + 2) * (4 * q : ℝ) ^ (8 * q) :=
          mul_le_mul hC hAb (by linarith only [hA]) (by positivity)
        _ = (4 * q : ℝ) ^ (25 * q + 2) := by rw [← pow_add]; congr 1; omega
        _ ≤ (4 * q : ℝ) ^ (30 * q) :=
          pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)) (by omega)
        _ ≤ _ := paper_threshold_alpha_third hqr hn
    have hh := mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-(α / 3)))
    rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hh
    change (M : ℝ) * (A * (n : ℝ) ^ (-(α / 3)) +
      M * (4 * (r + 1).factorial * (A * (n : ℝ) ^ (-(α / 3))))) ≤ 1 / 4
    nlinarith only [hh]
  · apply absorber_greedy_failure_lt_one hqr hn hMsize
    have hα := paperAlpha_le_rho hqr
    have hρ := paperRho_le_one_div_36 hqr
    have hh : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (n : ℝ) ^ (-(α / 3)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp only [α]; linarith only [hα, hρ])
    exact hh.trans (le_mul_of_one_le_left (Real.rpow_nonneg hn0.le _) hA)

end Arxiv2411_18291
