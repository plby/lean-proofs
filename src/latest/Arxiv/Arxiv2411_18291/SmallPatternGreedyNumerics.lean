import Arxiv.Arxiv2411_18291.ExplicitAbsorberGreedyNumerics

/-! # Larger density constants for the small exchange patterns -/

namespace Arxiv2411_18291

theorem small_pattern_greedy_coefficient_le {q r M : ℕ} (hq : 2 ≤ q) (hr : r ≤ q)
    (hM : M ≤ (4 * q) ^ (2 * q)) :
    4 * M * (1 + 8 * M * r.factorial) ≤ (4 * q) ^ (5 * q + 2) := by
  have hfac : 1 ≤ r.factorial := Nat.factorial_pos r
  have hMMf : M ≤ M ^ 2 * r.factorial :=
    (Nat.le_self_pow two_ne_zero M).trans
      (by simpa using Nat.mul_le_mul_left (M ^ 2) hfac)
  have hc : 36 ≤ (4 * q) ^ 2 := by nlinarith only [hq]
  have hf : r.factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hr).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  calc
    _ ≤ 36 * M ^ 2 * r.factorial := by nlinarith only [hMMf]
    _ ≤ (4 * q) ^ 2 * ((4 * q) ^ (2 * q)) ^ 2 * (4 * q) ^ q :=
      Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_left hM 2)) hf
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega

/-- Small exchange patterns allow density constants up to `(4q)^(24q)`.
The working exponent may range from `alpha/3` to `1/2`; in particular this
does not force the later absorber stages to spend the `alpha/2` margin. -/
theorem small_pattern_separated_greedy_numerics {q r n w M d : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : w ≤ (4 * q) ^ (2 * q)) (hM : M ≤ (4 * q) ^ (2 * q))
    (hd : d ≤ (4 * q) ^ (8 * q)) {A ρ : ℝ}
    (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2) :
    let θ := A * (n : ℝ) ^ (-ρ)
    0 < n ∧ 4 * w ^ 2 ≤ n ∧ 4 * w * (d * w) ≤ n ∧
      (M : ℝ) * (θ + M * (8 * (r + 1).factorial * θ)) ≤ 1 / 4 ∧
      (M : ℝ) * n.choose r * Real.exp (-(4 * (r + 1).factorial * θ * n / 3)) < 1 := by
  dsimp only
  have hq : 2 ≤ q := by omega
  have hboost := (boost_threshold_le_paper_threshold hqr).trans hn
  have hnNat : 0 < n := Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hMsize : M ≤ n := hM.trans
    ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans hboost)
  have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
  refine ⟨hnNat, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ (4 * q) ^ 1 * ((4 * q) ^ (2 * q)) ^ 2 :=
        Nat.mul_le_mul (by simp only [pow_one]; omega) (Nat.pow_le_pow_left hw 2)
      _ = (4 * q) ^ (1 + (2 * q) * 2) := by rw [← pow_mul, ← pow_add]
      _ ≤ (4 * q) ^ (90 * q) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := hboost
  · calc
      _ ≤ (4 * q) ^ 1 * (4 * q) ^ (2 * q) *
          ((4 * q) ^ (8 * q) * (4 * q) ^ (2 * q)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by simp only [pow_one]; omega) hw)
          (Nat.mul_le_mul hd hw)
      _ = (4 * q) ^ (1 + 2 * q + (8 * q + 2 * q)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
      _ ≤ (4 * q) ^ (90 * q) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := hboost
  · have hC : (4 * M * (1 + 8 * M * (r + 1).factorial) : ℝ) ≤
        (4 * q : ℝ) ^ (5 * q + 2) := by
      exact_mod_cast small_pattern_greedy_coefficient_le hq hqr.le hM
    have hcoef : (4 * M * (1 + 8 * M * (r + 1).factorial) : ℝ) * A ≤
        (n : ℝ) ^ ρ := by
      calc
        _ ≤ (4 * q : ℝ) ^ (5 * q + 2) * (4 * q : ℝ) ^ (24 * q) :=
          mul_le_mul hC hAb hAnonneg (by positivity)
        _ = (4 * q : ℝ) ^ (29 * q + 2) := by rw [← pow_add]; congr 1; omega
        _ ≤ (4 * q : ℝ) ^ (30 * q) :=
          pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)) (by omega)
        _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 3) := paper_threshold_alpha_third hqr hn
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hρ
    have hh := mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-ρ))
    rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hh
    nlinarith only [hh]
  · have hθ : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * (A * (n : ℝ) ^ (-ρ)) := by
      have hh := Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hρhalf)
      have hscale : (n : ℝ) ^ (-ρ) ≤ 2 * (A * (n : ℝ) ^ (-ρ)) := by
        have hp := Real.rpow_nonneg hn0.le (-ρ)
        nlinarith only [hA, hp]
      exact hh.trans hscale
    have htail := absorber_greedy_failure_lt_one hqr hn hMsize hθ
    convert htail using 1
    congr 2
    ring

/-- Without a separation constraint the output constant is `4*r!`, at the
same flexible working exponent and density coefficient. -/
theorem small_pattern_greedy_numerics {q r n w M : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : w ≤ (4 * q) ^ (2 * q)) (hM : M ≤ (4 * q) ^ (2 * q))
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2) :
    let θ := A * (n : ℝ) ^ (-ρ)
    0 < n ∧ 4 * w ^ 2 ≤ n ∧
      (M : ℝ) * (θ + M * (4 * (r + 1).factorial * θ)) ≤ 1 / 4 ∧
      (M : ℝ) * n.choose r * Real.exp (-(2 * (r + 1).factorial * θ * n / 3)) < 1 := by
  dsimp only
  obtain ⟨hnpos, hsize, _, hsmall, _⟩ := small_pattern_separated_greedy_numerics
    hqr hn hw hM (d := 0) (Nat.zero_le _) hA hAb hρ hρhalf
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  refine ⟨hnpos, hsize, ?_, ?_⟩
  · calc
      _ ≤ (M : ℝ) * (A * (n : ℝ) ^ (-ρ) +
          M * (8 * (r + 1).factorial * (A * (n : ℝ) ^ (-ρ)))) := by
        gcongr
        norm_num
      _ ≤ _ := hsmall
  · have hMsize : M ≤ n := hM.trans
      ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
        ((boost_threshold_le_paper_threshold hqr).trans hn))
    apply absorber_greedy_failure_lt_one hqr hn hMsize
    exact (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hρhalf)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) hA)

end Arxiv2411_18291
