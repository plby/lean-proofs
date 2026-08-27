import Arxiv.Arxiv2411_18291.ScaledNibbleInitialMargins
import Arxiv.Arxiv2411_18291.ExplicitNibbleGrowth

/-! # Expressing the smaller comparison error as a power at n0 -/

noncomputable section

namespace Arxiv2411_18291

def scaledNibbleExponent (n k : ℕ) (ε : ℝ) : ℝ :=
  ε + 3 * Real.log (5 * (k : ℝ) / 2) / Real.log n

theorem scaled_nibble_exponent_bounds {n k : ℕ} {ε : ℝ}
    (hn : (1 : ℝ) < n) (hk : 1 ≤ k) (hε : ε ≤ 1 / 4)
    (hscale : 5 * (k : ℝ) / 2 ≤ (n : ℝ) ^ (1 / 20 : ℝ)) :
    ε ≤ scaledNibbleExponent n k ε ∧ scaledNibbleExponent n k ε ≤ 2 / 5 ∧
      (n : ℝ) ^ (-(scaledNibbleExponent n k ε / 3)) =
        (2 / (5 * (k : ℝ))) * (n : ℝ) ^ (-(ε / 3)) := by
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : (0 : ℝ) < 5 * (k : ℝ) / 2 := by positivity
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn
  have hlogc : 0 ≤ Real.log (5 * (k : ℝ) / 2) := Real.log_nonneg (by linarith only [hK])
  have hlogs : Real.log (5 * (k : ℝ) / 2) ≤ (1 / 20 : ℝ) * Real.log n := by
    have hh := Real.log_le_log hc hscale
    rwa [Real.log_rpow hn0] at hh
  have hquot : 3 * Real.log (5 * (k : ℝ) / 2) / Real.log n ≤ 3 / 20 := by
    apply (div_le_iff₀ hlogn).mpr
    linarith only [hlogs]
  have hquot0 : 0 ≤ 3 * Real.log (5 * (k : ℝ) / 2) / Real.log n := by positivity
  refine ⟨by dsimp only [scaledNibbleExponent]; linarith only [hquot0],
    by dsimp only [scaledNibbleExponent]; linarith only [hquot, hε], ?_⟩
  have heq : Real.log (n : ℝ) * (-(scaledNibbleExponent n k ε / 3)) =
      -(Real.log (5 * (k : ℝ) / 2)) + Real.log n * (-(ε / 3)) := by
    unfold scaledNibbleExponent
    field_simp
    ring
  rw [Real.rpow_def_of_pos hn0, heq, Real.exp_add, Real.exp_neg, Real.exp_log hc,
    ← Real.rpow_def_of_pos hn0]
  congr 1
  field_simp

theorem nibble_error_scale_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) :
    5 * (q.choose r : ℝ) / 2 ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hh := paper_threshold_nibble_monomial (C := 5) (i := 0) (j := 1) (d := 0)
    hr hqr hn (by norm_num) (by norm_num) (by norm_num) (by omega)
  simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat, mul_one] at hh
  have hρ := paperRho_le_one_div_36 hqr
  calc
    _ ≤ 5 * (q.choose r : ℝ) := by
      have hk : (0 : ℝ) ≤ q.choose r := Nat.cast_nonneg _
      linarith only [hk]
    _ ≤ (n : ℝ) ^ paperRho q r := hh
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hρ])

theorem scaled_nibble_exponent_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) {ε : ℝ} (hε : ε ≤ 1 / 4) :
    ε ≤ scaledNibbleExponent n (q.choose r) ε ∧
      scaledNibbleExponent n (q.choose r) ε ≤ 2 / 5 ∧
      (n : ℝ) ^ (-(scaledNibbleExponent n (q.choose r) ε / 3)) =
        (2 / (5 * (q.choose r : ℝ))) * (n : ℝ) ^ (-(ε / 3)) :=
  scaled_nibble_exponent_bounds
    (by exact_mod_cast (paperSizeThreshold_one_lt hqr).trans_le hn)
    (Nat.choose_pos hqr.le) hε (nibble_error_scale_paper_threshold hr hqr hn)

end Arxiv2411_18291
