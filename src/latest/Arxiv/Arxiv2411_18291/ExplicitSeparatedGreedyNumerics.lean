import Arxiv.Arxiv2411_18291.ExplicitAbsorberGreedyNumerics

/-! # Finite placement bounds with free-vertex separation -/

namespace Arxiv2411_18291

theorem absorber_separated_greedy_numerics {q r n w M d : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : w ≤ (4 * q) ^ (8 * q)) (hM : M ≤ (4 * q) ^ (8 * q))
    (hd : d ≤ (4 * q) ^ (8 * q)) {A : ℝ}
    (hA : 1 ≤ A) (hAb : 2 * A ≤ (4 * q : ℝ) ^ (8 * q)) :
    let θ := A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))
    0 < n ∧ 4 * w ^ 2 ≤ n ∧ 4 * w * (d * w) ≤ n ∧
      (M : ℝ) * (θ + M * (8 * (r + 1).factorial * θ)) ≤ 1 / 4 ∧
      (M : ℝ) * n.choose r * Real.exp (-(4 * (r + 1).factorial * θ * n / 3)) < 1 := by
  dsimp only
  obtain ⟨hnpos, hsize, hsmall, hfailure⟩ := absorber_greedy_numerics hqr hn hw hM
    (by linarith only [hA] : 1 ≤ 2 * A) hAb
  refine ⟨hnpos, hsize, ?_, ?_, ?_⟩
  · have hboost := (boost_threshold_le_paper_threshold hqr).trans hn
    calc
      _ ≤ (4 * q) ^ 1 * (4 * q) ^ (8 * q) *
          ((4 * q) ^ (8 * q) * (4 * q) ^ (8 * q)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by simp only [pow_one]; omega) hw)
          (Nat.mul_le_mul hd hw)
      _ = (4 * q) ^ (1 + 8 * q + (8 * q + 8 * q)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
      _ ≤ (4 * q) ^ (90 * q) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := hboost
  · have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
    have hnonneg : (0 : ℝ) ≤ M * (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) :=
      by positivity
    nlinarith only [hsmall, hnonneg]
  · convert hfailure using 1
    congr 2
    ring

end Arxiv2411_18291
