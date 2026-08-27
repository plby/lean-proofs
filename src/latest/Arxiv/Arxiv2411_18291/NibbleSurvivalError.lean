import Arxiv.Arxiv2411_18291.NibbleEdgeRemainders

/-! # A uniform bound for the frozen comparison's survival correction -/

namespace Arxiv2411_18291

theorem nibbleEdgeSlope_nonneg (k : ℕ) {g D p : ℝ}
    (hg : 0 ≤ g) (hD : 0 ≤ D) (hp : 0 ≤ p) : 0 ≤ nibbleEdgeSlope k g D p := by
  unfold nibbleEdgeSlope
  positivity

theorem nibbleEdgeSurvival_le_scale {k : ℕ} (hk : 3 ≤ k) {a g D p : ℝ}
    (hg : 0 < g) (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    (hlarge : 16 * (k : ℝ) ^ 3 ≤ a ^ 2 * g) :
    4 * nibbleDegreeMain k D p * (2 * nibbleEdgeSlope k g D p) /
        nibbleCliqueMain k g D p ≤ nibbleEdgeStepScale k a g D p := by
  have hk0 : 0 < k := by omega
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hκ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hc : 8 * ((k - 1 : ℕ) : ℝ) * k ≤ 16 * (k : ℝ) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right hκ (show 0 ≤ 8 * (k : ℝ) by positivity)
    have hk2 := mul_nonneg (by nlinarith only [hk'] : 0 ≤ 2 * (k : ℝ) - 1)
      (sq_nonneg (k : ℝ))
    nlinarith only [hmul, hk2]
  have hnum : (8 * ((k - 1 : ℕ) : ℝ) * k) * p ^ (k - 1) ≤ a ^ 2 * g := by
    have h := mul_le_mul_of_nonneg_left (pow_le_one₀ hp.le hp1 : p ^ (k - 1) ≤ 1)
      (show 0 ≤ 8 * ((k - 1 : ℕ) : ℝ) * k by positivity)
    simp only [mul_one] at h
    exact h.trans (hc.trans hlarge)
  have hexp : k - 2 + 1 = k - 1 := by omega
  have hpow : p ^ (k - 2) * p = p ^ (k - 1) := by rw [← pow_succ, hexp]
  calc
    _ = 8 * nibbleEdgeSlope k g D p *
        (nibbleDegreeMain k D p / nibbleCliqueMain k g D p) := by ring
    _ = 8 * nibbleEdgeSlope k g D p * ((k : ℝ) / (p * g)) := by
      rw [nibbleDegreeMain_clique_ratio hk0 hg.ne' hD.ne' hp.ne']
    _ = ((k : ℝ) * D / (p ^ 2 * g ^ 2)) *
        ((8 * ((k - 1 : ℕ) : ℝ) * k) * p ^ (k - 1)) := by
      unfold nibbleEdgeSlope
      rw [← hpow]
      field_simp
    _ ≤ ((k : ℝ) * D / (p ^ 2 * g ^ 2)) * (a ^ 2 * g) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by
      unfold nibbleEdgeStepScale
      field_simp

end Arxiv2411_18291
