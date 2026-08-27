import Arxiv.Arxiv2411_18291.NibbleEdgeIncrements

/-! # Uniform control of the concrete edge-comparison remainders -/

namespace Arxiv2411_18291

theorem nibbleEdgeStepScale_nonneg (k : ℕ) {a g D p : ℝ} (hg : 0 ≤ g) (hD : 0 ≤ D) :
    0 ≤ nibbleEdgeStepScale k a g D p := by
  unfold nibbleEdgeStepScale
  positivity

theorem nibbleEdgeSlope_dominates_errors {k : ℕ} (hk : 3 ≤ k) {a g D p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 ≤ D) (hp : 0 < p) (hap : a ≤ p ^ k)
    (hsmall : (16 * (k : ℝ)) ^ 2 * a ≤ 1) :
    (1 + 32 * k) * nibbleEdgeStepScale k a g D p ≤ nibbleEdgeSlope k g D p := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hκ : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k - 1 by omega)
  have hc : 1 + 32 * (k : ℝ) ≤ (16 * (k : ℝ)) ^ 2 := by nlinarith only [hk']
  have hca : (1 + 32 * (k : ℝ)) * a ≤ ((k - 1 : ℕ) : ℝ) :=
    ((mul_le_mul_of_nonneg_right hc ha).trans hsmall).trans hκ
  have hnum : (1 + 32 * (k : ℝ)) * a ^ 2 ≤ ((k - 1 : ℕ) : ℝ) * p ^ k := by
    have h₁ := mul_le_mul_of_nonneg_right hca ha
    have h₂ := mul_le_mul_of_nonneg_left hap (Nat.cast_nonneg (k - 1))
    nlinarith only [h₁, h₂]
  have hexp : k - 2 + 2 = k := by omega
  have hpow : p ^ (k - 2) * p ^ 2 = p ^ k := by rw [← pow_add, hexp]
  calc
    _ = ((k : ℝ) * D / (p ^ 2 * g)) * ((1 + 32 * k) * a ^ 2) := by
      unfold nibbleEdgeStepScale
      ring
    _ ≤ ((k : ℝ) * D / (p ^ 2 * g)) * (((k - 1 : ℕ) : ℝ) * p ^ k) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by
      unfold nibbleEdgeSlope
      rw [← hpow]
      field_simp

theorem nibbleEdgeTaylor_le_scale {k : ℕ} (hk : 3 ≤ k) {a g D p : ℝ}
    (hg : 0 < g) (hD : 0 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1)
    (hlarge : (k : ℝ) ^ 3 ≤ a ^ 2 * g) :
    nibbleEdgeTaylor k g D p ≤ nibbleEdgeStepScale k a g D p := by
  have hκ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hκ₂ : ((k - 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 2
  have hc : ((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) * k ≤ (k : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul hκ hκ₂ (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg k)
    nlinarith only [h]
  have hnum : (((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) * k) * p ^ (k - 1) ≤ a ^ 2 * g := by
    have hpow : p ^ (k - 1) ≤ 1 := pow_le_one₀ hp.le hp1
    have h := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ ((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) * k by positivity)
    simp only [mul_one] at h
    exact h.trans (hc.trans hlarge)
  have hexp : k - 3 + 2 = k - 1 := by omega
  have hpow : p ^ (k - 3) * p ^ 2 = p ^ (k - 1) := by rw [← pow_add, hexp]
  calc
    _ = (D * k / (p ^ 2 * g ^ 2)) *
        ((((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) * k) * p ^ (k - 1)) := by
      unfold nibbleEdgeTaylor
      rw [← hpow]
      field_simp
    _ ≤ (D * k / (p ^ 2 * g ^ 2)) * (a ^ 2 * g) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by
      unfold nibbleEdgeStepScale
      field_simp

end Arxiv2411_18291
