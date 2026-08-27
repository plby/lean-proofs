import Arxiv.Arxiv2411_18291.NibbleCliqueIncrements

/-! # Uniform remainder and step-size bounds for the clique-count comparisons -/

namespace Arxiv2411_18291

theorem nibbleCliqueStepScale_nonneg (k : ℕ) {a D p : ℝ}
    (ha : 0 ≤ a) (hD : 0 ≤ D) (hp : 0 ≤ p) : 0 ≤ nibbleCliqueStepScale k a D p := by
  unfold nibbleCliqueStepScale
  positivity

theorem nibbleCliqueStepScale_le (k : ℕ) {a D p : ℝ} (ha : 0 ≤ a) (hap : a ≤ p)
    (hD : 0 ≤ D) (hp : 0 < p) : nibbleCliqueStepScale k a D p ≤ (k : ℝ) ^ 3 * D := by
  unfold nibbleCliqueStepScale
  apply (div_le_iff₀ (pow_pos hp 3)).mpr
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hap 3)
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg k) 3) hD)
  nlinarith only [h]

theorem nibbleCliqueSlope_nonneg (k : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ nibbleCliqueSlope k D p := by
  unfold nibbleCliqueSlope
  positivity

theorem nibbleCliqueSlope_le (k : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    nibbleCliqueSlope k D p ≤ (k : ℝ) * D := by
  unfold nibbleCliqueSlope
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ hp hp1 : p ^ (k - 1) ≤ 1) (mul_nonneg (Nat.cast_nonneg _) hD)

theorem nibbleCliqueTaylor_le_scale {k : ℕ} (hk : 2 ≤ k) {a g D p : ℝ}
    (hg : 0 < g) (hD : 0 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1) (hsteps : 1 ≤ a ^ 3 * g) :
    nibbleCliqueTaylor k g D p ≤ nibbleCliqueStepScale k a D p := by
  have hκ : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hnum : ((k - 1 : ℕ) : ℝ) * p ^ (k + 1) ≤ (k : ℝ) * (a ^ 3 * g) := by
    calc
      _ ≤ ((k - 1 : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hp.le hp1) (Nat.cast_nonneg _)
      _ ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_right hκ zero_le_one
      _ ≤ _ := mul_le_mul_of_nonneg_left hsteps (Nat.cast_nonneg _)
  have hexp : k - 2 + 3 = k + 1 := by omega
  have hpow : p ^ (k + 1) = p ^ (k - 2) * p ^ 3 := by rw [← pow_add, hexp]
  calc
    _ = (D * (k : ℝ) ^ 2 / (p ^ 3 * g)) * (((k - 1 : ℕ) : ℝ) * p ^ (k + 1)) := by
      unfold nibbleCliqueTaylor
      rw [hpow]
      field_simp
    _ ≤ (D * (k : ℝ) ^ 2 / (p ^ 3 * g)) * ((k : ℝ) * (a ^ 3 * g)) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by
      unfold nibbleCliqueStepScale
      field_simp

end Arxiv2411_18291
