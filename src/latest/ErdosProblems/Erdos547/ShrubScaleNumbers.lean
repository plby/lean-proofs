import ErdosProblems.Erdos547.AllocationNumbers

/-!
# Smallness, rounding variance, and target slack at the shrub scale
-/

namespace Erdos547

theorem shrub_cluster_scale (ρ n B m ℓ : ℝ) (hρ : 0 ≤ ρ)
    (hn : n ≤ 8 * B * m) (hℓ : ℓ ≤ 2 * ρ * n) :
    ℓ ≤ 16 * ρ * B * m := by
  have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2 * ρ by positivity)
  nlinarith only [hh, hℓ]

theorem shrub_variance_margin (ρ n B m ℓ z err : ℝ)
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hm : 0 < m) (hℓ : 0 ≤ ℓ) (hz : 0 ≤ z)
    (hn : n ≤ 8 * B * m) (hℓbound : ℓ ≤ 16 * ρ * B * m)
    (hzbound : z ≤ 2 * n) (hsmall : 256 * ρ * B ^ 2 < err ^ 2) :
    ℓ * z < (err * m) ^ 2 := by
  have hzlarge : z ≤ 16 * B * m := by linarith only [hzbound, hn]
  have hproduct := mul_le_mul hℓbound hzlarge hz (by positivity)
  have hstrict := mul_lt_mul_of_pos_right hsmall (sq_pos_of_pos hm)
  nlinarith only [hproduct, hstrict]

theorem shrub_target_margin (s η θ ρ B m M t ℓ γ : ℝ)
    (hs : 0 < s) (hη : 0 ≤ η) (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ)
    (hB : 0 ≤ B) (hm : 0 ≤ m) (ht : 0 ≤ t) (htB : t ≤ B)
    (hM : m / 2 ≤ M) (hγ : η / 2 ≤ γ)
    (hℓ : ℓ ≤ 16 * ρ * B * m)
    (hsmall : 1024 * ρ * B ^ 2 ≤ s ^ 2 * η * θ) :
    (4 * ℓ / s) * t ≤ s / 4 * (γ * M * θ) := by
  have hprod := mul_le_mul hℓ htB ht (by positivity)
  have hsmallm := mul_le_mul_of_nonneg_right hsmall hm
  have hmain := mul_le_mul hM hγ (div_nonneg hη (by norm_num))
    (show 0 ≤ M by linarith only [hM, hm])
  have hmainScaled := mul_le_mul_of_nonneg_right hmain
    (mul_nonneg (sq_nonneg s) hθ)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hs).mpr
  nlinarith only [hprod, hsmallm, hmainScaled]

end Erdos547

#print axioms Erdos547.shrub_variance_margin
#print axioms Erdos547.shrub_target_margin
