import ErdosProblems.Erdos547.EmbeddingScaleConstants

/-!
# Scalar allocation margins for the four coated parts
-/

namespace Erdos547

theorem coated_part_ratio_lower (η n x y : ℝ) (hη : 0 ≤ η) (hx : 0 < x)
    (hxupper : x ≤ 2 * n) (hylower : η * n ≤ y) : η / 2 ≤ y / x := by
  apply (le_div_iff₀ hx).mpr
  have hh := mul_le_mul_of_nonneg_left hxupper hη
  nlinarith only [hh, hylower]

theorem allowed_head_mass_margin (s η θ δ n m t x : ℝ)
    (hs : 0 ≤ s) (hη : 0 ≤ η) (hm : 0 < m) (ht : 0 ≤ t) (hx : 0 ≤ x)
    (hvolume : m * t ≤ 2 * n) (hpart : η * n ≤ x)
    (hexception : θ + 4 * δ ≤ s * η / 4) (hclusters : 8 ≤ s * η * t) :
    (1 - s) * ((1 + 10 * s) / m) * x ≤
      ((1 + 10 * s) / m) * x - θ * t - 2 - 4 * (δ * t) := by
  have hηvolume := mul_le_mul_of_nonneg_left hvolume hη
  have hbase : η * t / 2 ≤ ((1 + 10 * s) / m) * x := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hm).mpr
    have hsx := mul_nonneg hs hx
    nlinarith only [hηvolume, hpart, hsx]
  have hsbase := mul_le_mul_of_nonneg_left hbase hs
  have he := mul_le_mul_of_nonneg_right hexception ht
  nlinarith only [hsbase, he, hclusters]

theorem relative_far_mean_of_near (s M x y A : ℝ) (hx : 0 < x) (hy : 0 ≤ y)
    (hA : 0 < A) (hmean : x / A + s * M ≤ (1 - s) * M) :
    y / A + s * M * (y / x) ≤ (1 - s) * M * (y / x) := by
  have hprod := mul_le_mul_of_nonneg_right hmean (div_nonneg hy hx.le)
  have he : x / A * (y / x) = y / A := by field_simp
  nlinarith only [hprod, he]

namespace EmbeddingConstants

variable {a : ℝ} (k : EmbeddingConstants a)

theorem rounding_error_near (m M : ℝ) (hm : 0 ≤ m) (hM : m / 2 ≤ M) :
    k.errorFraction * m ≤ k.theta * (k.slack * M) := by
  have hη : k.treeEta ≤ 1 := by linarith only [k.treeEta_le]
  have hηm := mul_le_mul_of_nonneg_right hη hm
  have hbase : k.treeEta * m / 100 ≤ M := by linarith only [hηm, hM, hm]
  have hh := mul_le_mul_of_nonneg_left hbase (mul_nonneg k.slack_pos.le k.theta_pos.le)
  unfold errorFraction
  nlinarith only [hh]

theorem rounding_error_far (m M γ : ℝ) (hm : 0 ≤ m) (hM : m / 2 ≤ M)
    (hγ : k.treeEta / 2 ≤ γ) :
    k.errorFraction * m ≤ k.theta * (k.slack * M * γ) := by
  have hγ0 : 0 ≤ γ := by linarith only [hγ, k.treeEta_pos]
  have hh := mul_le_mul hM hγ (div_nonneg k.treeEta_pos.le (by norm_num))
    (by linarith only [hM, hm])
  have hηm := mul_nonneg k.treeEta_pos.le hm
  have hbase : k.treeEta * m / 100 ≤ M * γ := by nlinarith only [hh, hηm]
  have hs := mul_le_mul_of_nonneg_left hbase (mul_nonneg k.slack_pos.le k.theta_pos.le)
  unfold errorFraction
  nlinarith only [hs]

end EmbeddingConstants

end Erdos547

#print axioms Erdos547.allowed_head_mass_margin
#print axioms Erdos547.EmbeddingConstants.rounding_error_far
