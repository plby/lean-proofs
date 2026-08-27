import Arxiv.Arxiv2411_18291.AsymptoticNibbleEndConditions
import Arxiv.Arxiv2411_18291.AsymptoticNibbleExponents

/-! # Scalar nibble estimates for graph-size exponent at least one -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_dense_nibble_scalar_conditions (k d : ℕ) (hk : 3 ≤ k)
    {ε γ δ ℓ cg cD : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hγ : 1 ≤ γ) (hδ : ℓ + 2 / 3 ≤ δ) (hcg : 0 < cg) (hcD : 0 < cD) :
    ∀ᶠ n : ℕ in atTop, ∀ g D : ℝ,
      cg * (n : ℝ) ^ γ ≤ g → cD * (n : ℝ) ^ δ ≤ D →
      let a := (n : ℝ) ^ (-(ε / 3))
      let p₀ := (n : ℝ) ^ (-(ε / (3 * k)))
      let L := (n : ℝ) ^ ℓ
      NibbleComparisonParameters k a g D p₀ L ∧
        NibbleCountConditions k a g D p₀ L ∧
        NibbleEndConditions k a g n p₀ d ∧
        NibbleExponentConditions k d a g D n L ((n : ℝ) ^ (1 / 2 - ε)) cg := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith only [hkR]
  have hβ : 0 < ε / (3 * k) := div_pos hε (by positivity)
  have hkβ : (k : ℝ) * (ε / (3 * k)) = ε / 3 := by field_simp
  have hαβ : 2 * (ε / (3 * k)) < ε / 3 := by
    have h := mul_lt_mul_of_pos_right (show (2 : ℝ) < k by linarith only [hkR]) hβ
    rwa [hkβ] at h
  have hP := eventually_nibble_comparison_parameters k hk
    (α := ε / 3) (β := ε / (3 * k)) (γ := γ) (δ := δ) (ℓ := ℓ)
    (cg := cg) (cD := cD) hβ hαβ hkβ.le
    (by linarith only [hεhalf, hγ]) (by linarith only [hεhalf, hδ]) hcg hcD
  have hQ := eventually_nibble_count_conditions k hk
    (α := ε / 3) (β := ε / (3 * k)) (γ := γ) (δ := δ) (ℓ := ℓ)
    (cg := cg) (cD := cD) hβ hkβ.le
    (by linarith only [hεhalf, hγ]) (by linarith only [hεhalf, hδ]) hcg hcD
  have hR := eventually_nibble_end_conditions k d
    (α := ε / 3) (β := ε / (3 * k)) (γ := γ) (cg := cg)
    (by linarith only [hεhalf]) (by linarith only [hαβ, hβ])
    (by linarith only [hεhalf, hγ]) hcg
  have hS := eventually_nibble_exponent_conditions k d
    (α := ε / 3) (η := 1 / 2 - ε) (γ := γ) (δ := δ) (ℓ := ℓ)
    (cg := cg) (cD := cD) hγ
    (by linarith only [hεhalf, hγ]) (by linarith only [hεhalf, hδ])
    (by linarith only [hεhalf, hγ]) (by linarith only [hε]) hcg hcD
  filter_upwards [hP, hQ, hR, hS] with n hP hQ hR hS
  intro g D hg hD
  exact ⟨hP g D hg hD, hQ g D hg hD, hR g hg, hS g D hg hD⟩

end Arxiv2411_18291
