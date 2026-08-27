import Arxiv.Arxiv2411_18291.DenseNibbleScalars
import Arxiv.Arxiv2411_18291.NibbleBinomialScales

/-! # Nibble parameters at constant graph density, including rank one -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_dense_nibble_parameters (q r : ℕ) (hqr : r + 1 < q)
    (hk : 3 ≤ q.choose (r + 1)) {ε θ : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, ∀ g τ : ℝ,
      θ * (n.choose (r + 1) : ℝ) ≤ g → (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      let k := q.choose (r + 1)
      let a := (n : ℝ) ^ (-(ε / 3))
      let D := τ * (n.choose (q - (r + 1)) : ℝ)
      let p₀ := (n : ℝ) ^ (-(ε / (3 * k)))
      let L := (n : ℝ) ^ (q - (r + 1) - 1)
      NibbleComparisonParameters k a g D p₀ L ∧
        NibbleCountConditions k a g D p₀ L ∧
        NibbleEndConditions k a g n p₀ (q - r) ∧
        NibbleExponentConditions k (q - r) a g D n L ((n : ℝ) ^ (1 / 2 - ε))
          (θ / (2 * ((r + 1).factorial : ℝ))) := by
  have hsub : ((q - (r + 1) - 1 : ℕ) : ℝ) = ((q - (r + 1) : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ q - (r + 1) by omega), Nat.cast_one]
  have hδ : ((q - (r + 1) - 1 : ℕ) : ℝ) + 2 / 3 ≤
      ((q - (r + 1) : ℕ) : ℝ) - 1 / 3 := by rw [hsub]; linarith
  have hparams := eventually_dense_nibble_scalar_conditions (q.choose (r + 1)) (q - r) hk
    (γ := ((r + 1 : ℕ) : ℝ)) (δ := ((q - (r + 1) : ℕ) : ℝ) - 1 / 3)
    (ℓ := ((q - (r + 1) - 1 : ℕ) : ℝ))
    (cg := θ / (2 * ((r + 1).factorial : ℝ)))
    (cD := 1 / (2 * ((q - (r + 1)).factorial : ℝ)))
    hε hεhalf (by exact_mod_cast (show 1 ≤ r + 1 by omega)) hδ (by positivity) (by positivity)
  filter_upwards [hparams, eventually_choose_ge_half_power (r + 1),
    eventually_binomial_density_lower (q - (r + 1)) (1 / 3)] with n hparams hchoose hdegree
  intro g τ hg hτ
  have hglower : (θ / (2 * ((r + 1).factorial : ℝ))) *
      (n : ℝ) ^ ((r + 1 : ℕ) : ℝ) ≤ g := by
    rw [Real.rpow_natCast]
    calc
      _ = θ * ((n : ℝ) ^ (r + 1) / (2 * (r + 1).factorial)) := by ring
      _ ≤ θ * (n.choose (r + 1) : ℝ) := mul_le_mul_of_nonneg_left hchoose hθ.le
      _ ≤ g := hg
  simpa only [Real.rpow_natCast] using
    hparams g (τ * (n.choose (q - (r + 1)) : ℝ)) hglower (hdegree τ hτ)

end Arxiv2411_18291
