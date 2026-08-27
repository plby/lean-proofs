import Arxiv.Arxiv2411_18291.AsymptoticNibbleExponents
import Arxiv.Arxiv2411_18291.NibbleBinomialScales

/-! # A common positive-power exponent at the paper's density scales -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_nibble_exponent_conditions_from_densities (q r : ℕ) (hr : 2 ≤ r)
    (hqr : r < q) {ε : ℝ} (hε : ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ φ τ : ℝ,
      (n : ℝ) ^ (-(r : ℝ) / 3) ≤ φ → (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      NibbleExponentConditions (q.choose r) (q - r + 1) ((n : ℝ) ^ (-(ε / 3)))
        (φ * (n.choose r : ℝ)) (τ * (n.choose (q - r) : ℝ)) n
        ((n : ℝ) ^ (q - r - 1)) ((n : ℝ) ^ (1 / 3 - 2 * ε / 3))
        (1 / (2 * (r.factorial : ℝ))) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hγ1 : (1 : ℝ) ≤ (r : ℝ) - r / 3 := by linarith only [hrR]
  have hcount : (1 / 3 - 2 * ε / 3) + 6 * (ε / 3) < (r : ℝ) - r / 3 := by
    linarith only [hε, hrR]
  have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
  have hcode : (1 / 3 - 2 * ε / 3) + ((q - r - 1 : ℕ) : ℝ) + 4 * (ε / 3) <
      ((q - r : ℕ) : ℝ) - 1 / 3 := by
    rw [hsub]
    linarith only [hε]
  have hgraph : (1 / 3 - 2 * ε / 3) + 4 * (ε / 3) < (r : ℝ) - r / 3 := by
    linarith only [hε, hrR]
  have hface : (1 / 3 - 2 * ε / 3) + 2 * (ε / 3) < 1 := by ring_nf; norm_num
  have hS := eventually_nibble_exponent_conditions (q.choose r) (q - r + 1)
    (α := ε / 3) (η := 1 / 3 - 2 * ε / 3) (γ := (r : ℝ) - r / 3)
    (δ := ((q - r : ℕ) : ℝ) - 1 / 3) (ℓ := ((q - r - 1 : ℕ) : ℝ))
    (cg := 1 / (2 * (r.factorial : ℝ))) (cD := 1 / (2 * ((q - r).factorial : ℝ)))
    hγ1 hcount hcode hgraph hface (by positivity) (by positivity)
  filter_upwards [hS, eventually_binomial_density_lower r ((r : ℝ) / 3),
    eventually_binomial_density_lower (q - r) (1 / 3)] with n hS' hgraph' hdegree
  intro φ τ hφ hτ
  have hg : (1 / (2 * (r.factorial : ℝ))) * (n : ℝ) ^ ((r : ℝ) - r / 3) ≤
      φ * (n.choose r : ℝ) := by
    apply hgraph' φ
    simpa only [neg_div] using hφ
  simpa only [Real.rpow_natCast] using
    hS' (φ * (n.choose r : ℝ)) (τ * (n.choose (q - r) : ℝ)) hg (hdegree τ hτ)

end Arxiv2411_18291
