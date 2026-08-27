import Arxiv.Arxiv2411_18291.AsymptoticNibbleParameters
import Arxiv.Arxiv2411_18291.NibbleBinomialScales

/-!
# Comparison parameters at the paper's density and clique-degree scales

The scalar comparison conditions hold eventually at the stated stopping
density. This does not yet establish simultaneous control of the processes
or the nibble's bounded-leave conclusion.
-/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_nibble_parameters_from_densities (q r : ℕ) (hr : 2 ≤ r) (hqr : r < q)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ φ τ : ℝ,
      (n : ℝ) ^ (-(r : ℝ) / 3) ≤ φ → (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      NibbleComparisonParameters (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
        (φ * (n.choose r : ℝ)) (τ * (n.choose (q - r) : ℝ))
        ((n : ℝ) ^ (-(ε / (3 * q.choose r)))) ((n : ℝ) ^ (q - r - 1)) := by
  let k := q.choose r
  have hk : 3 ≤ k := three_le_clique_size hr hqr
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith only [hkR]
  have hβ : 0 < ε / (3 * k) := div_pos hε (by positivity)
  have hαβ : 2 * (ε / (3 * k)) < ε / 3 := by
    rw [show 2 * (ε / (3 * k)) = (2 * ε) / (3 * k) by ring]
    apply (div_lt_iff₀ (show (0 : ℝ) < 3 * k by positivity)).mpr
    have hmul := mul_pos hε (show (0 : ℝ) < k - 2 by linarith only [hkR])
    nlinarith only [hmul]
  have hkβ : (k : ℝ) * (ε / (3 * k)) ≤ ε / 3 := by
    apply le_of_eq
    field_simp
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hγ : 2 * (ε / 3) < (r : ℝ) - r / 3 := by linarith only [hε1, hrR]
  have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
  have hδ : ((q - r - 1 : ℕ) : ℝ) + 2 * (ε / 3) < ((q - r : ℕ) : ℝ) - 1 / 3 := by
    rw [hsub]
    linarith only [hε1]
  have hp := eventually_nibble_comparison_parameters k hk
    (α := ε / 3) (β := ε / (3 * k)) (γ := (r : ℝ) - r / 3)
    (δ := ((q - r : ℕ) : ℝ) - 1 / 3) (ℓ := ((q - r - 1 : ℕ) : ℝ))
    (cg := 1 / (2 * (r.factorial : ℝ))) (cD := 1 / (2 * ((q - r).factorial : ℝ)))
    hβ hαβ hkβ hγ hδ (by positivity) (by positivity)
  filter_upwards [hp, eventually_binomial_density_lower r ((r : ℝ) / 3),
    eventually_binomial_density_lower (q - r) (1 / 3)] with n hparams hgraph hdegree
  intro φ τ hφ hτ
  have hg : (1 / (2 * (r.factorial : ℝ))) * (n : ℝ) ^ ((r : ℝ) - r / 3) ≤
      φ * (n.choose r : ℝ) := by
    apply hgraph φ
    simpa only [neg_div] using hφ
  have h := hparams (φ * (n.choose r : ℝ)) (τ * (n.choose (q - r) : ℝ)) hg (hdegree τ hτ)
  simpa only [k, Real.rpow_natCast] using h

end Arxiv2411_18291
