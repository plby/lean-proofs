import Arxiv.Arxiv2411_18291.AsymptoticNibbleCountConditions
import Arxiv.Arxiv2411_18291.NibblePaperComparisonParameters

/-! # Eventual clique-count conditions at the paper's density scales -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_nibble_count_parameters_from_densities (q r : ℕ) (hr : 2 ≤ r)
    (hqr : r < q) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2 / 3) :
    ∀ᶠ n : ℕ in atTop, ∀ φ τ : ℝ,
      (n : ℝ) ^ (-(r : ℝ) / 3) ≤ φ → (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      let k := q.choose r
      let a := (n : ℝ) ^ (-(ε / 3))
      let g := φ * (n.choose r : ℝ)
      let D := τ * (n.choose (q - r) : ℝ)
      let p₀ := (n : ℝ) ^ (-(ε / (3 * k)))
      let L := (n : ℝ) ^ (q - r - 1)
      NibbleComparisonParameters k a g D p₀ L ∧ NibbleCountConditions k a g D p₀ L := by
  let k := q.choose r
  have hk : 3 ≤ k := three_le_clique_size hr hqr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hβ : 0 < ε / (3 * k) := div_pos hε (by positivity)
  have hkβ : (k : ℝ) * (ε / (3 * k)) ≤ ε / 3 := by
    apply le_of_eq
    field_simp
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hγ : 3 * (ε / 3) < (r : ℝ) - r / 3 := by linarith only [hε2, hrR]
  have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
  have hδ : ((q - r - 1 : ℕ) : ℝ) + 3 * (ε / 3) < ((q - r : ℕ) : ℝ) - 1 / 3 := by
    rw [hsub]
    linarith only [hε2]
  have hQ := eventually_nibble_count_conditions k hk
    (α := ε / 3) (β := ε / (3 * k)) (γ := (r : ℝ) - r / 3)
    (δ := ((q - r : ℕ) : ℝ) - 1 / 3) (ℓ := ((q - r - 1 : ℕ) : ℝ))
    (cg := 1 / (2 * (r.factorial : ℝ))) (cD := 1 / (2 * ((q - r).factorial : ℝ)))
    hβ hkβ hγ hδ (by positivity) (by positivity)
  filter_upwards [hQ,
    eventually_nibble_parameters_from_densities q r hr hqr hε
      (hε2.trans (by norm_num : (2 / 3 : ℝ) < 1)),
    eventually_binomial_density_lower r ((r : ℝ) / 3),
    eventually_binomial_density_lower (q - r) (1 / 3)] with n hcount hbase hgraph hdegree
  intro φ τ hφ hτ
  dsimp only
  have hg : (1 / (2 * (r.factorial : ℝ))) * (n : ℝ) ^ ((r : ℝ) - r / 3) ≤
      φ * (n.choose r : ℝ) := by
    apply hgraph φ
    simpa only [neg_div] using hφ
  have h := hcount (φ * (n.choose r : ℝ)) (τ * (n.choose (q - r) : ℝ)) hg (hdegree τ hτ)
  refine ⟨hbase φ τ hφ hτ, ?_⟩
  simpa only [k, Real.rpow_natCast] using h

end Arxiv2411_18291
