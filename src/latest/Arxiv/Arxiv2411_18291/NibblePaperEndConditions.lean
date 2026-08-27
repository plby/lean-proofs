import Arxiv.Arxiv2411_18291.AsymptoticNibbleEndConditions
import Arxiv.Arxiv2411_18291.NibblePaperCountConditions

/-! # All scalar comparison and end conditions at the paper's density scales -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_nibble_all_parameters_from_densities (q r : ℕ) (hr : 2 ≤ r)
    (hqr : r < q) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2 / 3) :
    ∀ᶠ n : ℕ in atTop, ∀ φ τ : ℝ,
      (n : ℝ) ^ (-(r : ℝ) / 3) ≤ φ → (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      let k := q.choose r
      let a := (n : ℝ) ^ (-(ε / 3))
      let g := φ * (n.choose r : ℝ)
      let D := τ * (n.choose (q - r) : ℝ)
      let p₀ := (n : ℝ) ^ (-(ε / (3 * k)))
      let L := (n : ℝ) ^ (q - r - 1)
      NibbleComparisonParameters k a g D p₀ L ∧ NibbleCountConditions k a g D p₀ L ∧
        NibbleEndConditions k a g n p₀ (q - r + 1) := by
  let k := q.choose r
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast three_le_clique_size hr hqr
  have hk0 : (0 : ℝ) < k := by linarith only [hk]
  have hβ : 0 < ε / (3 * k) := div_pos hε (by positivity)
  have hkβ : (k : ℝ) * (ε / (3 * k)) = ε / 3 := by field_simp
  have hβα : ε / (3 * k) < ε / 3 := by
    have h := mul_lt_mul_of_pos_right (by linarith only [hk] : (1 : ℝ) < k) hβ
    simpa only [one_mul, hkβ] using h
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hγ : 3 * (ε / 3) < (r : ℝ) - r / 3 := by linarith only [hε2, hrR]
  have hend := eventually_nibble_end_conditions k (q - r + 1)
    (α := ε / 3) (β := ε / (3 * k)) (γ := (r : ℝ) - r / 3)
    (cg := 1 / (2 * (r.factorial : ℝ)))
    (by linarith only [hε2]) hβα hγ (by positivity)
  filter_upwards [eventually_nibble_count_parameters_from_densities q r hr hqr hε hε2,
    hend, eventually_binomial_density_lower r ((r : ℝ) / 3)] with n hbase he hgraph
  intro φ τ hφ hτ
  dsimp only
  obtain ⟨hP, hQ⟩ := hbase φ τ hφ hτ
  refine ⟨hP, hQ, he (φ * (n.choose r : ℝ)) ?_⟩
  apply hgraph φ
  simpa only [neg_div] using hφ

end Arxiv2411_18291
