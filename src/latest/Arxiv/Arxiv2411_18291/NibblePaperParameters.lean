import Arxiv.Arxiv2411_18291.AsymptoticNibble
import Arxiv.Arxiv2411_18291.DenseNibble
import Arxiv.Arxiv2411_18291.RankOnePairNibble
import Arxiv.Arxiv2411_18291.ExplicitAllRanksNibble

/-! # The paper's nibble lemma at the reserve exponent -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem paper_nibble_exponent_gap {k : ℕ} (hk : 0 < k) :
    -((1 / 3 : ℝ) / (3 * k)) < -(3 * (k : ℝ) * (1 / (6 * k : ℝ) ^ 2)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h₁ : (1 / 3 : ℝ) / (3 * k) = 1 / (9 * k : ℝ) := by field_simp; norm_num
  have h₂ : 3 * (k : ℝ) * (1 / (6 * k : ℝ) ^ 2) = 1 / (12 * k : ℝ) := by
    field_simp
    norm_num
  rw [h₁, h₂]
  apply neg_lt_neg
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hk']

theorem eventually_exists_nibble_paper_parameters_of_three_le (q r : ℕ)
    (hqr : r + 1 < q) (hk3 : 3 ≤ q.choose (r + 1)) :
    let k := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * k : ℝ) ^ 2
    ∀ᶠ n : ℕ in atTop, ∀ (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q)),
      (1 / 2 : ℝ) * (n.choose (r + 1) : ℝ) < G.card →
      (∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) →
      (∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
          (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2)) →
      ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
        IsDecomposition (cliqueSupport (r + 1) C) C ∧
          IsGraphBounded (G \ cliqueSupport (r + 1) C) ((n : ℝ) ^ (-(3 * k * ρ))) := by
  dsimp only
  filter_upwards [eventually_ge_atTop (paperSizeThreshold q (r + 1))] with n hn
  intro G H hG hHG hd
  exact exists_nibble_paper_threshold_of_three_le q r n hqr hk3 hn G H hG hHG hd

theorem eventually_exists_nibble_paper_parameters (q r : ℕ) (hr : 1 ≤ r) (hqr : r + 1 < q) :
    let k := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * k : ℝ) ^ 2
    ∀ᶠ n : ℕ in atTop, ∀ (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q)),
      (1 / 2 : ℝ) * (n.choose (r + 1) : ℝ) < G.card →
      (∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) →
      (∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
          (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2)) →
      ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
        IsDecomposition (cliqueSupport (r + 1) C) C ∧
          IsGraphBounded (G \ cliqueSupport (r + 1) C) ((n : ℝ) ^ (-(3 * k * ρ))) :=
  eventually_exists_nibble_paper_parameters_of_three_le q r hqr
    (three_le_clique_size (by omega) hqr)

/-- The eventual interface to the finite Nibble lemma in every stated rank,
including rank one and the pair case. -/
theorem eventually_exists_nibble_paper_parameters_all_ranks (q r : ℕ) (hqr : r + 1 < q) :
    let k := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * k : ℝ) ^ 2
    ∀ᶠ n : ℕ in atTop, ∀ (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q)),
      (1 / 2 : ℝ) * (n.choose (r + 1) : ℝ) < G.card →
      (∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) →
      (∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
          (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2)) →
      ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
        IsDecomposition (cliqueSupport (r + 1) C) C ∧
          IsGraphBounded (G \ cliqueSupport (r + 1) C) ((n : ℝ) ^ (-(3 * k * ρ))) := by
  dsimp only
  filter_upwards [eventually_ge_atTop (paperSizeThreshold q (r + 1))] with n hn
  intro G H hG hHG hd
  exact exists_nibble_paper_threshold q r n hqr hn G H hG hHG hd

end Arxiv2411_18291
