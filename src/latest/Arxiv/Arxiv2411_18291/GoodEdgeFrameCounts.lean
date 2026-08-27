import Arxiv.Arxiv2411_18291.AsymptoticCliqueCount
import Arxiv.Arxiv2411_18291.CliqueFamilyRelabeling

/-!
# Rooted clique choices supplied by good edges

The good-edge relative count gives a polynomial lower bound for the choices
in each near-frame piece. Vertex permutations preserve this bound exactly,
so it applies to every edge carrying the prescribed good-subgraph colour.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem edgeMainTerm_polynomial_lower {n b α d : ℝ} (hn : 0 < n) (hb : 0 < b)
    (hd : b * n ^ (-α) ≤ d) (q r : ℕ) :
    (b ^ (q.choose r - 1) / (q - r).factorial) * n ^ (-(α * ((q.choose r - 1 : ℕ) : ℝ))) *
      n ^ (q - r) ≤ cliqueMainTerm n d q r r := by
  have hbase : 0 ≤ b * n ^ (-α) := mul_nonneg hb.le (Real.rpow_nonneg hn.le _)
  calc
    _ = n ^ (q - r) * (b * n ^ (-α)) ^ (q.choose r - 1) / (q - r).factorial := by
      rw [mul_pow, ← Real.rpow_mul_natCast hn.le, neg_mul]
      ring
    _ ≤ _ := by
      simp only [cliqueMainTerm, Nat.choose_self]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hd _) (pow_nonneg hn.le _))
          (Nat.cast_nonneg _)

theorem relative_count_half_lower {x μ ε : ℝ} (hμ : 0 ≤ μ) (hε : ε ≤ 1 / 2)
    (hcount : |x - μ| ≤ ε * μ) : μ / 2 ≤ x := by
  have h := (abs_le.mp hcount).1
  have hsmall := mul_le_mul_of_nonneg_right hε hμ
  linarith only [h, hsmall]

theorem eventually_good_edge_rooted_count_lower (q r : ℕ) {b α τ : ℝ}
    (hb : 0 < b) (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, ∀ K G : Hypergraph (Fin n) r, ∀ D : Finset (Block (Fin n) q),
      b * (n : ℝ) ^ (-α) ≤ density K →
      (∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q r r| ≤
          (n : ℝ) ^ (-τ) * cliqueMainTerm n (density K) q r r) →
      ∀ σ : Equiv.Perm (Fin n), ∀ e ∈ mapGraph σ.toEmbedding G,
        (b ^ (q.choose r - 1) / (2 * (q - r).factorial)) *
          (n : ℝ) ^ (-(α * ((q.choose r - 1 : ℕ) : ℝ))) * (n : ℝ) ^ (q - r) ≤
            ((mapGraph σ.toEmbedding D).filter fun Q => e.val ⊆ Q.val).card := by
  have hsmall := ((tendsto_rpow_neg_atTop hτ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall] with n hn hsn
  intro K G D hd hcount σ e he
  obtain ⟨e₀, he₀, heq⟩ := (mem_mapGraph _ _ _).mp he
  rw [← heq, card_mapGraph_containing]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf := relative_count_half_lower
    (cliqueMainTerm_nonneg hnpos.le (density_nonneg K) q r r) hsn.le (hcount e₀ he₀)
  have hlo := edgeMainTerm_polynomial_lower hnpos hb hd q r
  calc
    _ = ((b ^ (q.choose r - 1) / (q - r).factorial) *
        (n : ℝ) ^ (-(α * ((q.choose r - 1 : ℕ) : ℝ))) * (n : ℝ) ^ (q - r)) / 2 := by ring
    _ ≤ cliqueMainTerm n (density K) q r r / 2 :=
      div_le_div_of_nonneg_right hlo (by norm_num)
    _ ≤ _ := hhalf

end Arxiv2411_18291
