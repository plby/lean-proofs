import Arxiv.Arxiv2411_18291.ExchangeFrameStructure

/-!
# Clique counts in an exchange

Both decompositions partition the graph into equally sized cliques.
These identities bound the near-frame density loss and the number of
independent far-clique colours in terms of the graph's edge count.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}
variable {S : ExchangeSystem W q r} {A : Finset (Block W q)}

theorem ExchangeSystem.far_card_mul_le (S : ExchangeSystem W q r) :
    q.choose r * S.farCliques.card ≤ 2 * S.graph.card := by
  have hfar : S.farCliques.card ≤ S.negative.card + S.positive.card := by
    calc
      _ ≤ S.replacementCliques.card := card_le_card sdiff_subset
      _ ≤ S.negative.card + (S.positive.erase S.base).card := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (card_le_card (erase_subset _ _)) _
  calc
    _ ≤ q.choose r * (S.negative.card + S.positive.card) := Nat.mul_le_mul_left _ hfar
    _ = 2 * S.graph.card := by
      rw [Nat.mul_add, ← S.negative_decomposition.card_eq, ← S.positive_decomposition.card_eq]
      omega

theorem IsExchangeFamily.choose_sq_le (hA : IsExchangeFamily S A) (hr : 0 < r) :
    q.choose r * q.choose r ≤ S.graph.card := by
  have hnear : S.nearCliques.card ≤ S.negative.card :=
    card_le_card (fun _ hQ => S.near_negative hQ)
  rw [hA.near_card hr] at hnear
  rw [S.negative_decomposition.card_eq]
  exact Nat.mul_le_mul_left _ hnear

theorem IsExchangeFamily.colour_exponent_le (hA : IsExchangeFamily S A) (hr : 0 < r)
    {α : ℝ} (hα : 0 ≤ α) :
    α * ((q.choose r - 1 : ℕ) : ℝ) * q.choose r +
      2 * (α * q.choose r) * S.farCliques.card ≤ 5 * α * S.graph.card := by
  have hnear : ((q.choose r - 1 : ℕ) : ℝ) * q.choose r ≤ (S.graph.card : ℝ) := by
    exact_mod_cast (Nat.mul_le_mul_right (q.choose r) (Nat.sub_le (q.choose r) 1)).trans
      (hA.choose_sq_le hr)
  have hfar : (q.choose r : ℝ) * S.farCliques.card ≤ 2 * S.graph.card := by
    exact_mod_cast S.far_card_mul_le
  have hn := mul_le_mul_of_nonneg_left hnear hα
  have hf := mul_le_mul_of_nonneg_left hfar hα
  nlinarith only [hn, hf]

end Arxiv2411_18291
