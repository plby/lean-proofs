import Arxiv.Arxiv2411_18291.CliqueFaceLoss

/-! # Average loss of a face degree under current clique-degree bounds -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem cliqueFaceLoss_average_bounds (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) (f : Block V r)
    (dmin dmax : ℝ)
    (hd : ∀ e ∈ G, dmin ≤ ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ∧
      ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ dmax) :
    ((G.filter fun e => f.val ⊆ e.val).card : ℝ) * dmin / H.card ≤
        (∑ Q ∈ H, (cliqueFaceLoss G f Q : ℝ)) / H.card ∧
      (∑ Q ∈ H, (cliqueFaceLoss G f Q : ℝ)) / H.card ≤
        ((G.filter fun e => f.val ⊆ e.val).card : ℝ) * dmax / H.card := by
  have hn : (0 : ℝ) ≤ H.card := Nat.cast_nonneg _
  rw [sum_cliqueFaceLoss G H hHG f]
  constructor
  · apply div_le_div_of_nonneg_right _ hn
    calc
      _ = ∑ _e ∈ G.filter (fun e => f.val ⊆ e.val), dmin := by simp
      _ ≤ _ := sum_le_sum fun e he => (hd e (mem_filter.mp he).1).1
  · apply div_le_div_of_nonneg_right _ hn
    calc
      _ ≤ ∑ _e ∈ G.filter (fun e => f.val ⊆ e.val), dmax :=
        sum_le_sum fun e he => (hd e (mem_filter.mp he).1).2
      _ = _ := by simp

end Arxiv2411_18291
