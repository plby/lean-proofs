import Arxiv.Arxiv2411_18291.CliqueSquaredDegrees

/-! # Initial clique-count accuracy from degree accuracy -/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291

theorem clique_count_deviation_of_degrees {V : Type*} [Fintype V] [DecidableEq V]
    {q r : ℕ} (hqr : r ≤ q) (G : Hypergraph V r) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) (D δ : ℝ)
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ δ) :
    |(H.card : ℝ) - D * G.card / (q.choose r : ℝ)| ≤ δ * G.card / (q.choose r : ℝ) := by
  have hk : (0 : ℝ) < q.choose r := by exact_mod_cast Nat.choose_pos hqr
  have hsum : |∑ e ∈ G, (((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D)| ≤
      δ * G.card := by
    calc
      _ ≤ ∑ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ G, δ := sum_le_sum hd
      _ = _ := by simp [mul_comm]
  rw [sum_sub_distrib, sum_clique_degree_over_graph G H hHG, sum_const,
    nsmul_eq_mul, mul_comm (G.card : ℝ) D] at hsum
  calc
    _ = |((H.card : ℝ) * q.choose r - D * G.card) / (q.choose r : ℝ)| := by
      congr 1
      field_simp
    _ = |(H.card : ℝ) * q.choose r - D * G.card| / (q.choose r : ℝ) := by
      rw [abs_div, abs_of_pos hk]
    _ ≤ _ := div_le_div_of_nonneg_right hsum hk.le

end Arxiv2411_18291
