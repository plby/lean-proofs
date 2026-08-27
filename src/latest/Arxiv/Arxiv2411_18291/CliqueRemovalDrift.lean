import Arxiv.Arxiv2411_18291.CliqueRemovalCounts
import Mathlib.Data.Real.Basic

/-!
# Double counting the average loss in clique removal

The sum of the edge-neighborhood estimates over selected cliques equals
the sum of squared edge degrees. The overlap bound makes the resulting
one-step average drift estimate explicit.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem sum_clique_family_edge_weights {R : Type*} [Semiring R]
    (H : Finset (Block V q)) (w : Block V r → R) :
    (∑ Q ∈ H, ∑ e ∈ cliqueEdges r Q, w e) =
      ∑ e, ((H.filter fun Q => e.val ⊆ Q.val).card : R) * w e := by
  simp only [cliqueEdges, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  rw [← sum_filter, sum_const, nsmul_eq_mul]

theorem sum_clique_edge_degrees (H : Finset (Block V q)) :
    (∑ Q ∈ H, ∑ e ∈ cliqueEdges r Q, (H.filter fun P => e.val ⊆ P.val).card) =
      ∑ e : Block V r, (H.filter fun P => e.val ⊆ P.val).card ^ 2 := by
  simpa only [Nat.cast_id, ← sq] using
    sum_clique_family_edge_weights H (fun e : Block V r => (H.filter fun P => e.val ⊆ P.val).card)

theorem cliqueRemoval_total_loss_bounds (hqr : r < q) (H : Finset (Block V q)) :
    (∑ Q ∈ H, (cliqueNeighborhood r H Q).card) ≤
        (∑ e : Block V r, (H.filter fun P => e.val ⊆ P.val).card ^ 2) ∧
      (∑ e : Block V r, (H.filter fun P => e.val ⊆ P.val).card ^ 2) ≤
        (∑ Q ∈ H, (cliqueNeighborhood r H Q).card) +
          H.card * ((q.choose r) ^ 2 * (Fintype.card V) ^ (q - r - 1)) := by
  constructor
  · rw [← sum_clique_edge_degrees]
    exact sum_le_sum fun Q _ => cliqueNeighborhood_card_le_sum H Q
  · rw [← sum_clique_edge_degrees]
    calc
      _ ≤ ∑ Q ∈ H, ((cliqueNeighborhood r H Q).card +
          (q.choose r) ^ 2 * (Fintype.card V) ^ (q - r - 1)) :=
        sum_le_sum fun Q _ => cliqueNeighborhood_sum_le_card_add_error hqr H Q
      _ = _ := by rw [sum_add_distrib]; simp

theorem cliqueRemoval_average_loss_bounds (hqr : r < q)
    (H : Finset (Block V q)) (hH : H.Nonempty) :
    let S := ∑ e : Block V r, ((H.filter fun P => e.val ⊆ P.val).card : ℝ) ^ 2
    let L := (∑ Q ∈ H, ((cliqueNeighborhood r H Q).card : ℝ)) / H.card
    S / H.card - (q.choose r : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (q - r - 1) ≤ L ∧
      L ≤ S / H.card := by
  obtain ⟨hlo, hhi⟩ := cliqueRemoval_total_loss_bounds hqr H
  have hcard : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hlo' : (∑ Q ∈ H, ((cliqueNeighborhood r H Q).card : ℝ)) ≤
      ∑ e : Block V r, ((H.filter fun P => e.val ⊆ P.val).card : ℝ) ^ 2 := by
    exact_mod_cast hlo
  have hhi' : (∑ e : Block V r, ((H.filter fun P => e.val ⊆ P.val).card : ℝ) ^ 2) ≤
      (∑ Q ∈ H, ((cliqueNeighborhood r H Q).card : ℝ)) +
        H.card * ((q.choose r : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (q - r - 1)) := by
    exact_mod_cast hhi
  dsimp only
  constructor
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hcard).mpr
    rw [add_mul, div_mul_cancel₀ _ hcard.ne']
    simpa only [mul_comm] using hhi'
  · exact div_le_div_of_nonneg_right hlo' hcard.le

end Arxiv2411_18291
