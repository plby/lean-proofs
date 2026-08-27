import Arxiv.Arxiv2411_18291.CliqueEdgeRemoval

/-!
# The loss in an edge degree frozen on removal

If a selected clique contains the tracked edge, the tracked value stays
fixed. Otherwise its loss is the number of discarded cliques through
that edge. Double counting expresses the total loss as a sum over the
tracked edge's cliques, with all selected cliques through the edge excluded.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem cliqueNeighborhood_eq_filter (H : Finset (Block V q)) (Q : Block V q) :
    cliqueNeighborhood r H Q =
      H.filter (fun P => ¬Disjoint (cliqueEdges r P) (cliqueEdges r Q)) := by
  ext P
  rw [mem_cliqueNeighborhood, mem_filter]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨e, heQ, heP⟩ hd
    exact disjoint_left.mp hd ((mem_cliqueEdges _ _).mpr heP) ((mem_cliqueEdges _ _).mpr heQ)
  · intro hn
    by_contra h
    apply hn
    apply disjoint_left.mpr
    intro e heP heQ
    exact h ⟨e, (mem_cliqueEdges _ _).mp heQ, (mem_cliqueEdges _ _).mp heP⟩

def frozenEdgeLoss (H : Finset (Block V q)) (e : Block V r) (Q : Block V q) : ℕ :=
  if ¬e.val ⊆ Q.val then ((cliqueNeighborhood r H Q).filter fun P => e.val ⊆ P.val).card
  else 0

theorem frozenEdgeLoss_le (hqr : r < q) (H : Finset (Block V q))
    (e : Block V r) (Q : Block V q) :
    frozenEdgeLoss H e Q ≤ q.choose r * (Fintype.card V) ^ (q - r - 1) := by
  unfold frozenEdgeLoss
  split_ifs with h
  · exact Nat.zero_le _
  · exact cliqueNeighborhood_edge_count_le hqr H e Q h

theorem sum_frozenEdgeLoss (H : Finset (Block V q)) (e : Block V r) :
    (∑ Q ∈ H, frozenEdgeLoss H e Q) =
      ∑ P ∈ H.filter (fun P => e.val ⊆ P.val),
        (cliqueNeighborhood r (H.filter fun Q => ¬e.val ⊆ Q.val) P).card := by
  simp only [frozenEdgeLoss, cliqueNeighborhood_eq_filter, card_eq_sum_ones, sum_filter,
    Finset.ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro P _
  apply sum_congr rfl
  intro Q _
  by_cases heP : e.val ⊆ P.val
  · by_cases heQ : e.val ⊆ Q.val
    · simp [heP, heQ]
    · simp [heP, heQ, disjoint_comm]
  · simp [heP]

end Arxiv2411_18291
