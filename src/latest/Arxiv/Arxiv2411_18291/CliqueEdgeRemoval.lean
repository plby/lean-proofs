import Arxiv.Arxiv2411_18291.CliqueRemovalCounts

/-!
# The change in an edge's clique degree

If the selected clique does not contain the tracked edge, every lost
clique contains that edge and a distinct edge of the selected clique.
The pair-codegree bound therefore gives a much smaller one-step change
than the total clique degree. A tracked degree must be frozen when its
edge itself is removed; that exceptional case is explicitly excluded here.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem cliqueRemoval_degree_partition (H : Finset (Block V q))
    (e : Block V r) (Q : Block V q) :
    ((cliqueRemoval r H Q).filter fun P => e.val ⊆ P.val).card +
      ((cliqueNeighborhood r H Q).filter fun P => e.val ⊆ P.val).card =
        (H.filter fun P => e.val ⊆ P.val).card := by
  have heq : (cliqueRemoval r H Q).filter (fun P => e.val ⊆ P.val) =
      (H.filter fun P => e.val ⊆ P.val) \
        ((cliqueNeighborhood r H Q).filter fun P => e.val ⊆ P.val) := by
    ext P
    simp only [cliqueRemoval, mem_filter, mem_sdiff]
    tauto
  rw [heq]
  exact card_sdiff_add_card_eq_card
    (filter_subset_filter _ (cliqueNeighborhood_subset H Q))

theorem cliqueNeighborhood_edge_filter_eq (H : Finset (Block V q))
    (e : Block V r) (Q : Block V q) :
    (cliqueNeighborhood r H Q).filter (fun P => e.val ⊆ P.val) =
      (cliqueEdges r Q).biUnion (fun f => H.filter fun P => e.val ⊆ P.val ∧ f.val ⊆ P.val) := by
  ext P
  simp only [mem_filter, mem_cliqueNeighborhood, mem_biUnion, mem_cliqueEdges]
  constructor
  · rintro ⟨⟨hPH, f, hfQ, hfP⟩, heP⟩
    exact ⟨f, hfQ, hPH, heP, hfP⟩
  · rintro ⟨f, hfQ, hPH, heP, hfP⟩
    exact ⟨⟨hPH, f, hfQ, hfP⟩, heP⟩

theorem cliqueNeighborhood_edge_count_le (hqr : r < q) (H : Finset (Block V q))
    (e : Block V r) (Q : Block V q) (heQ : ¬e.val ⊆ Q.val) :
    ((cliqueNeighborhood r H Q).filter fun P => e.val ⊆ P.val).card ≤
      q.choose r * (Fintype.card V) ^ (q - r - 1) := by
  rw [cliqueNeighborhood_edge_filter_eq]
  calc
    _ ≤ ∑ f ∈ cliqueEdges r Q,
        (H.filter fun P => e.val ⊆ P.val ∧ f.val ⊆ P.val).card := card_biUnion_le
    _ ≤ ∑ _f ∈ cliqueEdges r Q, (Fintype.card V) ^ (q - r - 1) := by
      apply sum_le_sum
      intro f hf
      apply clique_codegree_le_power hqr H e f
      rintro rfl
      exact heQ ((mem_cliqueEdges _ _).mp hf)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_cliqueEdges, Nat.cast_id]

theorem cliqueRemoval_degree_change_le (hqr : r < q) (H : Finset (Block V q))
    (e : Block V r) (Q : Block V q) (heQ : ¬e.val ⊆ Q.val) :
    (H.filter fun P => e.val ⊆ P.val).card -
      ((cliqueRemoval r H Q).filter fun P => e.val ⊆ P.val).card ≤
        q.choose r * (Fintype.card V) ^ (q - r - 1) := by
  have hpart := cliqueRemoval_degree_partition H e Q
  have hbound := cliqueNeighborhood_edge_count_le hqr H e Q heQ
  omega

end Arxiv2411_18291
