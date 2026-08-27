import Arxiv.Arxiv2411_18291.EliminationMultiplicity
import Arxiv.Arxiv2411_18291.IntegralExchangeGeneration

/-!
# Elimination multiplicities on the prescribed roots

Deleting a decomposition clique removes all occurrences of its edges from
that sign. An edge of either root therefore appears at most once among
the remaining cliques, and a common-root edge disappears completely.
The placed-family bound counts indexed roots with coefficient one.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem ExchangeSystem.elimination_count_le_one_of_root (S : ExchangeSystem V q r)
    {N : Block V q} (hN : N ∈ S.negative) (e : Block V r)
    (he : e ∈ cliqueEdges r S.base ∪ cliqueEdges r N) :
    ((S.eliminationCliques N).filter fun Q => e.val ⊆ Q.val).card ≤ 1 := by
  rcases mem_union.mp he with heP | heN
  · apply (card_le_card (show (S.eliminationCliques N).filter (fun Q => e.val ⊆ Q.val) ⊆
        S.negative.filter (fun Q => e.val ⊆ Q.val) from ?_)).trans
      (S.negative_decomposition.clique_count_le_one e)
    intro Q hQ
    obtain ⟨hQ, heQ⟩ := mem_filter.mp hQ
    rcases mem_union.mp hQ with hn | hp
    · exact mem_filter.mpr ⟨(mem_erase.mp hn).2, heQ⟩
    · exact (disjoint_left.mp (S.eliminationNegative_disjoint_base hp)
        ((mem_cliqueEdges _ _).mpr heQ) heP).elim
  · apply (card_le_card (show (S.eliminationCliques N).filter (fun Q => e.val ⊆ Q.val) ⊆
        S.positive.filter (fun Q => e.val ⊆ Q.val) from ?_)).trans
      (S.positive_decomposition.clique_count_le_one e)
    intro Q hQ
    obtain ⟨hQ, heQ⟩ := mem_filter.mp hQ
    rcases mem_union.mp hQ with hn | hp
    · exact (disjoint_left.mp (S.eliminationPositive_disjoint_negative hN hn)
        ((mem_cliqueEdges _ _).mpr heQ) heN).elim
    · exact mem_filter.mpr ⟨(mem_erase.mp hp).2, heQ⟩

theorem ExchangeSystem.elimination_count_common_eq_zero (S : ExchangeSystem V q r)
    {N : Block V q} (hN : N ∈ S.negative) (e : Block V r)
    (heP : e ∈ cliqueEdges r S.base) (heN : e ∈ cliqueEdges r N) :
    ((S.eliminationCliques N).filter fun Q => e.val ⊆ Q.val).card = 0 := by
  rw [card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro Q hQ
  exact S.elimination_avoids_common hN heP heN (mem_filter.mp hQ).1
    ((mem_cliqueEdges _ _).mpr (mem_filter.mp hQ).2)

variable {I W : Type*} [Fintype I] [Fintype W] [DecidableEq W]
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

theorem EliminationFamily.copy_count_le_one_of_root (F : EliminationFamily S N B P Q θ)
    (hN : N ∈ S.negative) (i : I) (e : Block V (r + 1))
    (he : e ∈ cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (Q i)) :
    ((mapGraph (F.embedding i) (S.eliminationCliques N)).filter
      fun R => e.val ⊆ R.val).card ≤ 1 := by
  have hN' : mapBlock (F.embedding i) N ∈ (S.map (F.embedding i)).negative :=
    (mem_mapGraph _ _ _).mpr ⟨N, hN, rfl⟩
  have h := (S.map (F.embedding i)).elimination_count_le_one_of_root hN' e
    (by simpa only [ExchangeSystem.map, F.positive_root, F.negative_root] using he)
  rwa [S.eliminationCliques_map] at h

theorem EliminationFamily.copy_count_common_eq_zero (F : EliminationFamily S N B P Q θ)
    (hN : N ∈ S.negative) (i : I) (e : Block V (r + 1))
    (heP : e ∈ cliqueEdges (r + 1) (P i)) (heQ : e ∈ cliqueEdges (r + 1) (Q i)) :
    ((mapGraph (F.embedding i) (S.eliminationCliques N)).filter
      fun R => e.val ⊆ R.val).card = 0 := by
  have hN' : mapBlock (F.embedding i) N ∈ (S.map (F.embedding i)).negative :=
    (mem_mapGraph _ _ _).mpr ⟨N, hN, rfl⟩
  have h := (S.map (F.embedding i)).elimination_count_common_eq_zero hN' e
    (by simpa only [ExchangeSystem.map, F.positive_root] using heP)
    (by simpa only [F.negative_root] using heQ)
  rwa [S.eliminationCliques_map] at h

theorem EliminationFamily.copy_count_original_sharp (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) (e : Block V (r + 1)) (heB : e ∈ B) :
    ((mapGraph (F.embedding i) (S.eliminationCliques N)).filter fun R => e.val ⊆ R.val).card ≤
      (if e.val ⊆ (P i).val then 1 else 0) + (if e.val ⊆ (Q i).val then 1 else 0) := by
  by_cases heP : e.val ⊆ (P i).val
  · have h := F.copy_count_le_one_of_root hpair.negative_mem i e
      (mem_union_left _ ((mem_cliqueEdges _ _).mpr heP))
    rw [if_pos heP]
    exact h.trans (by split_ifs <;> omega)
  · by_cases heQ : e.val ⊆ (Q i).val
    · have h := F.copy_count_le_one_of_root hpair.negative_mem i e
        (mem_union_right _ ((mem_cliqueEdges _ _).mpr heQ))
      simpa only [if_neg heP, if_pos heQ, zero_add] using h
    · have h := F.copy_count_original hpair i e heB
      simpa only [if_neg heP, if_neg heQ, add_zero, mul_zero] using h

theorem EliminationFamily.clique_count_original_sharp (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (e : Block V (r + 1)) (heB : e ∈ B) :
    (F.cliques.filter fun R => e.val ⊆ R.val).card ≤
      familyDegree P e.val + familyDegree Q e.val := by
  rw [cliques, filter_biUnion]
  calc
    _ ≤ ∑ i, ((mapGraph (F.embedding i) (S.eliminationCliques N)).filter
        fun R => e.val ⊆ R.val).card := card_biUnion_le
    _ ≤ ∑ i, ((if e.val ⊆ (P i).val then 1 else 0) +
        (if e.val ⊆ (Q i).val then 1 else 0)) :=
      sum_le_sum fun i _ => F.copy_count_original_sharp hpair i e heB
    _ = _ := by
      simp only [sum_add_distrib, familyDegree, card_eq_sum_ones, sum_filter]

end Arxiv2411_18291
