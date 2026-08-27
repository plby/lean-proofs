import Arxiv.Arxiv2411_18291.GroupEliminationCounts
import Arxiv.Arxiv2411_18291.SharpEliminationCounts

/-!
# Multiplicity reduction by eliminating rooted clique groups

Every eliminated group has a common old edge, which the exchange removes.
Other old edges cannot enter that group. Away from the old edge set, two
input occurrences become at most twice the group size plus two occurrences.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r m : ℕ}
variable {D : Finset (Block V q)} {B B₀ : Hypergraph V r}

theorem RootedCliqueGrouping.original_edge_eq_root (R : RootedCliqueGrouping D B m)
    (hB : B ⊆ B₀) (hsingle : ∀ P ∈ D, (cliqueEdges r P ∩ B₀).card ≤ 1)
    (c : R.groups) {P : Block V q} (hPc : P ∈ c.val) {e : Block V r}
    (he : e ∈ B₀) (heP : e.val ⊆ P.val) : e = (R.root c).val := by
  exact card_le_one.mp (hsingle P (R.subset c.val c.property hPc)) e
    (mem_inter.mpr ⟨(mem_cliqueEdges _ _).mpr heP, he⟩) (R.root c).val
    (mem_inter.mpr ⟨(mem_cliqueEdges _ _).mpr (R.root_mem c P hPc),
      hB (R.root c).property⟩)

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B B₀ H : Hypergraph V (r + 1)} {θ : ℝ}

theorem EliminationFamily.grouped_count_original_eq_zero (R : RootedCliqueGrouping D B m)
    (Q : R.groups → Block V q) (hQ : ∀ c, Q c ∈ c.val)
    (F : EliminationFamily S N H (fun i : GroupEliminationIndex R.groups Q => Q i.1)
      (fun i => i.2.val) θ) (hpair : IsEliminationPair S N e₀)
    (hB : B ⊆ B₀) (hH : B₀ ⊆ H)
    (hsingle : ∀ P ∈ D, (cliqueEdges (r + 1) P ∩ B₀).card ≤ 1)
    (e : Block V (r + 1)) (he : e ∈ B₀) :
    (F.cliques.filter fun P => e.val ⊆ P.val).card = 0 := by
  have hcopy (i : GroupEliminationIndex R.groups Q) :
      ((mapGraph (F.embedding i) (S.eliminationCliques N)).filter
        fun P => e.val ⊆ P.val).card = 0 := by
    by_cases hp : e.val ⊆ (Q i.1).val
    · have heq := R.original_edge_eq_root hB hsingle i.1 (hQ i.1) he hp
      have hn : e.val ⊆ i.2.val.val := by
        rw [heq]
        exact R.root_mem i.1 i.2.val (mem_erase.mp i.2.property).2
      exact F.copy_count_common_eq_zero hpair.negative_mem i e
        ((mem_cliqueEdges _ _).mpr hp) ((mem_cliqueEdges _ _).mpr hn)
    · have hn : ¬e.val ⊆ i.2.val.val := by
        intro hn
        have heq := R.original_edge_eq_root hB hsingle i.1
          (mem_erase.mp i.2.property).2 he hn
        apply hp
        rw [heq]
        exact R.root_mem i.1 (Q i.1) (hQ i.1)
      have h := F.copy_count_original_sharp hpair i e (hH he)
      simpa only [if_neg hp, if_neg hn, add_zero, Nat.le_zero] using h
  apply Nat.le_zero.mp
  rw [EliminationFamily.cliques, filter_biUnion]
  exact card_biUnion_le.trans (by simp only [hcopy, sum_const_zero, le_refl])

theorem EliminationFamily.grouped_multiplicity (R : RootedCliqueGrouping D B m)
    (Q : R.groups → Block V q) (hQ : ∀ c, Q c ∈ c.val)
    (F : EliminationFamily S N H (fun i : GroupEliminationIndex R.groups Q => Q i.1)
      (fun i => i.2.val) θ) (hpair : IsEliminationPair S N e₀)
    (hB : B ⊆ B₀) (hH : B₀ ⊆ H) (hsupport : cliqueSupport (r + 1) D ⊆ H)
    (hsingle : ∀ P ∈ D, (cliqueEdges (r + 1) P ∩ B₀).card ≤ 1)
    {K : ℕ} (hlow : ∀ e ∈ B₀, e ∉ B → (D.filter fun P => e.val ⊆ P.val).card ≤ K)
    (hnew : ∀ e : Block V (r + 1), e ∉ B₀ → (D.filter fun P => e.val ⊆ P.val).card ≤ 2)
    (e : Block V (r + 1)) :
    (((groupEliminationRetained D R.groups Q) ∪ F.cliques).filter
      fun P => e.val ⊆ P.val).card ≤ max K (2 * m + 2) := by
  rw [filter_union]
  apply (card_union_le _ _).trans
  by_cases he₀ : e ∈ B₀
  · rw [F.grouped_count_original_eq_zero R Q hQ hpair hB hH hsingle e he₀, add_zero]
    by_cases heB : e ∈ B
    · exact (R.retained_root_count Q ⟨e, heB⟩).trans
        (le_trans (by omega) (le_max_right K (2 * m + 2)))
    · exact (card_le_card (filter_subset_filter _ sdiff_subset)).trans
        ((hlow e he₀ heB).trans (le_max_left _ _))
  · by_cases heH : e ∈ H
    · have hf := F.clique_count_original_sharp hpair e heH
      have hl := (groupEliminationLeft_degree_le R.groups Q e.val).trans
        (representativeDegree_le_mul D R.groups R.subset R.disjoint Q hQ R.size e.val)
      have hr := retained_add_eliminated_count D R.groups R.subset R.disjoint Q e.val
      have hc := hnew e he₀
      have hm := Nat.mul_le_mul_left m hc
      have hbound : ((groupEliminationRetained D R.groups Q).filter
          fun P => e.val ⊆ P.val).card + (F.cliques.filter fun P => e.val ⊆ P.val).card ≤
            2 * m + 2 := by omega
      exact hbound.trans (le_max_right _ _)
    · have hz : ((groupEliminationRetained D R.groups Q).filter
          fun P => e.val ⊆ P.val).card = 0 := by
        rw [card_eq_zero]
        apply eq_empty_iff_forall_notMem.mpr
        intro P hP
        exact heH (hsupport (mem_biUnion.mpr ⟨P, (mem_sdiff.mp (mem_filter.mp hP).1).1,
          (mem_cliqueEdges _ _).mpr (mem_filter.mp hP).2⟩))
      rw [hz, zero_add]
      exact (F.clique_count_outside hpair e heH).trans
        (le_trans (by omega) (le_max_right K (2 * m + 2)))

end Arxiv2411_18291
