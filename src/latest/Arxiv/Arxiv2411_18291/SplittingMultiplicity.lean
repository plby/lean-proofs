import Arxiv.Arxiv2411_18291.SplittingPartners

/-!
# Multiplicity and boundary bounds after splitting

An edge outside the original graph belongs to a single exchange copy and
therefore to at most two replacement cliques. An original edge is covered
at most once per copy, and only copies rooted at a clique containing it
can contribute. These bounds control the full boundary multigraph for the
next random greedy placement.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem IsDecomposition.clique_count_le_one {G : Hypergraph V r} {D : Finset (Block V q)}
    (hD : IsDecomposition G D) (e : Block V r) :
    (D.filter fun Q => e.val ⊆ Q.val).card ≤ 1 := by
  rw [(isDecomposition_iff G D).mp hD e]
  split_ifs <;> omega

theorem ExchangeSystem.replacement_count_le_two (S : ExchangeSystem V q r) (e : Block V r) :
    (S.replacementCliques.filter fun Q => e.val ⊆ Q.val).card ≤ 2 := by
  rw [ExchangeSystem.replacementCliques, filter_union]
  have hp : ((S.positive.erase S.base).filter fun Q => e.val ⊆ Q.val).card ≤ 1 :=
    (card_le_card (filter_subset_filter _ (erase_subset _ _))).trans
      (S.positive_decomposition.clique_count_le_one e)
  exact (card_union_le _ _).trans (by
    have hn := S.negative_decomposition.clique_count_le_one e
    omega)

theorem ExchangeSystem.replacement_count_le_one_of_base (S : ExchangeSystem V q r)
    {e : Block V r} (he : e ∈ cliqueEdges r S.base) :
    (S.replacementCliques.filter fun Q => e.val ⊆ Q.val).card ≤ 1 := by
  apply (card_le_card (show S.replacementCliques.filter (fun Q => e.val ⊆ Q.val) ⊆
      S.negative.filter (fun Q => e.val ⊆ Q.val) from ?_)).trans
    (S.negative_decomposition.clique_count_le_one e)
  intro Q hQ
  obtain ⟨hQR, heQ⟩ := mem_filter.mp hQ
  rcases mem_union.mp hQR with hn | hp
  · exact mem_filter.mpr ⟨hn, heQ⟩
  · exact (disjoint_left.mp (S.positive_decomposition.cliques_disjoint
      (mem_erase.mp hp).2 S.base_mem (mem_erase.mp hp).1)
      ((mem_cliqueEdges _ _).mpr heQ) he).elim

variable {W : Type*} [Fintype W] [DecidableEq W] {C : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ : ℝ}

def SplittingFamily.cliques (F : SplittingFamily S D B C θ) : Finset (Block V q) :=
  exchangeSupport fun s => S.map (F.embedding s)

theorem SplittingFamily.cliques_eq_signs (F : SplittingFamily S D B C θ) :
    F.cliques = F.positiveCliques ∪ F.negativeCliques := by
  have hparts (T : ExchangeSystem V q (r + 1)) (b : Bool) :
      T.replacementCliques = T.positiveReplacement b ∪ T.negativeReplacement b := by
    cases b
    · exact union_comm _ _
    · rfl
  unfold cliques exchangeSupport positiveCliques negativeCliques
  rw [← biUnion_union]
  apply congrArg (fun f : SignedCliqueSlots D C → Finset (Block V q) => univ.biUnion f)
  funext s
  exact hparts _ s.2.1

theorem SplittingFamily.copy_count_original (F : SplittingFamily S D B C θ)
    (s : SignedCliqueSlots D C) (e : Block V (r + 1)) (heB : e ∈ B) :
    ((S.map (F.embedding s)).replacementCliques.filter fun Q => e.val ⊆ Q.val).card ≤
      if e.val ⊆ s.1.val.val then 1 else 0 := by
  by_cases heRoot : e.val ⊆ s.1.val.val
  · rw [if_pos heRoot]
    apply (S.map (F.embedding s)).replacement_count_le_one_of_base
    change e ∈ cliqueEdges (r + 1) (mapBlock (F.embedding s) S.base)
    rw [F.base s]
    exact (mem_cliqueEdges _ _).mpr heRoot
  · rw [if_neg heRoot]
    apply Nat.le_zero.mpr
    rw [card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    obtain ⟨hQR, heQ⟩ := mem_filter.mp hQ
    rw [S.replacementCliques_map] at hQR
    obtain ⟨Q₀, hQ₀, rfl⟩ := (mem_mapGraph _ _ _).mp hQR
    have heI := mem_inter.mpr ⟨(mem_cliqueEdges _ _).mpr heQ, heB⟩
    rw [F.copy_clique_inter s Q₀ (S.replacement_clique_subset hQ₀)] at heI
    have hroot := (mem_cliqueEdges _ _).mp (mem_inter.mp heI).2
    rw [F.base s] at hroot
    exact heRoot hroot

theorem SplittingFamily.clique_count_original (F : SplittingFamily S D B C θ)
    (e : Block V (r + 1)) (heB : e ∈ B) :
    (F.cliques.filter fun Q => e.val ⊆ Q.val).card ≤
      2 * C * (D.filter fun Q => e.val ⊆ Q.val).card := by
  rw [cliques, exchangeSupport, filter_biUnion]
  calc
    _ ≤ ∑ s : SignedCliqueSlots D C,
        ((S.map (F.embedding s)).replacementCliques.filter fun Q => e.val ⊆ Q.val).card :=
      card_biUnion_le
    _ ≤ ∑ s : SignedCliqueSlots D C, if e.val ⊆ s.1.val.val then 1 else 0 :=
      sum_le_sum fun s _ => F.copy_count_original s e heB
    _ = familyDegree (fun s : SignedCliqueSlots D C => s.1.val) e.val := by
      rw [familyDegree, ← sum_filter]
      simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
    _ ≤ _ := repeated_clique_degree_le D (fun s : SignedCliqueSlots D C => s.1.val)
      (fun s => s.1.property) (signedCliqueSlots_root_count D C) e.val

theorem SplittingFamily.clique_count_outside (F : SplittingFamily S D B C θ)
    (e : Block V (r + 1)) (heB : e ∉ B) :
    (F.cliques.filter fun Q => e.val ⊆ Q.val).card ≤ 2 := by
  by_cases hex : ∃ Q ∈ F.cliques, e.val ⊆ Q.val
  · obtain ⟨Q, hQ, heQ⟩ := hex
    obtain ⟨s, _, hs⟩ := mem_biUnion.mp hQ
    have hes : e ∈ mapGraph (F.embedding s) S.graph :=
      (S.map (F.embedding s)).replacement_clique_subset hs ((mem_cliqueEdges _ _).mpr heQ)
    apply (card_le_card (show F.cliques.filter (fun Q => e.val ⊆ Q.val) ⊆
        (S.map (F.embedding s)).replacementCliques.filter (fun Q => e.val ⊆ Q.val) from ?_)).trans
      ((S.map (F.embedding s)).replacement_count_le_two e)
    intro R hR
    obtain ⟨hR, heR⟩ := mem_filter.mp hR
    obtain ⟨t, _, ht⟩ := mem_biUnion.mp hR
    have het : e ∈ mapGraph (F.embedding t) S.graph :=
      (S.map (F.embedding t)).replacement_clique_subset ht ((mem_cliqueEdges _ _).mpr heR)
    have hst := F.copy_index_unique hes het heB
    subst t
    exact mem_filter.mpr ⟨ht, heR⟩
  · have hzero : F.cliques.filter (fun Q => e.val ⊆ Q.val) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      exact hex ⟨Q, (mem_filter.mp hQ).1, (mem_filter.mp hQ).2⟩
    rw [hzero, card_empty]
    omega

theorem SplittingFamily.clique_multiplicity (F : SplittingFamily S D B C θ) {M : ℕ}
    (hmult : ∀ e : Block V (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (e : Block V (r + 1)) :
    (F.cliques.filter fun Q => e.val ⊆ Q.val).card ≤ 2 * C * M + 2 := by
  by_cases heB : e ∈ B
  · exact (F.clique_count_original e heB).trans
      ((Nat.mul_le_mul_left (2 * C) (hmult e)).trans (Nat.le_add_right _ _))
  · exact (F.clique_count_outside e heB).trans (Nat.le_add_left _ _)

theorem SplittingFamily.cliques_support (F : SplittingFamily S D B C θ) :
    cliqueSupport (r + 1) F.cliques ⊆
      B ∪ univ.biUnion (fun s => mapGraph (F.embedding s) (newEdges S.base.val S.graph)) := by
  intro e he
  obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
  obtain ⟨s, _, hs⟩ := mem_biUnion.mp hQ
  by_cases heB : e ∈ B
  · exact mem_union_left _ heB
  · refine mem_union_right _ (mem_biUnion.mpr ⟨s, mem_univ _, ?_⟩)
    exact F.copy_new_of_notMem s e ((S.map (F.embedding s)).replacement_clique_subset hs heQ) heB

theorem SplittingFamily.cliques_bounded (F : SplittingFamily S D B C θ) {M : ℕ}
    (hmult : ∀ e : Block V (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ M) :
    IsCliqueFamilyBounded r F.cliques (((2 * C * M + 2 : ℕ) : ℝ) * θ) :=
  F.bounded.cliqueFamilyBounded F.cliques (by omega) (F.clique_multiplicity hmult) F.cliques_support

end Arxiv2411_18291
