import Arxiv.Arxiv2411_18291.EliminationNegativeGeometry
import Arxiv.Arxiv2411_18291.SplittingMultiplicity

/-!
# Support and local multiplicity of an elimination family

Both signs lie in the sparse extension graph. Each exchange copy covers
an edge at most twice, and an edge outside the previous graph belongs to
only one copy. These facts provide the support and local counting bounds
for the next elimination stage.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {I : Type*} [Fintype I] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

def EliminationFamily.graph (F : EliminationFamily S N B P Q θ) : Hypergraph V (r + 1) :=
  B ∪ univ.biUnion fun i => mapGraph (F.embedding i) (newEdges (S.base.val ∪ N.val) S.graph)

def EliminationFamily.cliques (F : EliminationFamily S N B P Q θ) : Finset (Block V q) :=
  univ.biUnion fun i => mapGraph (F.embedding i) (S.eliminationCliques N)

theorem EliminationFamily.cliques_eq_signs (F : EliminationFamily S N B P Q θ) :
    F.cliques = F.positiveCliques ∪ F.negativeCliques := by
  simp only [cliques, ExchangeSystem.eliminationCliques, mapGraph_union, biUnion_union,
    positiveCliques, negativeCliques]

theorem ExchangeSystem.elimination_subset_replacement (S : ExchangeSystem W q (r + 1))
    (N : Block W q) : S.eliminationCliques N ⊆ S.replacementCliques :=
  union_subset_union (erase_subset _ _) Subset.rfl

theorem EliminationFamily.clique_copy_graph (F : EliminationFamily S N B P Q θ)
    (i : I) {R : Block V q} (hR : R ∈ mapGraph (F.embedding i) (S.eliminationCliques N)) :
    cliqueEdges (r + 1) R ⊆ mapGraph (F.embedding i) S.graph := by
  obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hR
  rw [← map_cliqueEdges]
  exact mapGraph_mono _ (S.elimination_clique_subset N hR₀)

theorem EliminationFamily.copy_count_le_two (F : EliminationFamily S N B P Q θ)
    (i : I) (e : Block V (r + 1)) :
    ((mapGraph (F.embedding i) (S.eliminationCliques N)).filter fun R => e.val ⊆ R.val).card ≤
      2 := by
  have hsub : mapGraph (F.embedding i) (S.eliminationCliques N) ⊆
      (S.map (F.embedding i)).replacementCliques := by
    rw [S.replacementCliques_map]
    exact mapGraph_mono _ (S.elimination_subset_replacement N)
  exact (card_le_card (filter_subset_filter _ hsub)).trans
    ((S.map (F.embedding i)).replacement_count_le_two e)

theorem EliminationFamily.copy_index_unique (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {i j : I} {e : Block V (r + 1)}
    (hei : e ∈ mapGraph (F.embedding i) S.graph)
    (hej : e ∈ mapGraph (F.embedding j) S.graph) (heB : e ∉ B) : i = j := by
  by_contra hij
  exact heB (F.copy_inter_subset hpair hij (mem_inter.mpr ⟨hei, hej⟩))

theorem EliminationFamily.cliques_support (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) : cliqueSupport (r + 1) F.cliques ⊆ F.graph := by
  intro e he
  obtain ⟨R, hR, heR⟩ := mem_biUnion.mp he
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
  by_cases heB : e ∈ B
  · exact mem_union_left _ heB
  · exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _,
      F.copy_new_of_notMem hpair i e (F.clique_copy_graph i hi heR) heB⟩)

theorem EliminationFamily.clique_count_outside (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (e : Block V (r + 1)) (heB : e ∉ B) :
    (F.cliques.filter fun R => e.val ⊆ R.val).card ≤ 2 := by
  by_cases hex : ∃ R ∈ F.cliques, e.val ⊆ R.val
  · obtain ⟨R, hR, heR⟩ := hex
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
    have hei := F.clique_copy_graph i hi ((mem_cliqueEdges _ _).mpr heR)
    apply (card_le_card (show F.cliques.filter (fun R => e.val ⊆ R.val) ⊆
        (mapGraph (F.embedding i) (S.eliminationCliques N)).filter
          (fun R => e.val ⊆ R.val) from ?_)).trans (F.copy_count_le_two i e)
    intro T hT
    obtain ⟨hT, heT⟩ := mem_filter.mp hT
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hT
    have hej := F.clique_copy_graph j hj ((mem_cliqueEdges _ _).mpr heT)
    have hij := F.copy_index_unique hpair hei hej heB
    subst j
    exact mem_filter.mpr ⟨hj, heT⟩
  · have hzero : F.cliques.filter (fun R => e.val ⊆ R.val) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro R hR
      exact hex ⟨R, (mem_filter.mp hR).1, (mem_filter.mp hR).2⟩
    rw [hzero, card_empty]
    omega

end Arxiv2411_18291
