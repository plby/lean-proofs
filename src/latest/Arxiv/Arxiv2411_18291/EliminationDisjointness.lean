import Arxiv.Arxiv2411_18291.EliminationSupport

/-!
# Elimination cliques have no repeated occurrence

Every replacement contains a new edge, so it cannot also be a previous
clique or occur in another exchange copy. Together with the disjoint
signs inside each exchange, this permits selected replacements to be
represented by sets with coefficients in `{-1,0,1}`.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {N : Block W q}
variable {e₀ : Block W (r + 1)}

theorem IsEliminationPair.elimination_new_edge (hpair : IsEliminationPair S N e₀)
    (hqr : r + 1 ≤ q) {R : Block W q} (hR : R ∈ S.eliminationCliques N) :
    ∃ e ∈ cliqueEdges (r + 1) R, e ∈ newEdges (S.base.val ∪ N.val) S.graph := by
  by_contra hnone
  have hgraph := S.elimination_clique_subset N hR
  have hroot (e : Block W (r + 1)) (he : e ∈ cliqueEdges (r + 1) R) :
      e.val ⊆ S.base.val ∪ N.val := by
    by_contra hnot
    exact hnone ⟨e, he, (mem_newEdges S.graph e).mpr ⟨hgraph he, hnot⟩⟩
  rcases mem_union.mp hR with hp | hn
  · have hsub : cliqueEdges (r + 1) R ⊆ cliqueEdges (r + 1) S.base := by
      intro e he
      rcases hpair.root_edge_cases (hgraph he) (hroot e he) with hb | hN
      · exact (mem_cliqueEdges _ _).mpr hb
      · exact (disjoint_left.mp (S.eliminationPositive_disjoint_negative hpair.negative_mem hp)
          he ((mem_cliqueEdges _ _).mpr hN)).elim
    have hRbase : R = S.base := Subtype.ext (eq_of_subset_of_card_le
      (clique_vertices_subset (Nat.succ_pos r) hqr R S.base hsub)
      (by rw [R.property, S.base.property]))
    exact disjoint_left.mp S.disjoint (hRbase ▸ S.base_mem) (mem_erase.mp hp).2
  · have hsub : cliqueEdges (r + 1) R ⊆ cliqueEdges (r + 1) N := by
      intro e he
      rcases hpair.root_edge_cases (hgraph he) (hroot e he) with hb | hN
      · exact (disjoint_left.mp (S.eliminationNegative_disjoint_base hn)
          he ((mem_cliqueEdges _ _).mpr hb)).elim
      · exact (mem_cliqueEdges _ _).mpr hN
    have hRN : R = N := Subtype.ext (eq_of_subset_of_card_le
      (clique_vertices_subset (Nat.succ_pos r) hqr R N hsub)
      (by rw [R.property, N.property]))
    exact disjoint_left.mp S.disjoint (mem_erase.mp hn).2 (hRN ▸ hpair.negative_mem)

variable {I : Type*} [Fintype I] {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

theorem EliminationFamily.copy_new_edge (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (hqr : r + 1 ≤ q) (i : I)
    {R : Block V q} (hR : R ∈ mapGraph (F.embedding i) (S.eliminationCliques N)) :
    ∃ e ∈ cliqueEdges (r + 1) R,
      e ∈ mapGraph (F.embedding i) (newEdges (S.base.val ∪ N.val) S.graph) := by
  obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hR
  obtain ⟨e, heR, heNew⟩ := hpair.elimination_new_edge hqr hR₀
  refine ⟨mapBlock (F.embedding i) e, ?_, (mem_mapGraph _ _ _).mpr ⟨e, heNew, rfl⟩⟩
  rw [← map_cliqueEdges]
  exact (mem_mapGraph _ _ _).mpr ⟨e, heR, rfl⟩

theorem EliminationFamily.copies_disjoint (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (hqr : r + 1 ≤ q) :
    Pairwise fun i j => Disjoint (mapGraph (F.embedding i) (S.eliminationCliques N))
      (mapGraph (F.embedding j) (S.eliminationCliques N)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro R hRi hRj
  obtain ⟨e, heR, heNew⟩ := F.copy_new_edge hpair hqr i hRi
  have heB : e ∉ B := fun h => disjoint_left.mp (F.avoids i) heNew h
  exact disjoint_left.mp (F.disjoint hij) heNew
    (F.copy_new_of_notMem hpair j e (F.clique_copy_graph j hRj heR) heB)

theorem EliminationFamily.cliques_disjoint_previous (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (hqr : r + 1 ≤ q) (D : Finset (Block V q))
    (hsupport : cliqueSupport (r + 1) D ⊆ B) : Disjoint F.cliques D := by
  apply disjoint_left.mpr
  intro R hR hD
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
  obtain ⟨e, heR, heNew⟩ := F.copy_new_edge hpair hqr i hi
  exact disjoint_left.mp (F.avoids i) heNew (hsupport (mem_biUnion.mpr ⟨R, hD, heR⟩))

theorem EliminationFamily.signs_disjoint (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (hqr : r + 1 ≤ q) :
    Disjoint F.positiveCliques F.negativeCliques := by
  apply disjoint_left.mpr
  intro R hRp hRn
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hRp
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp hRn
  by_cases hij : i = j
  · subst j
    exact disjoint_left.mp ((disjoint_map _).mpr (S.elimination_signs_disjoint N)) hi hj
  · exact disjoint_left.mp (F.copies_disjoint hpair hqr hij)
      (mapGraph_mono _ subset_union_left hi) (mapGraph_mono _ subset_union_right hj)

end Arxiv2411_18291
