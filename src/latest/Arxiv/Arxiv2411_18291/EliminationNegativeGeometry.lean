import Arxiv.Arxiv2411_18291.EliminationCopyGeometry

/-!
# Good and bad negative elimination cliques

Good cliques avoid the previous graph and are edge-disjoint from all
other negative cliques. Bad cliques meet the previous graph in one edge.
The root-intersection criterion below proves full edge disjointness for
the further elimination stage once its positive partners are supplied.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {I : Type*} [Fintype I] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

theorem EliminationFamily.negative_copy_graph (F : EliminationFamily S N B P Q θ)
    (i : I) {R : Block W q} (hR : R ∈ S.eliminationNegative) :
    cliqueEdges (r + 1) (mapBlock (F.embedding i) R) ⊆ mapGraph (F.embedding i) S.graph := by
  rw [← map_cliqueEdges]
  exact mapGraph_mono _ (S.positive_decomposition.clique_subset (mem_erase.mp hR).2)

theorem EliminationFamily.negative_same_copy_disjoint (F : EliminationFamily S N B P Q θ)
    (i : I) {R T : Block W q} (hR : R ∈ S.eliminationNegative) (hT : T ∈ S.eliminationNegative)
    (hRT : mapBlock (F.embedding i) R ≠ mapBlock (F.embedding i) T) :
    Disjoint (cliqueEdges (r + 1) (mapBlock (F.embedding i) R))
      (cliqueEdges (r + 1) (mapBlock (F.embedding i) T)) :=
  (S.positive_decomposition.map (F.embedding i)).cliques_disjoint
    ((mem_mapGraph _ _ _).mpr ⟨R, (mem_erase.mp hR).2, rfl⟩)
    ((mem_mapGraph _ _ _).mpr ⟨T, (mem_erase.mp hT).2, rfl⟩) hRT

theorem EliminationFamily.negative_inter_subset_original (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {R T : Block V q}
    (hR : R ∈ F.negativeCliques) (hT : T ∈ F.negativeCliques) (hRT : R ≠ T) :
    cliqueEdges (r + 1) R ∩ cliqueEdges (r + 1) T ⊆ B := by
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp hT
  obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hi
  obtain ⟨T₀, hT₀, rfl⟩ := (mem_mapGraph _ _ _).mp hj
  intro e he
  by_cases hij : i = j
  · subst j
    exact (disjoint_left.mp (F.negative_same_copy_disjoint i hR₀ hT₀ hRT)
      (mem_inter.mp he).1 (mem_inter.mp he).2).elim
  · exact F.copy_inter_subset hpair hij (mem_inter.mpr
      ⟨F.negative_copy_graph i hR₀ (mem_inter.mp he).1,
        F.negative_copy_graph j hT₀ (mem_inter.mp he).2⟩)

theorem EliminationFamily.negative_disjoint_of_avoids (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {R T : Block V q}
    (hR : R ∈ F.negativeCliques) (hT : T ∈ F.negativeCliques) (hRT : R ≠ T)
    (havoid : Disjoint (cliqueEdges (r + 1) R) B) :
    Disjoint (cliqueEdges (r + 1) R) (cliqueEdges (r + 1) T) := by
  apply disjoint_left.mpr
  intro e heR heT
  exact disjoint_left.mp havoid heR
    (F.negative_inter_subset_original hpair hR hT hRT (mem_inter.mpr ⟨heR, heT⟩))

def EliminationFamily.goodNegative (F : EliminationFamily S N B P Q θ) : Finset (Block V q) :=
  F.negativeCliques.filter fun R => Disjoint (cliqueEdges (r + 1) R) B

def EliminationFamily.badNegative (F : EliminationFamily S N B P Q θ) : Finset (Block V q) :=
  F.negativeCliques \ F.goodNegative

theorem EliminationFamily.goodNegative_disjoint (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {R T : Block V q}
    (hR : R ∈ F.goodNegative) (hT : T ∈ F.negativeCliques) (hRT : R ≠ T) :
    Disjoint (cliqueEdges (r + 1) R) (cliqueEdges (r + 1) T) :=
  F.negative_disjoint_of_avoids hpair (mem_filter.mp hR).1 hT hRT (mem_filter.mp hR).2

theorem EliminationFamily.badNegative_inter_singleton (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {R : Block V q} (hR : R ∈ F.badNegative) :
    ∃ e ∈ B, cliqueEdges (r + 1) R ∩ B = {e} := by
  obtain ⟨hR, hnot⟩ := mem_sdiff.mp hR
  have hne : (cliqueEdges (r + 1) R ∩ B).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro hz
    exact hnot (mem_filter.mpr ⟨hR, disjoint_iff_inter_eq_empty.mpr hz⟩)
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
  obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hi
  exact F.negative_copy_original_singleton hpair i hR₀ hne

theorem EliminationFamily.negative_disjoint_previous (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {H : Hypergraph V (r + 1)} (hH : H ⊆ B)
    (hroot : ∀ i, cliqueEdges (r + 1) (Q i) ∩ H ⊆ cliqueEdges (r + 1) (P i))
    {R : Block V q} (hR : R ∈ F.negativeCliques) : Disjoint (cliqueEdges (r + 1) R) H := by
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
  obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hi
  apply disjoint_left.mpr
  intro e heR heH
  have heI := mem_inter.mpr ⟨heR, hH heH⟩
  rw [F.negative_copy_inter_original hpair i hR₀] at heI
  exact disjoint_left.mp (F.negative_copy_disjoint_positive i hR₀) heR
    (hroot i (mem_inter.mpr ⟨(mem_inter.mp heI).2, heH⟩))

theorem EliminationFamily.negative_pairwise_of_root_inter (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀)
    (hroot : ∀ i j, i ≠ j → cliqueEdges (r + 1) (Q i) ∩ cliqueEdges (r + 1) (Q j) ⊆
      cliqueEdges (r + 1) (P i)) :
    (F.negativeCliques : Set (Block V q)).Pairwise
      (fun R T => Disjoint (cliqueEdges (r + 1) R) (cliqueEdges (r + 1) T)) := by
  intro R hR T hT hRT
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hR
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp hT
  obtain ⟨R₀, hR₀, rfl⟩ := (mem_mapGraph _ _ _).mp hi
  obtain ⟨T₀, hT₀, rfl⟩ := (mem_mapGraph _ _ _).mp hj
  by_cases hij : i = j
  · subst j
    exact F.negative_same_copy_disjoint i hR₀ hT₀ hRT
  · apply disjoint_left.mpr
    intro e heR heT
    have heB := F.copy_inter_subset hpair hij (mem_inter.mpr
      ⟨F.negative_copy_graph i hR₀ heR, F.negative_copy_graph j hT₀ heT⟩)
    have heI := mem_inter.mpr ⟨heR, heB⟩
    have heJ := mem_inter.mpr ⟨heT, heB⟩
    rw [F.negative_copy_inter_original hpair i hR₀] at heI
    rw [F.negative_copy_inter_original hpair j hT₀] at heJ
    exact disjoint_left.mp (F.negative_copy_disjoint_positive i hR₀) heR
      (hroot i j hij (mem_inter.mpr ⟨(mem_inter.mp heI).2, (mem_inter.mp heJ).2⟩))

end Arxiv2411_18291
