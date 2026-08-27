import Arxiv.Arxiv2411_18291.EliminationFamily

/-!
# Old edges in an elimination copy

Different copies meet only in the previous graph. A negative replacement
meets that graph only inside its negative root and avoids its positive
root. If it has any old edge, that edge is unique, including the exact
vertex-intersection conclusion needed by further elimination.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {I : Type*} [Fintype I] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

def EliminationFamily.positiveCliques (F : EliminationFamily S N B P Q θ) : Finset (Block V q) :=
  univ.biUnion fun i => mapGraph (F.embedding i) (S.eliminationPositive N)

def EliminationFamily.negativeCliques (F : EliminationFamily S N B P Q θ) : Finset (Block V q) :=
  univ.biUnion fun i => mapGraph (F.embedding i) S.eliminationNegative

theorem EliminationFamily.new_edges_eq (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) :
    mapGraph (F.embedding i) (newEdges (S.base.val ∪ N.val) S.graph) =
      mapGraph (F.embedding i) S.graph \ (cliqueEdges (r + 1) (P i) ∪
        cliqueEdges (r + 1) (Q i)) := by
  rw [hpair.new_edges]
  calc
    _ = mapGraph (F.embedding i) S.graph \ mapGraph (F.embedding i)
        (cliqueEdges (r + 1) S.base ∪ cliqueEdges (r + 1) N) := map_sdiff _ _
    _ = _ := by
      rw [mapGraph_union, map_cliqueEdges, map_cliqueEdges, F.positive_root, F.negative_root]

theorem EliminationFamily.copy_new_of_notMem (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) (e : Block V (r + 1))
    (he : e ∈ mapGraph (F.embedding i) S.graph) (heB : e ∉ B) :
    e ∈ mapGraph (F.embedding i) (newEdges (S.base.val ∪ N.val) S.graph) := by
  rw [F.new_edges_eq hpair i]
  exact mem_sdiff.mpr ⟨he, fun h => heB (F.root_support i h)⟩

theorem EliminationFamily.copy_inter_subset (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) {i j : I} (hij : i ≠ j) :
    mapGraph (F.embedding i) S.graph ∩ mapGraph (F.embedding j) S.graph ⊆ B := by
  intro e he
  by_contra heB
  exact disjoint_left.mp (F.disjoint hij)
    (F.copy_new_of_notMem hpair i e (mem_inter.mp he).1 heB)
    (F.copy_new_of_notMem hpair j e (mem_inter.mp he).2 heB)

theorem EliminationFamily.copy_inter_original (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) :
    mapGraph (F.embedding i) S.graph ∩ B =
      cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (Q i) := by
  apply subset_antisymm
  · intro e he
    by_contra hnot
    have hnew : e ∈ mapGraph (F.embedding i) (newEdges (S.base.val ∪ N.val) S.graph) := by
      rw [F.new_edges_eq hpair i]
      exact mem_sdiff.mpr ⟨(mem_inter.mp he).1, hnot⟩
    exact disjoint_left.mp (F.avoids i) hnew (mem_inter.mp he).2
  · intro e he
    refine mem_inter.mpr ⟨?_, F.root_support i he⟩
    rcases mem_union.mp he with hp | hq
    · rw [← F.positive_root i, ← map_cliqueEdges] at hp
      exact mapGraph_mono _ (S.positive_decomposition.clique_subset S.base_mem) hp
    · rw [← F.negative_root i, ← map_cliqueEdges] at hq
      exact mapGraph_mono _ (S.negative_decomposition.clique_subset hpair.negative_mem) hq

theorem EliminationFamily.clique_inter_original (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) (R : Block W q)
    (hR : cliqueEdges (r + 1) R ⊆ S.graph) :
    cliqueEdges (r + 1) (mapBlock (F.embedding i) R) ∩ B =
      cliqueEdges (r + 1) (mapBlock (F.embedding i) R) ∩
        (cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (Q i)) := by
  ext e
  constructor
  · intro he
    refine mem_inter.mpr ⟨(mem_inter.mp he).1, ?_⟩
    rw [← F.copy_inter_original hpair i]
    refine mem_inter.mpr ⟨?_, (mem_inter.mp he).2⟩
    exact mapGraph_mono _ hR (by rw [map_cliqueEdges]; exact (mem_inter.mp he).1)
  · intro he
    exact mem_inter.mpr ⟨(mem_inter.mp he).1, F.root_support i (mem_inter.mp he).2⟩

theorem EliminationFamily.negative_copy_disjoint_positive (F : EliminationFamily S N B P Q θ)
    (i : I) {R : Block W q} (hR : R ∈ S.eliminationNegative) :
    Disjoint (cliqueEdges (r + 1) (mapBlock (F.embedding i) R))
      (cliqueEdges (r + 1) (P i)) := by
  have hdis : Disjoint (mapGraph (F.embedding i) (cliqueEdges (r + 1) R))
      (mapGraph (F.embedding i) (cliqueEdges (r + 1) S.base)) :=
    (disjoint_map _).mpr (S.eliminationNegative_disjoint_base hR)
  simpa only [map_cliqueEdges, F.positive_root] using hdis

theorem EliminationFamily.negative_copy_inter_original (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) {R : Block W q}
    (hR : R ∈ S.eliminationNegative) :
    cliqueEdges (r + 1) (mapBlock (F.embedding i) R) ∩ B =
      cliqueEdges (r + 1) (mapBlock (F.embedding i) R) ∩ cliqueEdges (r + 1) (Q i) := by
  rw [F.clique_inter_original hpair i R
      (S.positive_decomposition.clique_subset (mem_erase.mp hR).2), inter_union_distrib_left,
    disjoint_iff_inter_eq_empty.mp (F.negative_copy_disjoint_positive i hR), empty_union]

theorem EliminationFamily.negative_copy_inter_vertices (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) {R : Block W q}
    (hR : R ∈ S.eliminationNegative) {e : Block V (r + 1)}
    (heR : e ∈ cliqueEdges (r + 1) (mapBlock (F.embedding i) R))
    (heQ : e ∈ cliqueEdges (r + 1) (Q i)) :
    (mapBlock (F.embedding i) R).val ∩ (Q i).val = e.val := by
  apply (hpair.cross_simple.map (F.embedding i)).inter_eq
    ((mem_mapGraph _ _ _).mpr ⟨R, (mem_erase.mp hR).2, rfl⟩) _ heR heQ
  exact (mem_mapGraph _ _ _).mpr ⟨N, hpair.negative_mem, F.negative_root i⟩

theorem EliminationFamily.negative_copy_original_singleton (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) {R : Block W q}
    (hR : R ∈ S.eliminationNegative)
    (hne : (cliqueEdges (r + 1) (mapBlock (F.embedding i) R) ∩ B).Nonempty) :
    ∃ e ∈ B, cliqueEdges (r + 1) (mapBlock (F.embedding i) R) ∩ B = {e} := by
  obtain ⟨e, he⟩ := hne
  have heB := (mem_inter.mp he).2
  rw [F.negative_copy_inter_original hpair i hR] at he
  refine ⟨e, heB, ?_⟩
  rw [F.negative_copy_inter_original hpair i hR]
  exact cliqueEdges_inter_singleton_of_vertices _ _ e
    (F.negative_copy_inter_vertices hpair i hR (mem_inter.mp he).1 (mem_inter.mp he).2)

end Arxiv2411_18291
