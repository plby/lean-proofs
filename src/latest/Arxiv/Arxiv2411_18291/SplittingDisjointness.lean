import Arxiv.Arxiv2411_18291.ExchangeReplacement
import Arxiv.Arxiv2411_18291.CliqueRefinement

/-!
# Distinct replacement cliques from different exchange copies

Every replacement clique contains a new edge. If it appeared in two
copies, that edge would have to be new in both: the other copy's root
edges belong to the forbidden graph. The greedy disjointness invariant
therefore prevents repeated replacement cliques. It also keeps the
replacement family disjoint from the original clique family.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r t : ℕ}

theorem replacement_copy_new_edge (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 ≤ q)
    (f : W ↪ V) {P : Block V q} (hP : P ∈ (S.map f).replacementCliques) :
    ∃ e ∈ cliqueEdges (r + 1) P, e ∈ mapGraph f (newEdges S.base.val S.graph) := by
  rw [ExchangeSystem.replacementCliques_map] at hP
  obtain ⟨P₀, hP₀, rfl⟩ := (mem_mapGraph f S.replacementCliques P).mp hP
  obtain ⟨e, heP, henew⟩ := S.replacement_new_edge hqr hP₀
  refine ⟨mapBlock f e, ?_, (mem_mapGraph _ _ _).mpr ⟨e, henew, rfl⟩⟩
  rw [← map_cliqueEdges]
  exact (mem_mapGraph _ _ _).mpr ⟨e, heP, rfl⟩

theorem replacement_copies_disjoint (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 ≤ q)
    (f g : W ↪ V) (B : Hypergraph V (r + 1))
    (hf : Disjoint (mapGraph f (newEdges S.base.val S.graph)) B)
    (hgroot : cliqueEdges (r + 1) (mapBlock g S.base) ⊆ B)
    (hfg : Disjoint (mapGraph f (newEdges S.base.val S.graph))
      (mapGraph g (newEdges S.base.val S.graph))) :
    Disjoint (S.map f).replacementCliques (S.map g).replacementCliques := by
  apply disjoint_left.mpr
  intro P hPf hPg
  obtain ⟨e, heP, hef⟩ := replacement_copy_new_edge S hqr f hPf
  have heB : e ∉ B := fun h => disjoint_left.mp hf hef h
  have heg : e ∈ mapGraph g S.graph := (S.map g).replacement_clique_subset hPg heP
  obtain ⟨e₀, he₀, heq⟩ := (mem_mapGraph g S.graph e).mp heg
  have hnot : ¬e₀.val ⊆ S.base.val := by
    intro h
    have hroot : mapBlock g e₀ ∈ cliqueEdges (r + 1) (mapBlock g S.base) :=
      (mem_cliqueEdges _ _).mpr (map_subset_map.mpr h)
    exact heB (heq ▸ hgroot hroot)
  have henew : e ∈ mapGraph g (newEdges S.base.val S.graph) :=
    (mem_mapGraph _ _ _).mpr ⟨e₀, (mem_newEdges S.graph e₀).mpr ⟨he₀, hnot⟩, heq⟩
  exact disjoint_left.mp hfg hef henew

theorem replacement_copy_disjoint_original (S : ExchangeSystem W q (r + 1))
    (hqr : r + 1 ≤ q) (f : W ↪ V) (B : Hypergraph V (r + 1))
    (D : Finset (Block V q)) (hD : cliqueSupport (r + 1) D ⊆ B)
    (hf : Disjoint (mapGraph f (newEdges S.base.val S.graph)) B) :
    Disjoint (S.map f).replacementCliques D := by
  apply disjoint_left.mpr
  intro P hP hPD
  obtain ⟨e, heP, henew⟩ := replacement_copy_new_edge S hqr f hP
  exact disjoint_left.mp hf henew (hD (mem_biUnion.mpr ⟨P, hPD, heP⟩))

theorem IsGreedyFamily.replacement_families_disjoint (S : ExchangeSystem W q (r + 1))
    (hqr : r + 1 ≤ q) {Φ : Fin t → S.base.val ↪ V} {B : Hypergraph V (r + 1)}
    {Ψ : (i : Fin t) → EmbeddingExtension (Φ i)} {L : ℝ}
    (hΨ : IsGreedyFamily Φ S.graph B Ψ L)
    (hrootB : ∀ i, cliqueEdges (r + 1) (mapBlock (Ψ i).val S.base) ⊆ B) :
    Pairwise fun i j => Disjoint (S.map (Ψ i).val).replacementCliques
      (S.map (Ψ j).val).replacementCliques := by
  intro i j hij
  exact replacement_copies_disjoint S hqr (Ψ i).val (Ψ j).val B
    (hΨ.avoids i) (hrootB j) (hΨ.disjoint hij)

end Arxiv2411_18291
