import Arxiv.Arxiv2411_18291.IntegralGenerationTransitivity
import Arxiv.Arxiv2411_18291.SplittingMultiplicity
import Arxiv.Arxiv2411_18291.CliqueSupportBounds

/-!
# Exchange placements for splitting an arbitrary generating family

One exchange is rooted at each generator. New edges avoid the old support
and all other copies. This stage needs no bound on the original edge
multiplicities and no separation of private vertices between copies.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r : ℕ}

structure GeneratorSplitting (S : ExchangeSystem W q (r + 1))
    (D : Finset (Block V q)) (θ : ℝ) where
  embedding : D → W ↪ V
  base : ∀ Q, mapBlock (embedding Q) S.base = Q.val
  avoids : ∀ Q, Disjoint (mapGraph (embedding Q) (newEdges S.base.val S.graph))
    (cliqueSupport (r + 1) D)
  disjoint : Pairwise fun P Q => Disjoint
    (mapGraph (embedding P) (newEdges S.base.val S.graph))
    (mapGraph (embedding Q) (newEdges S.base.val S.graph))
  bounded : IsGraphBounded (cliqueSupport (r + 1) D ∪
    univ.biUnion fun Q => mapGraph (embedding Q) (newEdges S.base.val S.graph)) θ

variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)} {θ : ℝ}

def GeneratorSplitting.cliques (F : GeneratorSplitting S D θ) : Finset (Block V q) :=
  univ.biUnion fun Q : D => (S.map (F.embedding Q)).replacementCliques

def GeneratorSplitting.graph (F : GeneratorSplitting S D θ) : Hypergraph V (r + 1) :=
  cliqueSupport (r + 1) D ∪
    univ.biUnion fun Q => mapGraph (F.embedding Q) (newEdges S.base.val S.graph)

theorem GeneratorSplitting.generated_clique (F : GeneratorSplitting S D θ) (Q : D) :
    GeneratedBy F.cliques (indicator (cliqueEdges (r + 1) Q.val)) := by
  rw [← F.base Q]
  exact (S.map (F.embedding Q)).generatedBy_replacement.mono
    (fun P hP => mem_biUnion.mpr ⟨Q, mem_univ _, hP⟩)

theorem GeneratorSplitting.generated (F : GeneratorSplitting S D θ)
    {J : Block V (r + 1) → ℤ} (hJ : GeneratedBy D J) : GeneratedBy F.cliques J :=
  hJ.trans (fun Q hQ => F.generated_clique ⟨Q, hQ⟩)

theorem GeneratorSplitting.root_edges_subset (F : GeneratorSplitting S D θ) (Q : D) :
    cliqueEdges (r + 1) (mapBlock (F.embedding Q) S.base) ⊆ cliqueSupport (r + 1) D := by
  rw [F.base Q]
  exact fun e he => mem_biUnion.mpr ⟨Q.val, Q.property, he⟩

theorem GeneratorSplitting.copy_new_of_notMem (F : GeneratorSplitting S D θ) (Q : D)
    {e : Block V (r + 1)} (he : e ∈ mapGraph (F.embedding Q) S.graph)
    (heD : e ∉ cliqueSupport (r + 1) D) :
    e ∈ mapGraph (F.embedding Q) (newEdges S.base.val S.graph) := by
  obtain ⟨e₀, he₀, rfl⟩ := (mem_mapGraph _ _ _).mp he
  have hn : ¬e₀.val ⊆ S.base.val := by
    intro h
    exact heD (F.root_edges_subset Q ((mem_cliqueEdges _ _).mpr (map_subset_map.mpr h)))
  exact (mem_mapGraph _ _ _).mpr ⟨e₀, (mem_newEdges S.graph e₀).mpr ⟨he₀, hn⟩, rfl⟩

theorem GeneratorSplitting.copy_index_unique (F : GeneratorSplitting S D θ)
    {P Q : D} {e : Block V (r + 1)} (heP : e ∈ mapGraph (F.embedding P) S.graph)
    (heQ : e ∈ mapGraph (F.embedding Q) S.graph) (heD : e ∉ cliqueSupport (r + 1) D) : P = Q := by
  by_contra hne
  exact disjoint_left.mp (F.disjoint hne)
    (F.copy_new_of_notMem P heP heD) (F.copy_new_of_notMem Q heQ heD)

theorem GeneratorSplitting.cliques_support (F : GeneratorSplitting S D θ) :
    cliqueSupport (r + 1) F.cliques ⊆ F.graph := by
  intro e he
  obtain ⟨P, hP, heP⟩ := mem_biUnion.mp he
  obtain ⟨Q, _, hQ⟩ := mem_biUnion.mp hP
  by_cases heD : e ∈ cliqueSupport (r + 1) D
  · exact mem_union_left _ heD
  · exact mem_union_right _ (mem_biUnion.mpr ⟨Q, mem_univ _,
      F.copy_new_of_notMem Q ((S.map (F.embedding Q)).replacement_clique_subset hQ heP) heD⟩)

theorem GeneratorSplitting.copy_clique_inter (F : GeneratorSplitting S D θ)
    (Q : D) (P : Block W q) (hP : cliqueEdges (r + 1) P ⊆ S.graph) :
    cliqueEdges (r + 1) (mapBlock (F.embedding Q) P) ∩ cliqueSupport (r + 1) D =
      mapGraph (F.embedding Q) (cliqueEdges (r + 1) P ∩ cliqueEdges (r + 1) S.base) := by
  rw [mapGraph_inter, map_cliqueEdges, map_cliqueEdges]
  ext e
  simp only [mem_inter]
  apply and_congr_right
  intro heP
  constructor
  · intro heD
    have heMap : e ∈ mapGraph (F.embedding Q) (cliqueEdges (r + 1) P) := by
      rwa [map_cliqueEdges]
    obtain ⟨e₀, he₀, rfl⟩ := (mem_mapGraph _ _ _).mp heMap
    have heRoot : e₀.val ⊆ S.base.val := by
      by_contra hnot
      exact disjoint_left.mp (F.avoids Q)
        ((mem_mapGraph _ _ _).mpr ⟨e₀, (mem_newEdges S.graph e₀).mpr ⟨hP he₀, hnot⟩, rfl⟩) heD
    exact (mem_cliqueEdges _ _).mpr (map_subset_map.mpr heRoot)
  · intro he
    exact F.root_edges_subset Q he

end Arxiv2411_18291
