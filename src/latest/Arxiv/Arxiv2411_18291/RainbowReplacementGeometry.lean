import Arxiv.Arxiv2411_18291.ExchangeFrameStructure
import Arxiv.Arxiv2411_18291.RainbowExchangePlacements

/-!
# Replacement cliques inside the rainbow extension graph

A near clique has exactly its distinguished root edge in the base.
A far clique has no base edge. The corresponding subset statements
are preserved by every vertex embedding.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q r} {A : Finset (Block W q)}

omit [Fintype V] [DecidableEq V] in
theorem IsExchangeFamily.nearRoot_mem_clique (hA : IsExchangeFamily S A) (hr : 0 < r)
    (P : S.nearCliques) : hA.nearRoot hr P ∈ cliqueEdges r P.val :=
  (mem_cliqueEdges _ _).mpr inter_subset_left

omit [Fintype V] [DecidableEq V] in
theorem IsExchangeFamily.near_punctured_subset (hA : IsExchangeFamily S A) (hr : 0 < r)
    (P : S.nearCliques) :
    (cliqueEdges r P.val).erase (hA.nearRoot hr P) ⊆ S.graph \ cliqueEdges r S.base := by
  intro e he
  obtain ⟨hne, heP⟩ := mem_erase.mp he
  refine mem_sdiff.mpr ⟨S.replacement_clique_subset (mem_filter.mp P.property).1 heP, ?_⟩
  intro heB
  have hinter : e ∈ cliqueEdges r P.val ∩ cliqueEdges r S.base := mem_inter.mpr ⟨heP, heB⟩
  rw [hA.nearRoot_inter hr P] at hinter
  exact hne (mem_singleton.mp hinter)

omit [Fintype V] [DecidableEq V] in
theorem ExchangeSystem.far_subset_new (S : ExchangeSystem W q r)
    {P : Block W q} (hP : P ∈ S.farCliques) :
    cliqueEdges r P ⊆ S.graph \ cliqueEdges r S.base := by
  intro e he
  exact mem_sdiff.mpr ⟨S.replacement_clique_subset (mem_sdiff.mp hP).1 he,
    fun heB => disjoint_left.mp (S.far_disjoint_base hP) he heB⟩

theorem IsExchangeFamily.near_image_punctured_subset (hA : IsExchangeFamily S A)
    (hr : 0 < r) (f : W ↪ V) (P : S.nearCliques) :
    (cliqueEdges r (mapBlock f P.val)).erase (mapBlock f (hA.nearRoot hr P)) ⊆
      mapGraph f S.graph \ cliqueEdges r (mapBlock f S.base) := by
  simpa only [mapGraph_erase, mapGraph_sdiff, map_cliqueEdges] using
    mapGraph_mono f (hA.near_punctured_subset hr P)

theorem ExchangeSystem.far_image_subset_new (S : ExchangeSystem W q r)
    (f : W ↪ V) {P : Block W q} (hP : P ∈ S.farCliques) :
    cliqueEdges r (mapBlock f P) ⊆ mapGraph f S.graph \ cliqueEdges r (mapBlock f S.base) := by
  simpa only [mapGraph_sdiff, map_cliqueEdges] using mapGraph_mono f (S.far_subset_new hP)

end Arxiv2411_18291
