import Arxiv.Arxiv2411_18291.RainbowReplacementGeometry
import Arxiv.Arxiv2411_18291.RainbowAvoidingExtensions
import Arxiv.Arxiv2411_18291.RainbowPaletteUnion
import Arxiv.Arxiv2411_18291.RootColourPalette

/-!
# Rainbow properties of the replacement cliques of an arbitrary base

Choose an extension avoiding one colour for each coloured base edge.
Every near clique is rainbow after erasing its root edge, and is fully
rainbow when that root edge is coloured. Every far clique is fully rainbow.
The base itself need not have a rainbow colouring.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype W] [DecidableEq W]
variable [Fintype V] [DecidableEq V] {q r t : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} {N : Block W q}
variable {σ : I → Equiv.Perm V} {G : Hypergraph V (r + 1)}

theorem RainbowAvoidingExtensionProperties.clique_replacement_colours
    (hE : RainbowAvoidingExtensionProperties S N σ G t) (hA : IsExchangeFamily S A)
    (ht : q.choose (r + 1) ≤ t) (Q : Block V q) :
    ∃ f : W ↪ V, mapBlock f S.base = Q ∧
      (∀ P : S.nearCliques,
        IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
          ((cliqueEdges (r + 1) (mapBlock f P.val)).erase
            (mapBlock f (hA.nearRoot (Nat.succ_pos r) P)))) ∧
      (∀ P : S.nearCliques, mapBlock f (hA.nearRoot (Nat.succ_pos r) P) ∈ permutedUnion σ G →
        IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
          (cliqueEdges (r + 1) (mapBlock f P.val))) ∧
      ∀ P ∈ S.farCliques, IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
        (cliqueEdges (r + 1) (mapBlock f P)) := by
  classical
  obtain ⟨C, hC, hcol⟩ := exists_root_colour_palette σ G (cliqueEdges (r + 1) Q)
  have hCt : C.card ≤ t := by rw [card_cliqueEdges] at hC; exact hC.trans ht
  obtain ⟨f, hf, hnew⟩ := hE.clique C hCt Q
  have hnew' : IsRainbowAvoiding (fun i => mapGraph (σ i).toEmbedding G)
      (mapGraph f S.graph \ cliqueEdges (r + 1) (mapBlock f S.base)) C := by
    simpa only [hf] using hnew
  have hnear (P : S.nearCliques) :
      IsRainbowAvoiding (fun i => mapGraph (σ i).toEmbedding G)
        ((cliqueEdges (r + 1) (mapBlock f P.val)).erase
          (mapBlock f (hA.nearRoot (Nat.succ_pos r) P))) C :=
    hnew'.mono (hA.near_image_punctured_subset (Nat.succ_pos r) f P)
  refine ⟨f, hf, fun P => (hnear P).isRainbow, ?_, ?_⟩
  · intro P he
    have heQ : mapBlock f (hA.nearRoot (Nat.succ_pos r) P) ∈ cliqueEdges (r + 1) Q := by
      rw [← hf, ← map_cliqueEdges]
      exact (mem_mapGraph _ _ _).mpr
        ⟨_, hA.nearRoot_mem (Nat.succ_pos r) P, rfl⟩
    have heP : mapBlock f (hA.nearRoot (Nat.succ_pos r) P) ∈
        cliqueEdges (r + 1) (mapBlock f P.val) := by
      rw [← map_cliqueEdges]
      exact (mem_mapGraph _ _ _).mpr
        ⟨_, hA.nearRoot_mem_clique (Nat.succ_pos r) P, rfl⟩
    obtain ⟨i, hi, hei⟩ := hcol _ heQ he
    have hfull := (hnear P).insert hi hei
    rwa [insert_erase heP] at hfull
  · intro P hP
    exact (hnew'.mono (S.far_image_subset_new f hP)).isRainbow

end Arxiv2411_18291
