import Arxiv.Arxiv2411_18291.RainbowEliminationGeneration
import Arxiv.Arxiv2411_18291.RainbowAvoidingExtensions

/-!
# Generating a pair whose punctured roots are jointly rainbow

At most twice the clique edge count colours its two punctured roots.
The pair extension avoids those labels, so every elimination replacement
is rainbow. The integer exchange identity generates the root difference.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r t : ℕ} {S : ExchangeSystem W q (r + 1)} {N : Block W q}
variable {σ : I → Equiv.Perm V} {G : Hypergraph V (r + 1)}

theorem RainbowAvoidingExtensionProperties.pair_generated
    (hE : RainbowAvoidingExtensionProperties S N σ G t) (hN : N ∈ S.negative)
    (ht : 2 * q.choose (r + 1) ≤ t) (P Q : Block V q) (e : Block V (r + 1))
    (hPQ : P.val ∩ Q.val = e.val)
    (hroot : IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
      ((cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q).erase e)) :
    GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q)
      (indicator (cliqueEdges (r + 1) P) - indicator (cliqueEdges (r + 1) Q)) := by
  classical
  let R := cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q
  obtain ⟨c, hc⟩ := hroot
  let B := univ.image c
  have hR : (R.erase e).card ≤ 2 * q.choose (r + 1) := by
    calc
      _ ≤ R.card := card_le_card (erase_subset _ _)
      _ ≤ (cliqueEdges (r + 1) P).card + (cliqueEdges (r + 1) Q).card := card_union_le _ _
      _ = _ := by rw [card_cliqueEdges, card_cliqueEdges]; omega
  have hB : B.card ≤ t := by
    have himage : B.card ≤ (univ : Finset ↥(R.erase e)).card := card_image_le
    rw [card_univ, Fintype.card_coe] at himage
    exact (himage.trans hR).trans ht
  obtain ⟨f, hfP, hfQ, hnew⟩ := hE.pair B hB P Q e hPQ
  have hwhole := hnew.fill_root (mapGraph f S.graph) R e c hc
    (fun x => mem_image.mpr ⟨x, mem_univ _, rfl⟩)
  have hN' : mapBlock f N ∈ (S.map f).negative :=
    (mem_mapGraph f S.negative _).mpr ⟨N, hN, rfl⟩
  have heP : e ∈ cliqueEdges (r + 1) (S.map f).base := by
    change e ∈ cliqueEdges (r + 1) (mapBlock f S.base)
    rw [hfP, mem_cliqueEdges, ← hPQ]
    exact inter_subset_left
  have heQ : e ∈ cliqueEdges (r + 1) (mapBlock f N) := by
    rw [hfQ, mem_cliqueEdges, ← hPQ]
    exact inter_subset_right
  have hgen := (S.map f).rainbow_elimination_generated hN' e heP heQ
    (fun i => mapGraph (σ i).toEmbedding G) hwhole
  change GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q)
    (indicator (cliqueEdges (r + 1) (mapBlock f S.base)) -
      indicator (cliqueEdges (r + 1) (mapBlock f N))) at hgen
  rw [hfP, hfQ] at hgen
  exact hgen

end Arxiv2411_18291
