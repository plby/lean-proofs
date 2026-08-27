import Arxiv.Arxiv2411_18291.ModularSupport
import Arxiv.Arxiv2411_18291.RainbowIntegralGeneration

/-!
# The colour graph lies in the generator support

Extend a coloured edge to a punctured rainbow clique avoiding its colour,
then insert the root edge. Modular generation of this full rainbow clique
forces the root edge into the support of the modular generators.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype W] [DecidableEq W]
variable [Fintype V] [DecidableEq V] {q r t : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {P : Block W q}
variable {σ : I → Equiv.Perm V} {G : Hypergraph V (r + 1)}

theorem RainbowAvoidingExtensionProperties.exists_rainbow_clique
    (hE : RainbowAvoidingExtensionProperties S P σ G t) (ht : 1 ≤ t)
    {e : Block V (r + 1)} (he : e ∈ permutedUnion σ G) :
    ∃ Q : Block V q, e ∈ cliqueEdges (r + 1) Q ∧
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) (cliqueEdges (r + 1) Q) := by
  classical
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
  obtain ⟨Q, heQ, hQ⟩ :=
    hE.exists_punctured_clique {i} (by simpa only [card_singleton] using ht) e
  have heQ' : e ∈ cliqueEdges (r + 1) Q := (mem_cliqueEdges _ _).mpr heQ
  refine ⟨Q, heQ', ?_⟩
  simpa only [insert_erase heQ'] using hQ.insert (mem_singleton_self i) hi

theorem RainbowAvoidingExtensionProperties.colour_subset_generator_support
    (hE : RainbowAvoidingExtensionProperties S P σ G t) (ht : 1 ≤ t)
    (N : ℕ) [Nontrivial (ZMod N)] (D : Finset (Block V q))
    (hgen : ∀ Q : Block V q,
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) (cliqueEdges (r + 1) Q) →
      modularCliqueVector N (r + 1) Q ∈ generatedSubgroup (modularCliqueVector N (r + 1)) D) :
    permutedUnion σ G ⊆ cliqueSupport (r + 1) D := by
  intro e he
  obtain ⟨Q, heQ, hQ⟩ := hE.exists_rainbow_clique ht he
  exact cliqueEdges_subset_support_of_modular_generated D Q (hgen Q hQ) heQ

end Arxiv2411_18291
