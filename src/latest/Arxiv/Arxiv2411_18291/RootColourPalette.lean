import Arxiv.Arxiv2411_18291.ColouredGenerators

/-!
# A bounded palette for the coloured edges of a root

Choose one label for each root edge which lies in the union of the colour
graphs. The labels need not be distinct: their total number is bounded by
the root edge count, and each near clique uses only one root edge.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [DecidableEq V] {r : ℕ}

theorem exists_root_colour_palette (σ : I → Equiv.Perm V) (G H : Hypergraph V r) :
    ∃ C : Finset I, C.card ≤ H.card ∧ ∀ e ∈ H, e ∈ permutedUnion σ G →
      ∃ i ∈ C, e ∈ mapGraph (σ i).toEmbedding G := by
  classical
  let E := H ∩ permutedUnion σ G
  have hex (e : E) : ∃ i : I, e.val ∈ mapGraph (σ i).toEmbedding G := by
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp (mem_inter.mp e.property).2
    exact ⟨i, hi⟩
  choose c hc using hex
  refine ⟨univ.image c, ?_, fun e heH heG => ?_⟩
  · calc
      _ ≤ (univ : Finset E).card := card_image_le
      _ = E.card := by rw [card_univ, Fintype.card_coe]
      _ ≤ H.card := card_le_card inter_subset_left
  · let x : E := ⟨e, mem_inter.mpr ⟨heH, heG⟩⟩
    exact ⟨c x, mem_image.mpr ⟨x, mem_univ _, rfl⟩, hc x⟩

end Arxiv2411_18291
