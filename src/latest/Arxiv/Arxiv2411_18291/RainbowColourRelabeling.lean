import Arxiv.Arxiv2411_18291.RainbowCliqueCounts

/-!
# Preserving rainbow witnesses when adding or renaming colours

Injectively embedding the old colour indices preserves every previous
rainbow witness. The same implication holds for the finite extension and
punctured-clique families, so their lower bounds are preserved as well.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I J W V : Type*} {q r : ℕ}

theorem IsRainbow.reindex {colour : I → Hypergraph V r} {colour' : J → Hypergraph V r}
    {H : Hypergraph V r} (hH : IsRainbow colour H) (e : I ↪ J)
    (hcolour : ∀ i, colour i ⊆ colour' (e i)) : IsRainbow colour' H := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨c.trans e, fun f => hcolour (c f) (hc f)⟩

theorem IsRainbow.permutation_reindex {σ : I → Equiv.Perm V} {τ : J → Equiv.Perm V}
    {G H : Hypergraph V r} (hH : IsRainbow (fun i => mapGraph (σ i).toEmbedding G) H)
    (e : I ↪ J) (he : ∀ i, τ (e i) = σ i) :
    IsRainbow (fun j => mapGraph (τ j).toEmbedding G) H := by
  apply hH.reindex e
  intro i
  rw [he i]

variable [Fintype V] [DecidableEq V]

theorem rainbowPuncturedCliques_subset_reindex (σ : I → Equiv.Perm V)
    (τ : J → Equiv.Perm V) (G : Hypergraph V (r + 1)) (e : I ↪ J)
    (he : ∀ i, τ (e i) = σ i) (d : Block V (r + 1)) :
    rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) d q ⊆
      rainbowPuncturedCliques (fun j => mapGraph (τ j).toEmbedding G) d q := by
  classical
  intro Q hQ
  obtain ⟨_, hroot, hcol⟩ := mem_filter.mp hQ
  exact mem_filter.mpr ⟨mem_univ _, hroot, hcol.permutation_reindex e he⟩

variable [Fintype W] {F : Finset W}

theorem rainbowExtensions_subset_reindex (φ : F ↪ V) (E : Hypergraph W r)
    (σ : I → Equiv.Perm V) (τ : J → Equiv.Perm V) (G : Hypergraph V r) (e : I ↪ J)
    (he : ∀ i, τ (e i) = σ i) : rainbowExtensions φ E σ G ⊆ rainbowExtensions φ E τ G := by
  intro f hf
  exact (mem_rainbowExtensions _ _ _ _ _).mpr
    (((mem_rainbowExtensions _ _ _ _ _).mp hf).permutation_reindex e he)

end Arxiv2411_18291
