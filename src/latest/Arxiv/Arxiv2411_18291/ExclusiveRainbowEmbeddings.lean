import Arxiv.Arxiv2411_18291.RainbowCliqueCounts

/-! # Distinct clique images when each pattern edge has only its assigned colour -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {q r k : ℕ}

omit [Fintype V] [DecidableEq W] [DecidableEq V] in
theorem EmbeddingExtension.eq_of_punctured_block_images (φ : F ↪ V)
    (hk : 0 < k) (hkW : k < Fintype.card W) (f g : EmbeddingExtension φ)
    (he : ∀ e : Block W k, ¬e.val ⊆ F → mapBlock f.val e = mapBlock g.val e) : f = g := by
  classical
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  by_cases hxF : x ∈ F
  · exact (f.property ⟨x, hxF⟩).trans (g.property ⟨x, hxF⟩).symm
  · obtain ⟨s, hxs, _, hs⟩ := exists_subsuperset_card_eq
      (singleton_subset_iff.mpr (mem_univ x))
      (by simpa only [card_singleton] using Nat.succ_le_of_lt hk)
      (by simpa only [card_univ] using hkW.le)
    let e : Block W k := ⟨s, hs⟩
    have hxe : x ∈ e.val := hxs (mem_singleton_self _)
    have heF : ¬e.val ⊆ F := fun h => hxF (h hxe)
    have hximage : f.val x ∈ (mapBlock f.val e).val := mem_map.mpr ⟨x, hxe, rfl⟩
    rw [he e heF] at hximage
    obtain ⟨y, _, hy⟩ := mem_map.mp hximage
    by_cases hyx : y = x
    · simpa only [hyx] using hy.symm
    · have hsize : k ≤ ((univ : Finset W).erase y).card := by
        rw [card_erase_of_mem (mem_univ y), card_univ]
        omega
      have hsub : ({x} : Finset W) ⊆ univ.erase y :=
        singleton_subset_iff.mpr (mem_erase.mpr ⟨Ne.symm hyx, mem_univ _⟩)
      obtain ⟨t, hxt, ht, htk⟩ := exists_subsuperset_card_eq hsub
        (by simpa only [card_singleton] using Nat.succ_le_of_lt hk) hsize
      let d : Block W k := ⟨t, htk⟩
      have hxd : x ∈ d.val := hxt (mem_singleton_self _)
      have hdF : ¬d.val ⊆ F := fun h => hxF (h hxd)
      have hximage' : f.val x ∈ (mapBlock f.val d).val := mem_map.mpr ⟨x, hxd, rfl⟩
      rw [he d hdF] at hximage'
      obtain ⟨z, hz, hzg⟩ := mem_map.mp hximage'
      have hzy : z = y := g.val.injective (hzg.trans hy.symm)
      exact False.elim ((mem_erase.mp (ht (hzy ▸ hz))).1 rfl)

omit [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] in
def HasExclusiveColours (E : Hypergraph W k) (colour : E → Hypergraph V k)
    (f : W ↪ V) : Prop :=
  (∀ e : E, mapBlock f e.val ∈ colour e) ∧
    ∀ e d : E, e ≠ d → mapBlock f d.val ∉ colour e

omit [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] in
theorem HasExclusiveColours.isRainbow {E : Hypergraph W k} {colour : E → Hypergraph V k}
    {f : W ↪ V} (hf : HasExclusiveColours E colour f) : IsRainbow colour (mapGraph f E) :=
  isRainbow_mapGraph colour E f (Function.Embedding.refl E) hf.1

omit [Fintype V] [DecidableEq V] in
theorem exclusive_rooted_clique_image_injective [Finite V] (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) (hqr : r + 1 < q) (φ : F₀.val ↪ V)
    (colour : (newEdges F₀.val (complete W (r + 1))) → Hypergraph V (r + 1))
    (f g : EmbeddingExtension φ)
    (hf : HasExclusiveColours _ colour f.val) (hg : HasExclusiveColours _ colour g.val)
    (himage : embeddingClique hW f.val = embeddingClique hW g.val) : f = g := by
  classical
  let := Fintype.ofFinite V
  let E := newEdges F₀.val (complete W (r + 1))
  let root := rootImage φ F₀ Subset.rfl
  have hroot : usedVertices φ = root.val := (rootImage_self F₀ φ).symm
  have hmap : mapGraph f.val E = mapGraph g.val E := by
    rw [map_newEdges_complete_eq_erase F₀ hW φ root hroot f,
      map_newEdges_complete_eq_erase F₀ hW φ root hroot g, himage]
  apply EmbeddingExtension.eq_of_punctured_block_images φ (Nat.succ_pos r)
    (by simpa only [hW] using hqr) f g
  intro e heF
  have heE : e ∈ E := (mem_newEdges _ _).mpr ⟨mem_univ _, heF⟩
  have hge : mapBlock g.val e ∈ mapGraph f.val E := by
    rw [hmap]
    exact (mem_mapGraph _ _ _).mpr ⟨e, heE, rfl⟩
  obtain ⟨d, hdE, hd⟩ := (mem_mapGraph _ _ _).mp hge
  have hde : (⟨d, hdE⟩ : E) = ⟨e, heE⟩ := by
    by_contra hne
    have hcol : mapBlock f.val d ∈ colour ⟨e, heE⟩ := hd ▸ hg.1 ⟨e, heE⟩
    exact hf.2 ⟨e, heE⟩ ⟨d, hdE⟩ (Ne.symm hne) hcol
  have hdval : d = e := congrArg Subtype.val hde
  simpa only [hdval] using hd

open Classical in
def exclusiveColourExtensions (φ : F ↪ V) (E : Hypergraph W k)
    (σ : E → Equiv.Perm V) (G : Hypergraph V k) : Finset (EmbeddingExtension φ) :=
  univ.filter fun f => HasExclusiveColours E (fun e => mapGraph (σ e).toEmbedding G) f.val

omit [DecidableEq W] in
theorem exclusiveColourExtensions_subset_rainbow (φ : F ↪ V) (E : Hypergraph W k)
    (σ : E → Equiv.Perm V) (G : Hypergraph V k) :
    exclusiveColourExtensions φ E σ G ⊆ rainbowExtensions φ E σ G := by
  classical
  intro f hf
  exact (mem_rainbowExtensions _ _ _ _ _).mpr ((mem_filter.mp hf).2.isRainbow)

theorem exclusive_punctured_extensions_card_le (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) (hqr : r + 1 < q)
    (σ : (newEdges F₀.val (complete W (r + 1))) → Equiv.Perm V)
    (G : Hypergraph V (r + 1)) (e : Block V (r + 1)) :
    (exclusiveColourExtensions (edgeRootMap F₀ e)
      (newEdges F₀.val (complete W (r + 1))) σ G).card ≤
        (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card := by
  classical
  let T := exclusiveColourExtensions (edgeRootMap F₀ e)
    (newEdges F₀.val (complete W (r + 1))) σ G
  have hinj : Set.InjOn (fun f : EmbeddingExtension (edgeRootMap F₀ e) =>
      embeddingClique hW f.val) (T : Set (EmbeddingExtension (edgeRootMap F₀ e))) := by
    intro f hf g hg hfg
    exact exclusive_rooted_clique_image_injective F₀ hW hqr (edgeRootMap F₀ e)
      (fun i => mapGraph (σ i).toEmbedding G) f g (mem_filter.mp hf).2 (mem_filter.mp hg).2 hfg
  calc
    _ = (T.image (fun f => embeddingClique hW f.val)).card := (card_image_of_injOn hinj).symm
    _ ≤ ((rainbowExtensions (edgeRootMap F₀ e)
        (newEdges F₀.val (complete W (r + 1))) σ G).image
          (fun f => embeddingClique hW f.val)).card :=
      card_le_card (image_subset_image (exclusiveColourExtensions_subset_rainbow _ _ _ _))
    _ ≤ _ := card_le_card (rainbow_clique_image_subset F₀ hW σ G e)

end Arxiv2411_18291
