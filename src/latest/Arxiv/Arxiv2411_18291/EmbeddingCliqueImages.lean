import Arxiv.Arxiv2411_18291.GreedyRootCompatibility
import Arxiv.Arxiv2411_18291.PuncturedClique

/-!
# Clique images of root-preserving embeddings

Every clique of the pattern size containing the prescribed root image is
the image of an extension. Thus a lower bound on punctured cliques gives
a lower bound on candidate embeddings, without mistaking vertex orderings
for distinct cliques. New edges of these embeddings lie in the reserve.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {q r : ℕ}

def embeddingClique (hW : Fintype.card W = q) (f : W ↪ V) : Block V q :=
  ⟨univ.map f, by rw [card_map, card_univ, hW]⟩

omit [Fintype V] [DecidableEq W] [DecidableEq V] in
theorem mem_embeddingClique (hW : Fintype.card W = q) (f : W ↪ V) (v : V) :
    v ∈ (embeddingClique hW f).val ↔ ∃ w, f w = v := by
  simp [embeddingClique]

omit [Fintype V] [DecidableEq W] [DecidableEq V] in
theorem exists_extension_with_clique_image (φ : F ↪ V) (hW : Fintype.card W = q)
    (Q : Block V q) (hQ : usedVertices φ ⊆ Q.val) :
    ∃ f : EmbeddingExtension φ, embeddingClique hW f.val = Q := by
  let φQ : F ↪ Q.val :=
    ⟨fun x => ⟨φ x, hQ ((mem_usedVertices φ _).mpr ⟨x, rfl⟩)⟩,
      fun x y hxy => φ.injective (congrArg Subtype.val hxy)⟩
  have hsize : Fintype.card W ≤ Fintype.card Q.val := by
    rw [Fintype.card_coe, Q.property, hW]
  obtain ⟨fQ⟩ := nonempty_embeddingExtension φQ hsize
  let f : EmbeddingExtension φ :=
    ⟨fQ.val.trans (Function.Embedding.subtype (· ∈ Q.val)),
      fun x => congrArg Subtype.val (fQ.property x)⟩
  have hsub : (embeddingClique hW f.val).val ⊆ Q.val := by
    intro v hv
    obtain ⟨w, rfl⟩ := (mem_embeddingClique hW f.val v).mp hv
    exact (fQ.val w).property
  refine ⟨f, Subtype.ext (eq_of_subset_of_card_le hsub ?_)⟩
  rw [(embeddingClique hW f.val).property, Q.property]

theorem map_complete_eq_cliqueEdges (hW : Fintype.card W = q) (f : W ↪ V) :
    mapGraph f (complete W r) = cliqueEdges r (embeddingClique hW f) := by
  let Q : Block W q := ⟨univ, by rw [card_univ, hW]⟩
  have hQ : cliqueEdges r Q = complete W r := by
    ext e
    simp only [mem_cliqueEdges, Q, subset_univ, complete, mem_univ]
  calc
    _ = mapGraph f (cliqueEdges r Q) := by rw [hQ]
    _ = cliqueEdges r (mapBlock f Q) := map_cliqueEdges f Q
    _ = _ := rfl

open Classical in
def cliqueCandidateExtensions (φ : F ↪ V) (hW : Fintype.card W = q)
    (R : Hypergraph V (r + 1)) (e : Block V (r + 1)) : Finset (EmbeddingExtension φ) :=
  univ.filter fun f => embeddingClique hW f.val ∈ puncturedCliques R e q

omit [DecidableEq W] in
@[simp] theorem mem_cliqueCandidateExtensions (φ : F ↪ V) (hW : Fintype.card W = q)
    (R : Hypergraph V (r + 1)) (e : Block V (r + 1)) (f : EmbeddingExtension φ) :
    f ∈ cliqueCandidateExtensions φ hW R e ↔
      IsPuncturedClique R e (embeddingClique hW f.val).val := by
  classical
  simp only [cliqueCandidateExtensions, mem_filter, mem_univ, true_and, mem_puncturedCliques]

omit [DecidableEq W] in
theorem cliqueCandidateExtensions_card_ge (φ : F ↪ V) (hW : Fintype.card W = q)
    (R : Hypergraph V (r + 1)) (e : Block V (r + 1)) (hroot : usedVertices φ = e.val) :
    (puncturedCliques R e q).card ≤ (cliqueCandidateExtensions φ hW R e).card := by
  classical
  have hsub : puncturedCliques R e q ⊆
      (cliqueCandidateExtensions φ hW R e).image (fun f => embeddingClique hW f.val) := by
    intro Q hQ
    have hpunct := (mem_puncturedCliques R e Q).mp hQ
    obtain ⟨f, hf⟩ := exists_extension_with_clique_image φ hW Q (hroot ▸ hpunct.1)
    refine mem_image.mpr ⟨f, ?_, hf⟩
    apply (mem_cliqueCandidateExtensions φ hW R e f).mpr
    simpa only [hf] using hpunct
  exact (card_le_card hsub).trans card_image_le

omit [DecidableEq W] in
theorem cliqueCandidateExtensions_newEdge_mem (φ : F ↪ V) (hW : Fintype.card W = q)
    (R : Hypergraph V (r + 1)) (e : Block V (r + 1)) (hroot : usedVertices φ = e.val)
    (f : EmbeddingExtension φ) (hf : f ∈ cliqueCandidateExtensions φ hW R e)
    (g : Block W (r + 1)) (hg : ¬ g.val ⊆ F) : mapBlock f.val g ∈ R := by
  have hpunct := (mem_cliqueCandidateExtensions φ hW R e f).mp hf
  have hsub : (mapBlock f.val g).val ⊆ (embeddingClique hW f.val).val :=
    map_subset_map.mpr (subset_univ _)
  rcases hpunct.2 (mapBlock f.val g) hsub with hR | he
  · exact hR
  · have hmap : g.val.map f.val = F.map f.val := by
      calc
        _ = e.val := congrArg Subtype.val he
        _ = usedVertices φ := hroot.symm
        _ = F.map f.val := (EmbeddingExtension.map_roots φ f).symm
    have hEq : g.val = F := map_injective f.val hmap
    exact (hg (hEq ▸ Subset.refl F)).elim

theorem newEdges_complete_root (F₀ : Block W (r + 1)) :
    newEdges F₀.val (complete W (r + 1)) = (complete W (r + 1)).erase F₀ := by
  ext e
  have heq : e.val ⊆ F₀.val ↔ e = F₀ := by
    constructor
    · intro h
      exact Subtype.ext (eq_of_subset_of_card_le h (by rw [e.property, F₀.property]))
    · rintro rfl
      exact Subset.refl _
  simp only [mem_newEdges, complete, mem_univ, true_and, mem_erase, and_true, heq]

theorem map_newEdges_complete_eq_erase (F₀ : Block W (r + 1)) (hW : Fintype.card W = q)
    (φ : F₀.val ↪ V) (e : Block V (r + 1)) (hroot : usedVertices φ = e.val)
    (f : EmbeddingExtension φ) :
    mapGraph f.val (newEdges F₀.val (complete W (r + 1))) =
      (cliqueEdges (r + 1) (embeddingClique hW f.val)).erase e := by
  have he : mapBlock f.val F₀ = e := by
    apply Subtype.ext
    exact (EmbeddingExtension.map_roots φ f).trans hroot
  rw [newEdges_complete_root, mapGraph_erase, map_complete_eq_cliqueEdges hW, he]

end Arxiv2411_18291
