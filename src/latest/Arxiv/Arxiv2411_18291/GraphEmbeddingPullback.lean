import Arxiv.Arxiv2411_18291.Relabeling
import Arxiv.Arxiv2411_18291.CliqueRefinement

/-! # Restricting clique families to the image of a vertex embedding -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {q r : ℕ}

variable [Fintype V] [Fintype W]

theorem mapGraph_cliqueSupport (f : V ↪ W) (D : Finset (Block V q)) :
    mapGraph f (cliqueSupport r D) = cliqueSupport r (mapGraph f D) := by
  ext e'
  constructor
  · intro he'
    obtain ⟨e, he, rfl⟩ := (mem_mapGraph _ _ _).mp he'
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    refine mem_biUnion.mpr ⟨mapBlock f Q, (mem_mapGraph _ _ _).mpr ⟨Q, hQ, rfl⟩, ?_⟩
    exact (mem_cliqueEdges _ _).mpr
      ((mapBlock_subset_mapBlock f e Q).mpr ((mem_cliqueEdges _ _).mp heQ))
  · intro he'
    obtain ⟨Q', hQ', heQ'⟩ := mem_biUnion.mp he'
    obtain ⟨Q, hQ, rfl⟩ := (mem_mapGraph _ _ _).mp hQ'
    rw [← map_cliqueEdges] at heQ'
    obtain ⟨e, heQ, heq⟩ := (mem_mapGraph _ _ _).mp heQ'
    exact (mem_mapGraph _ _ _).mpr ⟨e, mem_biUnion.mpr ⟨Q, hQ, heQ⟩, heq⟩

omit [DecidableEq V] [DecidableEq W] [Fintype W] in
theorem exists_mapGraph_eq_of_supported (f : V ↪ W) (H : Finset (Block W q))
    (hH : ∀ Q ∈ H, Q.val ⊆ (univ : Finset V).map f) :
    ∃ D : Finset (Block V q), mapGraph f D = H := by
  classical
  let D := univ.filter fun P : Block V q => mapBlock f P ∈ H
  refine ⟨D, ?_⟩
  ext Q
  constructor
  · intro hQ
    obtain ⟨P, hP, rfl⟩ := (mem_mapGraph _ _ _).mp hQ
    exact (mem_filter.mp hP).2
  · intro hQ
    obtain ⟨s, _, hs⟩ := subset_map_iff.mp (hH Q hQ)
    have hsq : s.card = q := by rw [← card_map f, ← hs, Q.property]
    let P : Block V q := ⟨s, hsq⟩
    have hPQ : mapBlock f P = Q := Subtype.ext hs.symm
    exact (mem_mapGraph _ _ _).mpr ⟨P, mem_filter.mpr ⟨mem_univ _, hPQ.symm ▸ hQ⟩, hPQ⟩

end Arxiv2411_18291
