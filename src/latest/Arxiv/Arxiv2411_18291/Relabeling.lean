import Arxiv.Arxiv2411_18291.Partite
import Mathlib.Data.Finset.Preimage

/-! # Injective relabeling of hypergraphs and true decompositions -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} {q r : ℕ}

/-- Relabel a block along an injective vertex map. -/
def mapBlock (f : V ↪ W) (s : Block V r) : Block W r :=
  ⟨s.val.map f, by simpa using s.property⟩

theorem mapBlock_injective (f : V ↪ W) : Function.Injective (mapBlock (r := r) f) := by
  intro s t h
  exact Subtype.ext (Finset.map_injective f (congrArg Subtype.val h))

@[simp] theorem mapBlock_refl (s : Block V r) : mapBlock (Function.Embedding.refl V) s = s := by
  apply Subtype.ext
  exact Finset.map_refl

@[simp] theorem mapBlock_map {U : Type*} (f : V ↪ W) (g : W ↪ U) (s : Block V r) :
    mapBlock g (mapBlock f s) = mapBlock (f.trans g) s := by
  apply Subtype.ext
  exact Finset.map_map f g s.val

def blockEmbedding (f : V ↪ W) : Block V r ↪ Block W r :=
  ⟨mapBlock f, mapBlock_injective f⟩

/-- Relabel an edge or clique family. -/
def mapGraph (f : V ↪ W) (G : Hypergraph V r) : Hypergraph W r :=
  G.map (blockEmbedding f)

theorem mem_mapGraph (f : V ↪ W) (G : Hypergraph V r) (e : Block W r) :
    e ∈ mapGraph f G ↔ ∃ e' ∈ G, mapBlock f e' = e := by
  simp only [mapGraph, mem_map]
  rfl

@[simp] theorem card_mapGraph (f : V ↪ W) (G : Hypergraph V r) :
    (mapGraph f G).card = G.card := card_map _

@[simp] theorem mapBlock_subset_mapBlock (f : V ↪ W) (e : Block V r) (Q : Block V q) :
    (mapBlock f e).val ⊆ (mapBlock f Q).val ↔ e.val ⊆ Q.val := map_subset_map

theorem mapGraph_mono (f : V ↪ W) {G H : Hypergraph V r} (h : G ⊆ H) :
    mapGraph f G ⊆ mapGraph f H := map_subset_map.mpr h

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem map_cliqueEdges (f : V ↪ W) (Q : Block V q) :
    mapGraph f (cliqueEdges r Q) = cliqueEdges r (mapBlock f Q) := by
  ext e'
  rw [mem_mapGraph, mem_cliqueEdges]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (mapBlock_subset_mapBlock f e Q).mpr ((mem_cliqueEdges e Q).mp he)
  · intro he
    change e'.val ⊆ Q.val.map f at he
    obtain ⟨s, hs, hes⟩ := subset_map_iff.mp he
    have hsr : s.card = r := by rw [← card_map f, ← hes, e'.property]
    exact ⟨⟨s, hsr⟩, (mem_cliqueEdges _ Q).mpr hs, Subtype.ext hes.symm⟩

/-- An embedding of the vertices preserves the actual clique decomposition. -/
theorem IsDecomposition.map {G : Hypergraph V r} {D : Finset (Block V q)}
    (hD : IsDecomposition G D) (f : V ↪ W) :
    IsDecomposition (mapGraph f G) (mapGraph f D) := by
  apply isDecomposition_of_unique
  · intro Q' hQ'
    obtain ⟨Q, hQ, rfl⟩ := (mem_mapGraph f D Q').mp hQ'
    rw [← map_cliqueEdges]
    exact mapGraph_mono f (hD.clique_subset hQ)
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := (mem_mapGraph f G e').mp he'
    obtain ⟨Q, ⟨hQ, heQ⟩, huniq⟩ := hD.unique he
    refine ⟨mapBlock f Q, ⟨?_, (mapBlock_subset_mapBlock f e Q).mpr heQ⟩, ?_⟩
    · exact (mem_mapGraph f D _).mpr ⟨Q, hQ, rfl⟩
    · intro P' hP'
      obtain ⟨hPD, heP⟩ := hP'
      obtain ⟨P, hP, rfl⟩ := (mem_mapGraph f D P').mp hPD
      exact congrArg (mapBlock f) (huniq P ⟨hP, (mapBlock_subset_mapBlock f e P).mp heP⟩)

omit [Fintype V] [Fintype W] in
@[simp] theorem mapGraph_union (f : V ↪ W) (G H : Hypergraph V r) :
    mapGraph f (G ∪ H) = mapGraph f G ∪ mapGraph f H := map_union _ _

omit [Fintype V] [Fintype W] in
@[simp] theorem mapGraph_inter (f : V ↪ W) (G H : Hypergraph V r) :
    mapGraph f (G ∩ H) = mapGraph f G ∩ mapGraph f H := map_inter _ _

omit [Fintype V] [Fintype W] in
@[simp] theorem mapGraph_erase (f : V ↪ W) (D : Finset (Block V q)) (Q : Block V q) :
    mapGraph f (D.erase Q) = (mapGraph f D).erase (mapBlock f Q) := map_erase _ _ _

end Arxiv2411_18291
