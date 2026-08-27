import Arxiv.Arxiv2411_18291.EmbeddingCollisionCounts
import Arxiv.Arxiv2411_18291.BlockPairOrbits

/-!
# Intersections of extensions without free-vertex collisions

When two extensions do not collide, every shared image vertex comes from
the same prescribed root vertex. Images of a block therefore meet in
exactly its root part, which determines the joint-permutation orbit.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [DecidableEq W] [DecidableEq V] {F : Finset W} {q : ℕ}

omit [DecidableEq W] [DecidableEq V] in
theorem EmbeddingExtension.equal_vertex_of_no_collision (φ : F ↪ V)
    (f g : EmbeddingExtension φ) (hfg : ¬extensionsCollide φ f g)
    {u v : W} (heq : f.val u = g.val v) : u = v ∧ u ∈ F ∧ v ∈ F := by
  classical
  by_cases hu : u ∈ F
  · have hroot : f.val u = g.val u := (f.property ⟨u, hu⟩).trans (g.property ⟨u, hu⟩).symm
    have huv : u = v := g.val.injective (hroot.symm.trans heq)
    exact ⟨huv, hu, huv ▸ hu⟩
  · by_cases hv : v ∈ F
    · have hroot : f.val v = g.val v := (f.property ⟨v, hv⟩).trans (g.property ⟨v, hv⟩).symm
      have huv : u = v := f.val.injective (heq.trans hroot.symm)
      exact False.elim (hu (huv.symm ▸ hv))
    · exact False.elim (hfg ⟨⟨u, hu⟩, ⟨v, hv⟩, heq⟩)

theorem EmbeddingExtension.block_inter_eq_of_no_collision (φ : F ↪ V)
    (f g : EmbeddingExtension φ) (hfg : ¬extensionsCollide φ f g) (Q : Block W q) :
    (mapBlock f.val Q).val ∩ (mapBlock g.val Q).val = (Q.val ∩ F).map f.val := by
  ext x
  change x ∈ Q.val.map f.val ∩ Q.val.map g.val ↔ x ∈ (Q.val ∩ F).map f.val
  constructor
  · intro hx
    obtain ⟨u, hu, hux⟩ := mem_map.mp (mem_inter.mp hx).1
    obtain ⟨v, _, hvx⟩ := mem_map.mp (mem_inter.mp hx).2
    have huF := (f.equal_vertex_of_no_collision φ g hfg (hux.trans hvx.symm)).2.1
    exact mem_map.mpr ⟨u, mem_inter.mpr ⟨hu, huF⟩, hux⟩
  · intro hx
    obtain ⟨u, hu, hux⟩ := mem_map.mp hx
    obtain ⟨huQ, huF⟩ := mem_inter.mp hu
    have hroot : g.val u = f.val u := (g.property ⟨u, huF⟩).trans (f.property ⟨u, huF⟩).symm
    exact mem_inter.mpr ⟨mem_map.mpr ⟨u, huQ, hux⟩,
      mem_map.mpr ⟨u, huQ, hroot.trans hux⟩⟩

def extensionBlockPair (φ : F ↪ V) (f g : EmbeddingExtension φ)
    (hfg : ¬extensionsCollide φ f g) (Q : Block W q) :
    IntersectingBlockPair V q q (Q.val ∩ F).card :=
  ⟨(mapBlock f.val Q, mapBlock g.val Q), by
    rw [f.block_inter_eq_of_no_collision φ g hfg, card_map]⟩

theorem block_root_inter_card_lt (Q : Block W q) (hQ : ¬Q.val ⊆ F) :
    (Q.val ∩ F).card < q := by
  have h : (Q.val ∩ F).card < Q.val.card := card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left, fun h => hQ (inter_eq_left.mp h)⟩)
  simpa only [Q.property] using h

end Arxiv2411_18291
