import Arxiv.Arxiv2411_18291.RootedPieceEmbeddings
import Arxiv.Arxiv2411_18291.GreedyRootCompatibility

/-!
# Assembling and completing a prescribed frame embedding

A compatible assignment of target cliques gives an actual embedding of the
frame, preserving the entire base map. Every completion of that frame to
the full pattern preserves its assigned clique images.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [DecidableEq W] [DecidableEq V] {q : ℕ}

abbrev frameDomain (F : Finset W) (Q : I → Block W q) : Finset W :=
  F ∪ univ.biUnion (fun i => (Q i).val)

omit [DecidableEq V] in
theorem frameDomain_root_subset (F : Finset W) (Q : I → Block W q) : F ⊆ frameDomain F Q :=
  subset_union_left

omit [DecidableEq V] in
theorem frameDomain_piece_subset (F : Finset W) (Q : I → Block W q) (i : I) :
    (Q i).val ⊆ frameDomain F Q :=
  (subset_biUnion_of_mem (fun j => (Q j).val) (mem_univ i)).trans subset_union_right

omit [DecidableEq V] in
theorem frameDomain_card (F : Finset W) (Q : I → Block W q) (m : ℕ)
    (hQ : Pairwise fun i j => Disjoint ((Q i).val \ F) ((Q j).val \ F))
    (hsize : ∀ i, ((Q i).val \ F).card = m) :
    (frameDomain F Q).card = F.card + Fintype.card I * m := by
  classical
  have hd : ((univ : Finset (Option I)) : Set (Option I)).Pairwise (fun i j =>
      Disjoint (rootedPieces F (fun k => (Q k).val) i)
        (rootedPieces F (fun k => (Q k).val) j)) :=
    fun _ _ _ _ hij => rootedPieces_pairwise F (fun k => (Q k).val) hQ hij
  rw [frameDomain, ← rootedPieces_union F (fun i => (Q i).val), card_biUnion hd,
    Fintype.sum_option]
  simp only [rootedPieces, Option.elim_none, Option.elim_some, hsize, sum_const,
    card_univ, nsmul_eq_mul, Nat.cast_id]

structure IsFrameEmbedding {F : Finset W} (φ : F ↪ V) (Q : I → Block W q)
    (T : I → Block V q) (g : frameDomain F Q ↪ V) : Prop where
  root : ∀ x : F, g ⟨x.val, frameDomain_root_subset F Q x.property⟩ = φ x
  piece : ∀ i, rootImage g (Q i) (frameDomain_piece_subset F Q i) = T i

theorem exists_frame_embedding {F : Finset W} (φ : F ↪ V) (Q : I → Block W q)
    (T : I → Block V q)
    (hQ : Pairwise fun i j => Disjoint ((Q i).val \ F) ((Q j).val \ F))
    (hT : Pairwise fun i j =>
      Disjoint ((T i).val \ usedVertices φ) ((T j).val \ usedVertices φ))
    (hcard : ∀ i, ((Q i).val \ F).card = ((T i).val \ usedVertices φ).card)
    (hroot : ∀ i (x : F), x.val ∈ (Q i).val → φ x ∈ (T i).val) :
    ∃ g : frameDomain F Q ↪ V, IsFrameEmbedding φ Q T g := by
  obtain ⟨g, hg, hpieces⟩ := exists_rooted_piece_embedding φ
    (fun i => (Q i).val) (fun i => (T i).val) hQ hT hcard hroot
  refine ⟨g, hg, fun i => ?_⟩
  apply Subtype.ext
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hv
    exact hpieces i ⟨x.val, (mem_subtype.mp hx)⟩
  · rw [(rootImage g (Q i) (frameDomain_piece_subset F Q i)).property, (T i).property]

def IsFrameEmbedding.complete {F : Finset W} {φ : F ↪ V} {Q : I → Block W q}
    {T : I → Block V q} {g : frameDomain F Q ↪ V} (hg : IsFrameEmbedding φ Q T g)
    (f : EmbeddingExtension g) : EmbeddingExtension φ :=
  ⟨f.val, fun x => (f.property ⟨x.val, frameDomain_root_subset F Q x.property⟩).trans (hg.root x)⟩

omit [DecidableEq V] in
theorem IsFrameEmbedding.complete_piece {F : Finset W} {φ : F ↪ V} {Q : I → Block W q}
    {T : I → Block V q} {g : frameDomain F Q ↪ V} (hg : IsFrameEmbedding φ Q T g)
    (f : EmbeddingExtension g) (i : I) : mapBlock (hg.complete f).val (Q i) = T i :=
  (f.map_rootBlock g (Q i) (frameDomain_piece_subset F Q i)).trans (hg.piece i)

omit [DecidableEq V] in
theorem IsFrameEmbedding.complete_injective {F : Finset W} {φ : F ↪ V} {Q : I → Block W q}
    {T : I → Block V q} {g : frameDomain F Q ↪ V} (hg : IsFrameEmbedding φ Q T g) :
    Function.Injective hg.complete := by
  intro f f' hff
  exact Subtype.ext (congrArg (fun f : EmbeddingExtension φ => f.val) hff)

end Arxiv2411_18291
