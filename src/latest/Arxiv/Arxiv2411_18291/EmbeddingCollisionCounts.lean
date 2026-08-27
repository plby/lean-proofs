import Arxiv.Arxiv2411_18291.TargetEmbeddingCount
import Arxiv.Arxiv2411_18291.EmbeddingCountBounds

/-!
# Collisions between root-preserving extensions

Fixing the image of one free vertex removes one ambient-size factor.
Summing over pairs of free vertices bounds the number of ordered extension
pairs whose images meet outside the prescribed root image.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem card_filtered_product_le {A B : Type*} (S : Finset A) (T : Finset B)
    (R : A → B → Prop) [DecidableRel R] (M : ℕ)
    (hR : ∀ a ∈ S, (T.filter (R a)).card ≤ M) :
    ((S ×ˢ T).filter fun p => R p.1 p.2).card ≤ S.card * M := by
  calc
    _ = ∑ a ∈ S, (T.filter (R a)).card := by
      simp only [card_eq_sum_ones, sum_filter, sum_product]
    _ ≤ ∑ _a ∈ S, M := sum_le_sum hR
    _ = _ := by simp only [sum_const, smul_eq_mul]

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W}

def vertexTargetExtensions (φ : F ↪ V) (u : W) (v : V) : Finset (EmbeddingExtension φ) :=
  univ.filter fun f => f.val u = v

omit [DecidableEq W] in
theorem vertexTargetExtensions_card_le (φ : F ↪ V) (u : W) (hu : u ∉ F) (v : V) :
    (vertexTargetExtensions φ u v).card ≤
      Fintype.card V ^ (Fintype.card W - F.card - 1) := by
  classical
  have hs : ({u} : Finset W) \ F = {u} :=
    sdiff_eq_self_iff_disjoint.mpr (disjoint_singleton_left.mpr hu)
  have h := edgeTargetExtensions_card_le φ (⟨{u}, card_singleton u⟩ : Block W 1)
    (⟨{v}, card_singleton v⟩ : Block V 1)
  simpa [edgeTargetExtensions, vertexTargetExtensions, mapBlock, Subtype.ext_iff, hs] using h

omit [DecidableEq W] in
theorem fixed_vertex_collision_pairs_card_le (φ : F ↪ V)
    (S T : Finset (EmbeddingExtension φ)) (u v : W) (hv : v ∉ F) :
    ((S ×ˢ T).filter fun p => p.1.val u = p.2.val v).card ≤
      S.card * Fintype.card V ^ (Fintype.card W - F.card - 1) := by
  classical
  apply card_filtered_product_le S T (fun f g : EmbeddingExtension φ => f.val u = g.val v) _
  intro f _
  have hsub : (T.filter fun g => f.val u = g.val v) ⊆ vertexTargetExtensions φ v (f.val u) := by
    intro g hg
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hg).2.symm⟩
  exact (card_le_card hsub).trans (vertexTargetExtensions_card_le φ v hv (f.val u))

def extensionsCollide (φ : F ↪ V) (f g : EmbeddingExtension φ) : Prop :=
  ∃ u : FreeVertices F, ∃ v : FreeVertices F, f.val u.val = g.val v.val

open Classical in
def collidingExtensionPairs (φ : F ↪ V) (S T : Finset (EmbeddingExtension φ)) :
    Finset (EmbeddingExtension φ × EmbeddingExtension φ) :=
  (S ×ˢ T).filter fun p => extensionsCollide φ p.1 p.2

omit [DecidableEq W] [DecidableEq V] in
theorem collidingExtensionPairs_card_le (φ : F ↪ V) (S T : Finset (EmbeddingExtension φ)) :
    (collidingExtensionPairs φ S T).card ≤
      (Fintype.card W - F.card) ^ 2 * S.card *
        Fintype.card V ^ (Fintype.card W - F.card - 1) := by
  classical
  let U : Finset (FreeVertices F × FreeVertices F) := univ
  let B (uv : FreeVertices F × FreeVertices F) :=
    (S ×ˢ T).filter fun p => p.1.val uv.1.val = p.2.val uv.2.val
  have hsub : collidingExtensionPairs φ S T ⊆ U.biUnion B := by
    intro p hp
    obtain ⟨hpST, u, v, huv⟩ := mem_filter.mp hp
    exact mem_biUnion.mpr ⟨(u, v), mem_univ _, mem_filter.mpr ⟨hpST, huv⟩⟩
  have hU : U.card = (Fintype.card W - F.card) ^ 2 := by
    simp only [U, card_univ, Fintype.card_prod, FreeVertices, Fintype.card_subtype_compl,
      Fintype.card_coe, pow_two]
  calc
    _ ≤ (U.biUnion B).card := card_le_card hsub
    _ ≤ ∑ uv ∈ U, (B uv).card := card_biUnion_le
    _ ≤ ∑ _uv ∈ U, S.card * Fintype.card V ^ (Fintype.card W - F.card - 1) := by
      exact sum_le_sum (fun uv _ => fixed_vertex_collision_pairs_card_le φ S T
        uv.1.val uv.2.val uv.2.property)
    _ = _ := by rw [sum_const, hU, smul_eq_mul, Nat.mul_assoc]

end Arxiv2411_18291
