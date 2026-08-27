import Arxiv.Arxiv2411_18291.Relabeling
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Embeddings extending a prescribed root map

The free vertices must embed into the vertices unused by the root map. This
gives an explicit equivalence and the exact number of possible extensions,
before excluding forbidden edges in the random greedy process.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [DecidableEq W]
variable {F : Finset W}

def usedVertices (φ : F ↪ V) : Finset V := univ.map φ

omit [DecidableEq W] in
@[simp] theorem mem_usedVertices (φ : F ↪ V) (v : V) :
    v ∈ usedVertices φ ↔ ∃ x : F, φ x = v := by
  simp [usedVertices]

omit [DecidableEq W] in
@[simp] theorem card_usedVertices (φ : F ↪ V) : (usedVertices φ).card = F.card := by
  simp [usedVertices]

abbrev FreeVertices (F : Finset W) := {x : W // x ∉ F}

abbrev UnusedVertices (φ : F ↪ V) := {v : V // v ∉ usedVertices φ}

abbrev EmbeddingExtension (φ : F ↪ V) := {f : W ↪ V // ∀ x : F, f x.val = φ x}

def completeEmbedding (φ : F ↪ V) (ψ : FreeVertices F ↪ UnusedVertices φ) : W ↪ V where
  toFun x := if hx : x ∈ F then φ ⟨x, hx⟩ else (ψ ⟨x, hx⟩).val
  inj' := by
    intro x y hxy
    by_cases hx : x ∈ F <;> by_cases hy : y ∈ F
    · simp only [dif_pos hx, dif_pos hy] at hxy
      exact congrArg Subtype.val (φ.injective hxy)
    · simp only [dif_pos hx, dif_neg hy] at hxy
      exact ((ψ ⟨y, hy⟩).property ((mem_usedVertices φ _).mpr ⟨⟨x, hx⟩, hxy⟩)).elim
    · simp only [dif_neg hx, dif_pos hy] at hxy
      exact ((ψ ⟨x, hx⟩).property ((mem_usedVertices φ _).mpr ⟨⟨y, hy⟩, hxy.symm⟩)).elim
    · simp only [dif_neg hx, dif_neg hy] at hxy
      exact congrArg Subtype.val (ψ.injective (Subtype.ext hxy))

@[simp] theorem completeEmbedding_root (φ : F ↪ V) (ψ : FreeVertices F ↪ UnusedVertices φ)
    (x : F) : completeEmbedding φ ψ x.val = φ x := by
  change (if hx : x.val ∈ F then φ ⟨x.val, hx⟩ else (ψ ⟨x.val, hx⟩).val) = φ x
  rw [dif_pos x.property]

def completeExtension (φ : F ↪ V) (ψ : FreeVertices F ↪ UnusedVertices φ) :
    EmbeddingExtension φ := ⟨completeEmbedding φ ψ, completeEmbedding_root φ ψ⟩

def restrictExtension (φ : F ↪ V) (f : EmbeddingExtension φ) :
    FreeVertices F ↪ UnusedVertices φ where
  toFun x := ⟨f.val x.val, by
    intro h
    obtain ⟨y, hy⟩ := (mem_usedVertices φ _).mp h
    have he := f.val.injective ((f.property y).trans hy)
    exact x.property (he ▸ y.property)⟩
  inj' := by
    intro x y hxy
    exact Subtype.ext (f.val.injective (congrArg Subtype.val hxy))

/-- All choices for the free vertices, with no implicit extension assumption. -/
def embeddingExtensionEquiv (φ : F ↪ V) :
    EmbeddingExtension φ ≃ (FreeVertices F ↪ UnusedVertices φ) where
  toFun := restrictExtension φ
  invFun := completeExtension φ
  left_inv f := by
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    change (if hx : x ∈ F then φ ⟨x, hx⟩ else f.val x) = f.val x
    by_cases hx : x ∈ F
    · rw [dif_pos hx]
      exact (f.property ⟨x, hx⟩).symm
    · rw [dif_neg hx]
  right_inv ψ := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    change (if hx : x.val ∈ F then φ ⟨x.val, hx⟩ else (ψ ⟨x.val, hx⟩).val) = (ψ x).val
    rw [dif_neg x.property]

variable [Fintype W] [Fintype V] [DecidableEq V]

omit [DecidableEq W] in
theorem card_embeddingExtension (φ : F ↪ V) :
    Fintype.card (EmbeddingExtension φ) =
      (Fintype.card V - F.card).descFactorial (Fintype.card W - F.card) := by
  classical
  rw [Fintype.card_congr (embeddingExtensionEquiv φ), Fintype.card_embedding_eq]
  simp only [FreeVertices, UnusedVertices, Fintype.card_subtype_compl,
    Fintype.card_coe, card_usedVertices]

omit [DecidableEq W] [DecidableEq V] in
theorem nonempty_embeddingExtension (φ : F ↪ V) (hWV : Fintype.card W ≤ Fintype.card V) :
    Nonempty (EmbeddingExtension φ) := by
  classical
  apply Fintype.card_pos_iff.mp
  rw [card_embeddingExtension φ]
  exact Nat.descFactorial_pos.mpr (Nat.sub_le_sub_right hWV _)

end Arxiv2411_18291
