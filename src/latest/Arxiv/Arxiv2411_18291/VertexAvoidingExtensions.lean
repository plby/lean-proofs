import Arxiv.Arxiv2411_18291.ForbiddenEmbeddingCount

/-!
# Candidate embeddings avoiding a prescribed vertex set

Fixing the image of one free vertex leaves at most `n^(m-1)` extensions.
Thus a forbidden set of `u` vertices excludes at most `m*u*n^(m-1)`
extensions. Together with the initial extension count, this leaves at least
half of all `n^m` possible assignments under explicit size conditions.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W}

def vertexHitExtensions (φ : F ↪ V) (x : W) (v : V) : Finset (EmbeddingExtension φ) :=
  univ.filter fun f => f.val x = v

omit [DecidableEq W] in
theorem vertexHitExtensions_card_le (φ : F ↪ V) (x : W) (hx : x ∉ F) (v : V) :
    (vertexHitExtensions φ x v).card ≤
      Fintype.card V ^ (Fintype.card W - F.card - 1) := by
  classical
  let s := vertexHitExtensions φ x v
  let record : s → (FreeVertices (insert x F) → V) :=
    fun f => forgetExtensionVertex φ x f.val
  have hinj : Function.Injective record := by
    intro f g hfg
    apply Subtype.ext
    apply EmbeddingExtension.ext_of_forget_eq φ x hfg
    exact ((mem_filter.mp f.property).2).trans ((mem_filter.mp g.property).2).symm
  have hc : Fintype.card (FreeVertices (insert x F)) = Fintype.card W - F.card - 1 := by
    simp only [FreeVertices, Fintype.card_subtype_compl, Fintype.card_coe,
      card_insert_of_notMem hx]
    omega
  simpa only [Fintype.card_coe, Fintype.card_fun, hc] using Fintype.card_le_of_injective record hinj

def forbiddenVertexExtensions (φ : F ↪ V) (U : Finset V) : Finset (EmbeddingExtension φ) :=
  (univ \ F).biUnion fun x => U.biUnion (vertexHitExtensions φ x)

def vertexAvoidingExtensions (φ : F ↪ V) (U : Finset V) : Finset (EmbeddingExtension φ) :=
  univ \ forbiddenVertexExtensions φ U

@[simp] theorem mem_vertexAvoidingExtensions (φ : F ↪ V) (U : Finset V)
    (f : EmbeddingExtension φ) :
    f ∈ vertexAvoidingExtensions φ U ↔ Disjoint ((univ \ F).map f.val) U := by
  simp only [vertexAvoidingExtensions, mem_sdiff, mem_univ, true_and]
  constructor
  · intro hf
    apply disjoint_left.mpr
    intro v hv hU
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hv
    apply hf
    exact mem_biUnion.mpr ⟨x, hx,
      mem_biUnion.mpr ⟨f.val x, hU, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩⟩
  · intro hdis hf
    obtain ⟨x, hx, hfx⟩ := mem_biUnion.mp hf
    obtain ⟨v, hv, hfv⟩ := mem_biUnion.mp hfx
    have heq : f.val x = v := (mem_filter.mp hfv).2
    exact disjoint_left.mp hdis (mem_map.mpr ⟨x, hx, heq⟩) hv

theorem forbiddenVertexExtensions_card_le (φ : F ↪ V) (U : Finset V) :
    (forbiddenVertexExtensions φ U).card ≤ (Fintype.card W - F.card) * U.card *
      Fintype.card V ^ (Fintype.card W - F.card - 1) := by
  calc
    _ ≤ ∑ x ∈ univ \ F, (U.biUnion (vertexHitExtensions φ x)).card := card_biUnion_le
    _ ≤ ∑ x ∈ univ \ F, ∑ _v ∈ U,
        Fintype.card V ^ (Fintype.card W - F.card - 1) := by
      apply sum_le_sum
      intro x hx
      exact card_biUnion_le.trans (sum_le_sum fun v _ =>
        vertexHitExtensions_card_le φ x (mem_sdiff.mp hx).2 v)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, card_sdiff_of_subset (subset_univ F), card_univ,
        Nat.cast_id]
      ring

theorem vertexAvoidingExtensions_card_half (φ : F ↪ V) (U : Finset V)
    (hn : 4 * Fintype.card W ^ 2 ≤ Fintype.card V)
    (hU : 4 * Fintype.card W * U.card ≤ Fintype.card V) :
    (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤
      (vertexAvoidingExtensions φ U).card := by
  have hbad : 4 * (forbiddenVertexExtensions φ U).card ≤
      Fintype.card V ^ (Fintype.card W - F.card) := by
    by_cases hm : Fintype.card W - F.card = 0
    · have hb := forbiddenVertexExtensions_card_le φ U
      simp only [hm, zero_mul] at hb
      have hz : (forbiddenVertexExtensions φ U).card = 0 := by omega
      simp only [hz, mul_zero, hm, pow_zero, Nat.zero_le]
    · calc
        _ ≤ 4 * ((Fintype.card W - F.card) * U.card *
            Fintype.card V ^ (Fintype.card W - F.card - 1)) :=
          Nat.mul_le_mul_left 4 (forbiddenVertexExtensions_card_le φ U)
        _ ≤ (4 * Fintype.card W * U.card) *
            Fintype.card V ^ (Fintype.card W - F.card - 1) := by
          rw [← mul_assoc, ← mul_assoc]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right U.card
            (Nat.mul_le_mul_left 4 (Nat.sub_le _ _)))
        _ ≤ Fintype.card V * Fintype.card V ^ (Fintype.card W - F.card - 1) :=
          Nat.mul_le_mul_right _ hU
        _ = _ := by
          rw [mul_comm, ← pow_succ]
          congr 1
          omega
  have hbadReal : 4 * ((forbiddenVertexExtensions φ U).card : ℝ) ≤
      (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) := by exact_mod_cast hbad
  have hstart := card_embeddingExtension_three_quarters φ hn
  have hcard : ((vertexAvoidingExtensions φ U).card : ℝ) =
      Fintype.card (EmbeddingExtension φ) - (forbiddenVertexExtensions φ U).card := by
    rw [vertexAvoidingExtensions, card_sdiff_of_subset (subset_univ _), card_univ,
      Nat.cast_sub (card_le_univ _)]
  rw [hcard]
  linarith

end Arxiv2411_18291
