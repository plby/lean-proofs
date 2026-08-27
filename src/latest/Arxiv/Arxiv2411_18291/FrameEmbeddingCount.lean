import Arxiv.Arxiv2411_18291.FrameEmbeddings
import Arxiv.Arxiv2411_18291.FrameAssignments
import Arxiv.Arxiv2411_18291.EmbeddingCountBounds

/-!
# A lower bound for full embeddings with a prescribed near frame

Distinct assignments have disjoint sets of completing embeddings. Each
assembled frame has many completions, so its assignment count multiplies
by the usual falling-factorial lower bound for the remaining free vertices.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype W] [Fintype V]
variable [DecidableEq W] [DecidableEq V] {F : Finset W} {q : ℕ}

open Classical in
def frameCandidateExtensions (φ : F ↪ V) (Q : I → Block W q)
    (D : I → Finset (Block V q)) : Finset (EmbeddingExtension φ) :=
  univ.filter fun f => ∀ i, mapBlock f.val (Q i) ∈ D i

omit [DecidableEq W] in
theorem mem_frameCandidateExtensions (φ : F ↪ V) (Q : I → Block W q)
    (D : I → Finset (Block V q)) (f : EmbeddingExtension φ) :
    f ∈ frameCandidateExtensions φ Q D ↔ ∀ i, mapBlock f.val (Q i) ∈ D i := by
  classical
  simp only [frameCandidateExtensions, mem_filter, mem_univ, true_and]

theorem frameCandidateExtensions_count_of_assignments (φ : F ↪ V) (Q : I → Block W q)
    (D : I → Finset (Block V q)) (Y : Finset (I → Block V q))
    (hY : ∀ T ∈ Y, (∀ i, T i ∈ D i) ∧
      ∃ g : frameDomain F Q ↪ V, IsFrameEmbedding φ Q T g)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) :
    (3 / 4 : ℝ) * Y.card * (Fintype.card V : ℝ) ^
      (Fintype.card W - (frameDomain F Q).card) ≤ (frameCandidateExtensions φ Q D).card := by
  classical
  choose g hg using fun T : Y => (hY T.val T.property).2
  let f : (Σ T : Y, EmbeddingExtension (g T)) → frameCandidateExtensions φ Q D :=
    fun z => ⟨(hg z.1).complete z.2, mem_filter.mpr ⟨mem_univ _, fun i => by
      rw [(hg z.1).complete_piece z.2 i]
      exact (hY z.1.val z.1.property).1 i⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨T, a⟩ ⟨T', a'⟩ haa
    have hc : (hg T).complete a = (hg T').complete a' :=
      congrArg (fun z : frameCandidateExtensions φ Q D => z.val) haa
    have hTT : T = T' := by
      apply Subtype.ext
      funext i
      calc
        _ = mapBlock ((hg T).complete a).val (Q i) := ((hg T).complete_piece a i).symm
        _ = mapBlock ((hg T').complete a').val (Q i) := by rw [hc]
        _ = _ := (hg T').complete_piece a' i
    subst T'
    exact congrArg (Sigma.mk T) ((hg T).complete_injective hc)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma, Fintype.card_coe] at hcard
  have hcardR : (∑ T : Y, (Fintype.card (EmbeddingExtension (g T)) : ℝ)) ≤
      (frameCandidateExtensions φ Q D).card := by exact_mod_cast hcard
  calc
    _ = ∑ _T : Y, (3 / 4 : ℝ) * (Fintype.card V : ℝ) ^
        (Fintype.card W - (frameDomain F Q).card) := by
      rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring
    _ ≤ ∑ T : Y, (Fintype.card (EmbeddingExtension (g T)) : ℝ) :=
      sum_le_sum (fun T _ => card_embeddingExtension_three_quarters (g T) hn)
    _ ≤ _ := hcardR

omit [Fintype I] in
theorem frameCandidateExtensions_card_lower {a t : ℕ} (φ : F ↪ V)
    (Q : Fin t → Block W q) (e : ℕ → Block V a) (D : ℕ → Finset (Block V q))
    (haq : a < q)
    (hQ : Pairwise fun i j => Disjoint ((Q i).val \ F) ((Q j).val \ F))
    (hQsize : ∀ i, ((Q i).val \ F).card = q - a)
    (hφ : ∀ i : Fin t, ∀ x : F, x.val ∈ (Q i).val → φ x ∈ (e i).val)
    (heB : ∀ i, (e i).val ⊆ usedVertices φ)
    (hD : ∀ i, ∀ T ∈ D i, (e i).val ⊆ T.val) {L : ℝ} (hL : 0 ≤ L)
    (hsize : ∀ i < t, L ≤ (D i).card)
    (hsmall : ((F.card + t * q : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ (q - a - 1) ≤ L / 2)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) :
    (3 / 4 : ℝ) * (L / 2) ^ t * (Fintype.card V : ℝ) ^
      (Fintype.card W - (frameDomain F Q).card) ≤
        (frameCandidateExtensions φ Q (fun i => D i)).card := by
  classical
  let Y := frameAssignments (usedVertices φ) e D t
  have hY : ∀ T ∈ Y, (∀ i : Fin t, T i ∈ D i) ∧
      ∃ g : frameDomain F Q ↪ V, IsFrameEmbedding φ Q T g := by
    intro T hT
    obtain ⟨_, hTi, hdisj⟩ := mem_filter.mp hT
    refine ⟨fun i => (hTi i).1, exists_frame_embedding φ Q T hQ hdisj ?_ ?_⟩
    · intro i
      rw [hQsize i, card_sdiff, inter_comm, (hTi i).2, (T i).property, (e i).property]
    · intro i x hx
      have heT : (e i).val ⊆ (T i).val := by rw [← (hTi i).2]; exact inter_subset_left
      exact heT (hφ i x hx)
  have hcount := frameCandidateExtensions_count_of_assignments φ Q (fun i => D i) Y hY hn
  have hseq : (L / 2) ^ t ≤ (Y.card : ℝ) :=
    frameAssignments_card_lower (usedVertices φ) e D t haq heB hD hL hsize
      (by simpa only [card_usedVertices] using hsmall)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hseq (by norm_num : (0 : ℝ) ≤ 3 / 4))
      (pow_nonneg (Nat.cast_nonneg _) _)).trans hcount

end Arxiv2411_18291
