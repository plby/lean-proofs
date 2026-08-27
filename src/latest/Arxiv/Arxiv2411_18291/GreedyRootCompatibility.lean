import Arxiv.Arxiv2411_18291.EdgeFamilyBoundedness
import Arxiv.Arxiv2411_18291.UniformExtensionProbability

/-!
# Compatibility of prescribed roots with target edges

Admissibility puts the rooted part of a new edge inside a fixed root edge.
Any target of the new edge must consequently have a large intersection
with that root edge's image. Boundedness of the input family controls how
many indices can satisfy this necessary condition, even when root images
repeat.
-/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [DecidableEq W] [DecidableEq V] {F : Finset W} {r : ℕ}

def rootBlock (F : Finset W) (e : Block W r) (he : e.val ⊆ F) : Block F r :=
  ⟨e.val.subtype (· ∈ F), by
    rw [← card_map (Function.Embedding.subtype (· ∈ F)),
      subtype_map_of_mem (fun _ hx => he hx), e.property]⟩

def rootImage (φ : F ↪ V) (e : Block W r) (he : e.val ⊆ F) : Block V r :=
  mapBlock φ (rootBlock F e he)

omit [DecidableEq V] in
theorem EmbeddingExtension.map_rootBlock (φ : F ↪ V) (f : EmbeddingExtension φ)
    (e : Block W r) (he : e.val ⊆ F) : mapBlock f.val e = rootImage φ e he := by
  apply Subtype.ext
  ext v
  change v ∈ e.val.map f.val ↔ v ∈ (e.val.subtype (· ∈ F)).map φ
  simp only [mem_map, mem_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, he hx⟩, hx, (f.property ⟨x, he hx⟩).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, f.property x⟩

/-- Admissibility of the rooted extension type from Definition 5.4. -/
def IsAdmissible (H : Hypergraph W (r + 1)) (F : Finset W) : Prop :=
  ∀ e ∈ H, ¬ e.val ⊆ F → ∃ f ∈ H, f.val ⊆ F ∧ e.val ∩ F ⊆ f.val

theorem rootImage_overlap_of_target (φ : F ↪ V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (a : EmbeddingExtension φ)
    (g : Block V (r + 1)) (hag : mapBlock a.val e = g) :
    r + 1 - (e.val \ F).card ≤ (g.val ∩ (rootImage φ f hf).val).card := by
  have hsub : (e.val ∩ F).map a.val ⊆
      (mapBlock a.val e).val ∩ (mapBlock a.val f).val := by
    change (e.val ∩ F).map a.val ⊆ e.val.map a.val ∩ f.val.map a.val
    rw [← map_inter]
    exact map_subset_map.mpr (subset_inter inter_subset_left hcover)
  rw [hag, EmbeddingExtension.map_rootBlock φ a f hf] at hsub
  have hc := card_le_card hsub
  rw [card_map] at hc
  have hec := card_sdiff_add_card_inter e.val F
  rw [e.property] at hec
  omega

variable [Fintype W] [Fintype V]

theorem uniformExtensions_target_probability_le_compatible (φ : F ↪ V)
    [MeasurableSpace (EmbeddingExtension φ)] [MeasurableSingletonClass (EmbeddingExtension φ)]
    (s : Finset (EmbeddingExtension φ)) (hs : s.Nonempty)
    (hcount : (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ s.card)
    (hn : 0 < Fintype.card V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (g : Block V (r + 1)) :
    (PMF.uniformOfFinset s hs).toMeasure.real {a | mapBlock a.val e = g} ≤
      if r + 1 - (e.val \ F).card ≤ (g.val ∩ (rootImage φ f hf).val).card then
        2 * (e.val \ F).card.factorial / (Fintype.card V : ℝ) ^ (e.val \ F).card
      else 0 := by
  split_ifs with h
  · exact uniformExtensions_target_probability_le φ s hs hcount hn e g
  · have he : {a : EmbeddingExtension φ | mapBlock a.val e = g} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact h (rootImage_overlap_of_target φ e f hf hcover a g ha)
    rw [he, measureReal_empty]

variable {I : Type*} [Fintype I]

/-- Sum of the deterministic one-step probability bounds for one target. -/
theorem IsEdgeFamilyBounded.overlap_weight_sum_le {E : I → Block V (r + 1)} {θ : ℝ}
    (hE : IsEdgeFamilyBounded E θ) (hθ : 0 ≤ θ) (hn : 0 < Fintype.card V)
    (g : Block V (r + 1)) (k : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r + 1) :
    (∑ i, if r + 1 - k ≤ (g.val ∩ (E i).val).card then
      2 * (k.factorial : ℝ) / (Fintype.card V : ℝ) ^ k else 0) ≤
      2 * (r + 1).factorial * θ := by
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hc := hE.overlap_card_le hθ g (r + 1 - k) (by omega)
  rw [Nat.sub_sub_self hkr, Nat.choose_symm hkr] at hc
  have hfac : (r + 1).choose k * k.factorial ≤ (r + 1).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial hkr
    have hp := Nat.factorial_pos (r + 1 - k)
    nlinarith
  calc
    _ = (familyOverlapIndices E g (r + 1 - k)).card *
        (2 * (k.factorial : ℝ) / (Fintype.card V : ℝ) ^ k) := by
      rw [← sum_filter]
      simp only [familyOverlapIndices, sum_const, nsmul_eq_mul]
    _ ≤ ((r + 1).choose k * θ * (Fintype.card V : ℝ) ^ k) *
        (2 * (k.factorial : ℝ) / (Fintype.card V : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2 * ((r + 1).choose k * (k.factorial : ℝ)) * θ := by
      field_simp [hV.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hfac) (by norm_num)) hθ

end Arxiv2411_18291
