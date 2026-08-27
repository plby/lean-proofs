import Arxiv.Arxiv2411_18291.GreedyRootCompatibility

/-!
# Probability budgets for the greedy extension process

Each step has a deterministic probability bound depending only on its root
map. Summing over the input family gives a bound independent of the number
of steps. Summing over edges containing one face then gives the conditional
mean budget needed for adaptive concentration.
-/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

def rootTargetWeight (φ : F ↪ V) (e f : Block W (r + 1)) (hf : f.val ⊆ F)
    (g : Block V (r + 1)) : ℝ :=
  if r + 1 - (e.val \ F).card ≤ (g.val ∩ (rootImage φ f hf).val).card then
    2 * (e.val \ F).card.factorial / (Fintype.card V : ℝ) ^ (e.val \ F).card
  else 0

def rootFaceWeight (φ : F ↪ V) (e f : Block W (r + 1)) (hf : f.val ⊆ F)
    (S : Block V r) : ℝ :=
  ∑ g ∈ (complete V (r + 1)).filter (fun g => S.val ⊆ g.val), rootTargetWeight φ e f hf g

omit [Fintype W] in
theorem rootTargetWeight_nonneg (φ : F ↪ V) (e f : Block W (r + 1)) (hf : f.val ⊆ F)
    (g : Block V (r + 1)) : 0 ≤ rootTargetWeight φ e f hf g := by
  unfold rootTargetWeight
  split_ifs <;> positivity

omit [Fintype W] in
theorem rootFaceWeight_nonneg (φ : F ↪ V) (e f : Block W (r + 1)) (hf : f.val ⊆ F)
    (S : Block V r) : 0 ≤ rootFaceWeight φ e f hf S :=
  sum_nonneg fun g _ => rootTargetWeight_nonneg φ e f hf g

omit [DecidableEq W] [Fintype W] in
theorem embeddingExtension_face_probability_le_sum (φ : F ↪ V)
    [MeasurableSpace (EmbeddingExtension φ)] (P : Measure (EmbeddingExtension φ))
    [IsProbabilityMeasure P] (e : Block W (r + 1)) (S : Block V r) :
    P.real {a | S.val ⊆ (mapBlock a.val e).val} ≤
      ∑ g ∈ (complete V (r + 1)).filter (fun g => S.val ⊆ g.val),
        P.real {a | mapBlock a.val e = g} := by
  have hevent : {a : EmbeddingExtension φ | S.val ⊆ (mapBlock a.val e).val} =
      ⋃ g ∈ (complete V (r + 1)).filter (fun g => S.val ⊆ g.val),
        {a | mapBlock a.val e = g} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_filter, complete, mem_univ, true_and]
    constructor
    · intro ha
      exact ⟨mapBlock a.val e, ha, rfl⟩
    · rintro ⟨g, hg, he⟩
      simpa only [he] using hg
  rw [hevent]
  exact measureReal_biUnion_finset_le _ _

theorem uniformExtensions_face_probability_le_weight (φ : F ↪ V)
    [MeasurableSpace (EmbeddingExtension φ)] [MeasurableSingletonClass (EmbeddingExtension φ)]
    (s : Finset (EmbeddingExtension φ)) (hs : s.Nonempty)
    (hcount : (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ s.card)
    (hn : 0 < Fintype.card V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (S : Block V r) :
    (PMF.uniformOfFinset s hs).toMeasure.real {a | S.val ⊆ (mapBlock a.val e).val} ≤
      rootFaceWeight φ e f hf S := by
  apply (embeddingExtension_face_probability_le_sum φ _ e S).trans
  apply sum_le_sum
  intro g _
  exact uniformExtensions_target_probability_le_compatible φ s hs hcount hn e f hf hcover g

variable {I : Type*} [Fintype I]

omit [Fintype W] in
theorem sum_rootTargetWeight_le (Φ : I → F ↪ V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) {θ : ℝ} (hE : IsEdgeFamilyBounded (fun i => rootImage (Φ i) f hf) θ)
    (hθ : 0 ≤ θ) (hn : 0 < Fintype.card V) (he : ¬ e.val ⊆ F) (g : Block V (r + 1)) :
    (∑ i, rootTargetWeight (Φ i) e f hf g) ≤ 2 * (r + 1).factorial * θ := by
  have hk : 1 ≤ (e.val \ F).card := by
    apply card_pos.mpr
    exact sdiff_nonempty.mpr he
  have hkr : (e.val \ F).card ≤ r + 1 := by
    simpa only [e.property] using card_le_card (sdiff_subset : e.val \ F ⊆ e.val)
  exact hE.overlap_weight_sum_le hθ hn g _ hk hkr

omit [Fintype W] in
/-- The total face budget is at most `2*r!*θ*n` in the paper's rank notation. -/
theorem sum_rootFaceWeight_le (Φ : I → F ↪ V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) {θ : ℝ} (hE : IsEdgeFamilyBounded (fun i => rootImage (Φ i) f hf) θ)
    (hθ : 0 ≤ θ) (hn : 0 < Fintype.card V) (he : ¬ e.val ⊆ F) (S : Block V r) :
    (∑ i, rootFaceWeight (Φ i) e f hf S) ≤
      2 * (r + 1).factorial * θ * Fintype.card V := by
  have hc : ((complete V (r + 1)).filter (fun g => S.val ⊆ g.val)).card ≤
      Fintype.card V := by
    rw [← card_neighbors_eq_degree]
    exact card_le_univ _
  calc
    _ = ∑ g ∈ (complete V (r + 1)).filter (fun g => S.val ⊆ g.val),
        ∑ i, rootTargetWeight (Φ i) e f hf g := sum_comm
    _ ≤ ∑ _g ∈ (complete V (r + 1)).filter (fun g => S.val ⊆ g.val),
        2 * (r + 1).factorial * θ :=
      sum_le_sum fun g _ => sum_rootTargetWeight_le Φ e f hf hE hθ hn he g
    _ = ((complete V (r + 1)).filter (fun g => S.val ⊆ g.val)).card *
        (2 * (r + 1).factorial * θ) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card V * (2 * (r + 1).factorial * θ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := by ring

end Arxiv2411_18291
