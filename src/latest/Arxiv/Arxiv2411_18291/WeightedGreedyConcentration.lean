import Arxiv.Arxiv2411_18291.WeightedGreedyProcess

/-! # Concentration for the actual weighted greedy process

The increment bound is the maximum root weight, not one. Every increment
is nonnegative, and every transition expectation is bounded uniformly over
its previous history. The parameter `c` can exceed one.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

theorem weightedGreedyDegree_tail (Φ : ℕ → F ↪ V) (w : ℕ → ℕ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θB θR L C c : ℝ}
    (hB : IsGraphBounded B θB) (hθB : 0 ≤ θB) (hθR : 0 ≤ θR) (hL : 0 ≤ L)
    (hC : 0 < C) (hc : 0 < c)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θB + H.card * L) ≤ 1 / 4) (t : ℕ)
    (hw : ∀ i < t, (w i : ℝ) ≤ C)
    (e f : Block W (r + 1)) (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val)
    (he : ¬ e.val ⊆ F)
    (hroot : IsWeightedFamilyBounded r (fun i : Fin t => rootImage (Φ i) f hf)
      (fun i => w i) θR) (S : Block V r) :
    (weightedGreedyProbability Φ w H B L).real {ω |
      (1 + c) * (2 * (r + 1).factorial * θR * Fintype.card V) ≤
        (weightedTrajectoryDegree w ω t e S.val : ℝ)} ≤
      Real.exp (-(2 * (r + 1).factorial * θR * Fintype.card V * c ^ 2 / ((2 + c) * C))) := by
  have hbudget : (∑ i ∈ range t, (w i : ℝ) * rootFaceWeight (Φ i) e f hf S) ≤
      2 * (r + 1).factorial * θR * Fintype.card V := by
    rw [Finset.sum_range (fun i => (w i : ℝ) * rootFaceWeight (Φ i) e f hf S)]
    exact sum_weighted_rootFaceWeight_le (fun i : Fin t => Φ i) (fun i => w i)
      e f hf hroot hθR hnpos he S
  have hinc : ∀ i < t, ∀ a : EmbeddingState W V,
      0 ≤ (w i : ℝ) * stateFaceIndicator a e S.val ∧
        (w i : ℝ) * stateFaceIndicator a e S.val ≤ C := by
    intro i hi a
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (stateFaceIndicator_bounds a e S.val).1, ?_⟩
    have hle := mul_le_mul_of_nonneg_left (stateFaceIndicator_bounds a e S.val).2
      (Nat.cast_nonneg (w i) : (0 : ℝ) ≤ _)
    rw [mul_one] at hle
    exact hle.trans (hw i hi)
  have ht := FiniteHistoryProcess.upper_tail_ge (abortedEmbedding W V)
    (weightedGreedyStep Φ w H B L) (fun i a => (w i : ℝ) * stateFaceIndicator a e S.val)
    t (fun i => (w i : ℝ) * rootFaceWeight (Φ i) e f hf S) hC hc hinc
    (fun i _ h => weightedGreedyStep_mean_le Φ w H B hB hθB hL hn hnpos hsmall
      i h e f hf hcover S) hbudget
  simpa only [weightedGreedyProbability, weightedTrajectoryDegree_real] using ht

omit [Fintype W] in
theorem weightedTrajectoryDegree_failure_le (w : ℕ → ℕ) (H : Hypergraph W (r + 1))
    (F : Finset W) (P : Measure (ℕ → EmbeddingState W V)) [IsProbabilityMeasure P]
    (t : ℕ) (T δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ e ∈ newEdges F H, ∀ S : Block V r,
      P.real {ω | T ≤ (weightedTrajectoryDegree w ω t e S.val : ℝ)} ≤ δ) :
    P.real {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
      T ≤ (weightedTrajectoryDegree w ω t e S.val : ℝ)} ≤
        H.card * Fintype.card (Block V r) * δ := by
  let D (e : Block W (r + 1)) (S : Block V r) : Set (ℕ → EmbeddingState W V) :=
    {ω | T ≤ (weightedTrajectoryDegree w ω t e S.val : ℝ)}
  have hd : ∀ e ∈ newEdges F H, P.real (⋃ S, D e S) ≤
      Fintype.card (Block V r) * δ := by
    intro e he
    calc
      _ ≤ ∑ S : Block V r, P.real (D e S) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _S : Block V r, δ := sum_le_sum fun S _ => hbound e he S
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]
  have hevent : {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
      T ≤ (weightedTrajectoryDegree w ω t e S.val : ℝ)} =
        ⋃ e ∈ newEdges F H, ⋃ S, D e S := by
    ext ω
    simp only [D, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor <;> rintro ⟨e, he, S, hS⟩ <;> exact ⟨e, he, S, hS⟩
  rw [hevent]
  calc
    _ ≤ ∑ e ∈ newEdges F H, P.real (⋃ S, D e S) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _e ∈ newEdges F H, Fintype.card (Block V r) * δ := sum_le_sum hd
    _ = (newEdges F H).card * (Fintype.card (Block V r) * δ) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ H.card * (Fintype.card (Block V r) * δ) :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_filter_le H (fun e => ¬ e.val ⊆ F))
        (mul_nonneg (Nat.cast_nonneg _) hδ)
    _ = _ := by ring

theorem weightedGreedy_all_degrees_failure (Φ : ℕ → F ↪ V) (w : ℕ → ℕ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θB θR L C c : ℝ}
    (hB : IsGraphBounded B θB) (hθB : 0 ≤ θB) (hθR : 0 ≤ θR) (hL : 0 ≤ L)
    (hC : 0 < C) (hc : 0 < c)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θB + H.card * L) ≤ 1 / 4) (t : ℕ)
    (hw : ∀ i < t, (w i : ℝ) ≤ C) (hA : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsWeightedFamilyBounded r (fun i : Fin t => rootImage (Φ i) f hf) (fun i => w i) θR) :
    (weightedGreedyProbability Φ w H B L).real {ω |
      ∃ e ∈ newEdges F H, ∃ S : Block V r,
        (1 + c) * (2 * (r + 1).factorial * θR * Fintype.card V) ≤
          (weightedTrajectoryDegree w ω t e S.val : ℝ)} ≤
      H.card * Fintype.card (Block V r) *
        Real.exp (-(2 * (r + 1).factorial * θR * Fintype.card V * c ^ 2 / ((2 + c) * C))) := by
  apply weightedTrajectoryDegree_failure_le w H F _ t _ _ (Real.exp_pos _).le
  intro e he S
  obtain ⟨heH, heF⟩ := (mem_newEdges H e).mp he
  obtain ⟨f, hfH, hfF, hcover⟩ := hA e heH heF
  exact weightedGreedyDegree_tail Φ w H B hB hθB hθR hL hC hc hn hnpos hsmall t hw
    e f hfF hcover heF (hroots f hfH hfF) S

end Arxiv2411_18291
