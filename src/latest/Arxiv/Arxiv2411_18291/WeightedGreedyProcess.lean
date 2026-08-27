import Arxiv.Arxiv2411_18291.GreedyDegreeConcentration
import Arxiv.Arxiv2411_18291.WeightedGreedyBudgets

/-! # Greedy embeddings stopped at weighted degree caps

Each root is embedded once. Its fixed natural weight multiplies its actual
incidence indicators. The stop uses only the previous history, and weights
at least one make the same cap control the ordinary forbidden graph.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r n : ℕ}

def weightedHistoryDegree (w : ℕ → ℕ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (e : Block W r) (S : Finset V) : ℕ :=
  ∑ j ∈ range n, w j * edgeIncidence (stateEdge (historyAt h j) e) S

def weightedTrajectoryDegree (w : ℕ → ℕ) (ω : ℕ → EmbeddingState W V)
    (t : ℕ) (e : Block W r) (S : Finset V) : ℕ :=
  ∑ j ∈ range t, w j * edgeIncidence (stateEdge (ω (j + 1)) e) S

def weightedHistoryGood (w : ℕ → ℕ) (H : Hypergraph W (r + 1)) (F : Finset W) (L : ℝ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n) : Prop :=
  ∀ e ∈ newEdges F H, ∀ S : Block V r,
    (weightedHistoryDegree w h e S.val : ℝ) < L * Fintype.card V

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem historyDegree_le_weighted (w : ℕ → ℕ)
    (hw : ∀ j < n, 1 ≤ w j) (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (e : Block W r) (S : Finset V) : historyDegree h e S ≤ weightedHistoryDegree w h e S := by
  unfold historyDegree partialFamilyDegree weightedHistoryDegree
  apply sum_le_sum
  intro j hj
  exact le_mul_of_one_le_left (Nat.zero_le _) (hw j (mem_range.mp hj))

omit [Fintype W] in
theorem weightedHistoryGood.unweighted (w : ℕ → ℕ) (H : Hypergraph W (r + 1))
    {L : ℝ} {h : FiniteHistoryProcess.History (EmbeddingState W V) n}
    (hgood : weightedHistoryGood w H F L h) (hw : ∀ j < n, 1 ≤ w j) :
    historyGood H F L h := by
  intro e he S
  have hle : (historyDegree h e S.val : ℝ) ≤ weightedHistoryDegree w h e S.val := by
    exact_mod_cast historyDegree_le_weighted w hw h e S.val
  exact hle.trans_lt (hgood e he S)

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem weightedTrajectoryDegree_real (w : ℕ → ℕ) (ω : ℕ → EmbeddingState W V)
    (t : ℕ) (e : Block W r) (S : Finset V) :
    (weightedTrajectoryDegree w ω t e S : ℝ) =
      ∑ j ∈ range t, (w j : ℝ) * stateFaceIndicator (ω (j + 1)) e S := by
  simp only [weightedTrajectoryDegree, stateFaceIndicator, Nat.cast_sum, Nat.cast_mul]

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem weightedTrajectoryDegree_mono (w : ℕ → ℕ) (ω : ℕ → EmbeddingState W V)
    {s t : ℕ} (hst : s ≤ t) (e : Block W r) (S : Finset V) :
    weightedTrajectoryDegree w ω s e S ≤ weightedTrajectoryDegree w ω t e S :=
  sum_le_sum_of_subset_of_nonneg (range_mono hst) (fun _ _ _ => Nat.zero_le _)

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem weightedHistoryDegree_prefix (w : ℕ → ℕ) (ω : ℕ → EmbeddingState W V)
    (t : ℕ) (e : Block W r) (S : Finset V) :
    weightedHistoryDegree w (frestrictLe t ω) e S = weightedTrajectoryDegree w ω t e S := by
  apply sum_congr rfl
  intro j hj
  rw [historyAt_prefix ω t j (mem_range.mp hj)]

def weightedGreedyStep (Φ : ℕ → F ↪ V) (w : ℕ → ℕ) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (n : ℕ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n) : PMF (EmbeddingState W V) := by
  classical
  exact if weightedHistoryGood w H F L h then greedyStep Φ H B L n h
    else PMF.pure (abortedEmbedding W V)

def weightedGreedyProbability (Φ : ℕ → F ↪ V) (w : ℕ → ℕ) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) : Measure (ℕ → EmbeddingState W V) :=
  FiniteHistoryProcess.probability (abortedEmbedding W V) (weightedGreedyStep Φ w H B L)

instance weightedGreedyProbability_isProbability (Φ : ℕ → F ↪ V) (w : ℕ → ℕ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) :
    IsProbabilityMeasure (weightedGreedyProbability Φ w H B L) := by
  unfold weightedGreedyProbability
  exact FiniteHistoryProcess.probability_isProbability (abortedEmbedding W V)
    (weightedGreedyStep Φ w H B L)

theorem weightedGreedyStep_mean_le (Φ : ℕ → F ↪ V) (w : ℕ → ℕ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ L : ℝ}
    (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ) (hL : 0 ≤ L)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θ + H.card * L) ≤ 1 / 4)
    (n : ℕ) (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (e f : Block W (r + 1)) (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (S : Block V r) :
    (∫ a, (w n : ℝ) * stateFaceIndicator a e S.val
      ∂(weightedGreedyStep Φ w H B L n h).toMeasure) ≤
        (w n : ℝ) * rootFaceWeight (Φ n) e f hf S := by
  classical
  unfold weightedGreedyStep
  split_ifs
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (greedyStep_mean_le Φ H B hB hθ hL hn hnpos hsmall n h e f hf hcover S)
      (Nat.cast_nonneg _)
  · rw [PMF.toMeasure_pure, integral_dirac, stateFaceIndicator_aborted, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (rootFaceWeight_nonneg (Φ n) e f hf S)

end Arxiv2411_18291
