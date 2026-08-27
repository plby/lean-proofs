import Arxiv.Arxiv2411_18291.GreedyStepExpectation

/-!
# Simultaneous degree concentration for greedy embeddings

The process is stopped using only its previous history. Every step satisfies
the deterministic root-dependent expectation budget, so the adaptive tail
bound controls its final degree counts. A finite union bound makes this
simultaneous over all new pattern edges and ambient faces.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

def trajectoryDegree (ω : ℕ → EmbeddingState W V) (t : ℕ) (e : Block W r)
    (S : Finset V) : ℕ :=
  partialFamilyDegree (range t) (fun i => stateEdge (ω (i + 1)) e) S

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem trajectoryDegree_real (ω : ℕ → EmbeddingState W V) (t : ℕ) (e : Block W r)
    (S : Finset V) :
    (trajectoryDegree ω t e S : ℝ) = ∑ i ∈ range t, stateFaceIndicator (ω (i + 1)) e S := by
  simp only [trajectoryDegree, partialFamilyDegree, stateFaceIndicator, Nat.cast_sum]

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem trajectoryDegree_mono (ω : ℕ → EmbeddingState W V) {s t : ℕ} (hst : s ≤ t)
    (e : Block W r) (S : Finset V) : trajectoryDegree ω s e S ≤ trajectoryDegree ω t e S :=
  partialFamilyDegree_mono (range_mono hst) _ _

omit [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] in
theorem historyAt_prefix (ω : ℕ → EmbeddingState W V) (t j : ℕ) (hj : j < t) :
    historyAt (frestrictLe t ω) j = ω (j + 1) := by
  simp only [historyAt, dif_pos (Nat.succ_le_of_lt hj), frestrictLe_apply]

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem historyDegree_prefix (ω : ℕ → EmbeddingState W V) (t : ℕ) (e : Block W r)
    (S : Finset V) : historyDegree (frestrictLe t ω) e S = trajectoryDegree ω t e S := by
  unfold historyDegree trajectoryDegree partialFamilyDegree
  apply sum_congr rfl
  intro i hi
  simp only [historyAt, dif_pos (Nat.succ_le_of_lt (mem_range.mp hi)), frestrictLe_apply]

theorem greedyDegree_tail (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ L : ℝ} (hB : IsGraphBounded B θ)
    (hθ : 0 ≤ θ) (hL : 0 ≤ L) (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θ + H.card * L) ≤ 1 / 4)
    (t : ℕ) (e f : Block W (r + 1)) (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val)
    (he : ¬ e.val ⊆ F)
    (hroot : IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) (S : Block V r) :
    (greedyProbability Φ H B L).real {ω |
      4 * (r + 1).factorial * θ * Fintype.card V ≤ (trajectoryDegree ω t e S.val : ℝ)} ≤
      Real.exp (-(2 * (r + 1).factorial * θ * Fintype.card V / 3)) := by
  have hbudget : (∑ i ∈ range t, rootFaceWeight (Φ i) e f hf S) ≤
      2 * (r + 1).factorial * θ * Fintype.card V := by
    rw [Finset.sum_range (fun i => rootFaceWeight (Φ i) e f hf S)]
    exact sum_rootFaceWeight_le (fun i : Fin t => Φ i) e f hf hroot hθ hnpos he S
  have ht := FiniteHistoryProcess.indicator_double_tail (abortedEmbedding W V)
    (greedyStep Φ H B L) (fun _ a => stateFaceIndicator a e S.val) t
    (fun i => rootFaceWeight (Φ i) e f hf S)
    (fun _ _ a => stateFaceIndicator_bounds a e S.val)
    (fun i _ h => greedyStep_mean_le Φ H B hB hθ hL hn hnpos hsmall i h e f hf hcover S) hbudget
  have htwo : 2 * (2 * ((r + 1).factorial : ℝ) * θ * Fintype.card V) =
      4 * (r + 1).factorial * θ * Fintype.card V := by ring
  simpa only [greedyProbability, trajectoryDegree_real, htwo] using ht

omit [Fintype W] in
theorem trajectoryDegree_failure_le (H : Hypergraph W (r + 1)) (F : Finset W)
    (P : Measure (ℕ → EmbeddingState W V)) [IsProbabilityMeasure P] (t : ℕ) (T δ : ℝ)
    (hδ : 0 ≤ δ)
    (hbound : ∀ e ∈ newEdges F H, ∀ S : Block V r,
      P.real {ω | T ≤ (trajectoryDegree ω t e S.val : ℝ)} ≤ δ) :
    P.real {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
      T ≤ (trajectoryDegree ω t e S.val : ℝ)} ≤ H.card * Fintype.card (Block V r) * δ := by
  let D (e : Block W (r + 1)) (S : Block V r) : Set (ℕ → EmbeddingState W V) :=
    {ω | T ≤ (trajectoryDegree ω t e S.val : ℝ)}
  have hd : ∀ e ∈ newEdges F H, P.real (⋃ S, D e S) ≤
      Fintype.card (Block V r) * δ := by
    intro e he
    calc
      _ ≤ ∑ S : Block V r, P.real (D e S) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _S : Block V r, δ := sum_le_sum fun S _ => hbound e he S
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]
  have hevent : {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
      T ≤ (trajectoryDegree ω t e S.val : ℝ)} =
      ⋃ e ∈ newEdges F H, ⋃ S, D e S := by
    ext ω
    simp only [D, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor <;> rintro ⟨e, he, S, hS⟩ <;> exact ⟨e, he, S, hS⟩
  rw [hevent]
  calc
    _ ≤ ∑ e ∈ newEdges F H, P.real (⋃ S, D e S) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _e ∈ newEdges F H, Fintype.card (Block V r) * δ := sum_le_sum hd
    _ = (newEdges F H).card * (Fintype.card (Block V r) * δ) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ H.card * (Fintype.card (Block V r) * δ) :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_filter_le H (fun e => ¬ e.val ⊆ F))
        (mul_nonneg (Nat.cast_nonneg _) hδ)
    _ = _ := by ring

theorem greedy_all_degrees_failure (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ L : ℝ} (hB : IsGraphBounded B θ)
    (hθ : 0 ≤ θ) (hL : 0 ≤ L) (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θ + H.card * L) ≤ 1 / 4)
    (t : ℕ) (hA : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    (greedyProbability Φ H B L).real {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
      4 * (r + 1).factorial * θ * Fintype.card V ≤ (trajectoryDegree ω t e S.val : ℝ)} ≤
      H.card * Fintype.card (Block V r) *
        Real.exp (-(2 * (r + 1).factorial * θ * Fintype.card V / 3)) := by
  apply trajectoryDegree_failure_le H F _ t _ _ (Real.exp_pos _).le
  intro e he S
  obtain ⟨heH, heF⟩ := (mem_newEdges H e).mp he
  obtain ⟨f, hfH, hfF, hcover⟩ := hA e heH heF
  exact greedyDegree_tail Φ H B hB hθ hL hn hnpos hsmall t e f hfF hcover heF
    (hroots f hfH hfF) S

end Arxiv2411_18291
