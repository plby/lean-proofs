import Arxiv.Arxiv2411_18291.GreedyEmbeddingProcess

/-!
# Conditional-mean bounds for the greedy process

Uniform legal choices satisfy the root-dependent probability budget.
Stopped or aborted steps contribute zero. The bound therefore holds for
every possible history, and can be used by the trajectory concentration
theorem without conditioning on a future success event.
-/

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

omit [Fintype W] [Fintype V] [DecidableEq W] in
@[simp] theorem stateFaceIndicator_none (e : Block W r) (S : Finset V) :
    stateFaceIndicator (none : EmbeddingState W V) e S = 0 := by
  simp [stateFaceIndicator, stateEdge, edgeIncidence]

omit [Fintype W] [Fintype V] [DecidableEq W] in
@[simp] theorem stateFaceIndicator_aborted (e : Block W r) (S : Finset V) :
    stateFaceIndicator (abortedEmbedding W V) e S = 0 := stateFaceIndicator_none e S

omit [Fintype W] [Fintype V] [DecidableEq W] in
@[simp] theorem stateFaceIndicator_some (a : W ↪ V) (e : Block W r) (S : Finset V) :
    stateFaceIndicator (some a : EmbeddingState W V) e S =
      if S ⊆ (mapBlock a e).val then 1 else 0 := by
  unfold stateFaceIndicator stateEdge edgeIncidence
  simp only [Option.map_some]
  split_ifs <;> norm_num

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem uniformExtension_state_mean_eq [Finite W] [Finite V] (φ : F ↪ V)
    [MeasurableSpace (EmbeddingExtension φ)] [MeasurableSingletonClass (EmbeddingExtension φ)]
    (s : Finset (EmbeddingExtension φ)) (hs : s.Nonempty)
    (e : Block W r) (S : Finset V) :
    (∫ a, stateFaceIndicator a e S
      ∂((PMF.uniformOfFinset s hs).map (fun f => chosenEmbedding f.val)).toMeasure) =
      (PMF.uniformOfFinset s hs).toMeasure.real {a | S ⊆ (mapBlock a.val e).val} := by
  let : Fintype W := Fintype.ofFinite W
  let : Fintype V := Fintype.ofFinite V
  have hm : Measurable (fun f : EmbeddingExtension φ => chosenEmbedding f.val) :=
    measurable_of_finite _
  rw [← PMF.toMeasure_map _ _ hm, integral_map hm.aemeasurable
    (measurable_of_finite
      (fun a : EmbeddingState W V => stateFaceIndicator a e S)).aestronglyMeasurable]
  have hi : (fun a : EmbeddingExtension φ => stateFaceIndicator (chosenEmbedding a.val) e S) =
      {a : EmbeddingExtension φ | S ⊆ (mapBlock a.val e).val}.indicator (fun _ => (1 : ℝ)) := by
    funext a
    simp only [chosenEmbedding, stateFaceIndicator_some, Set.indicator, Set.mem_ofPred_eq]
  rw [hi]
  exact integral_indicator_one (μ := (PMF.uniformOfFinset s hs).toMeasure)
    (s := {a : EmbeddingExtension φ | S ⊆ (mapBlock a.val e).val})
    (Set.toFinite _).measurableSet

theorem uniformExtension_state_mean_le (φ : F ↪ V)
    (s : Finset (EmbeddingExtension φ)) (hs : s.Nonempty)
    (hcount : (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ s.card)
    (hn : 0 < Fintype.card V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (S : Block V r) :
    (∫ a, stateFaceIndicator a e S.val
      ∂((PMF.uniformOfFinset s hs).map (fun f => chosenEmbedding f.val)).toMeasure) ≤
      rootFaceWeight φ e f hf S := by
  let : MeasurableSpace (EmbeddingExtension φ) := ⊤
  rw [uniformExtension_state_mean_eq φ s hs e S.val]
  exact uniformExtensions_face_probability_le_weight φ s hs hcount hn e f hf hcover S

theorem greedyStep_mean_le (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ L : ℝ} (hB : IsGraphBounded B θ)
    (hθ : 0 ≤ θ) (hL : 0 ≤ L) (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θ + H.card * L) ≤ 1 / 4)
    (n : ℕ) (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (e f : Block W (r + 1)) (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (S : Block V r) :
    (∫ a, stateFaceIndicator a e S.val ∂(greedyStep Φ H B L n h).toMeasure) ≤
      rootFaceWeight (Φ n) e f hf S := by
  classical
  unfold greedyStep
  split_ifs with hgood hs
  · exact uniformExtension_state_mean_le (Φ n) _ hs
      (historyLegal_card_half (Φ n) H B h hB hθ hL hn hsmall hgood.2) hnpos e f hf hcover S
  · rw [PMF.toMeasure_pure, integral_dirac, stateFaceIndicator_aborted]
    exact rootFaceWeight_nonneg (Φ n) e f hf S
  · rw [PMF.toMeasure_pure, integral_dirac, stateFaceIndicator_aborted]
    exact rootFaceWeight_nonneg (Φ n) e f hf S

end Arxiv2411_18291
