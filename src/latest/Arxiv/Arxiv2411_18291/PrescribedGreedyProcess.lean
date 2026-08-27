import Arxiv.Arxiv2411_18291.PrescribedExtensionProbability

/-!
# Greedy choices from prescribed, possibly history-dependent, candidates

The candidate family can enforce additional requirements such as putting
every new edge in the reserve. It may also depend on earlier choices, as
needed by the absorber's vertex-separation restrictions. A lower bound on
its size is required only when the history is successful and below the cap.
-/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

abbrev CandidateFamilies (Φ : ℕ → F ↪ V) :=
  (i : ℕ) → FiniteHistoryProcess.History (EmbeddingState W V) i →
    Finset (EmbeddingExtension (Φ i))

def HasCandidateLowerBound (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (L η : ℝ) (t : ℕ) : Prop :=
  ∀ i < t, ∀ h, historySuccessful h → historyGood H F L h →
    η * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ (A i h).card

def prescribedGreedyStep (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (n : ℕ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n) : PMF (EmbeddingState W V) := by
  classical
  exact if historySuccessful h ∧ historyGood H F L h then
    if hs : (candidateLegalExtensions (Φ n) H (historyForbidden H B F h) (A n h)).Nonempty then
      (PMF.uniformOfFinset _ hs).map (fun f => chosenEmbedding f.val)
    else PMF.pure (abortedEmbedding W V)
  else PMF.pure (abortedEmbedding W V)

def prescribedGreedyProbability (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) :
    Measure (ℕ → EmbeddingState W V) :=
  FiniteHistoryProcess.probability (abortedEmbedding W V) (prescribedGreedyStep Φ A H B L)

instance prescribedGreedyProbability_isProbability (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) :
    IsProbabilityMeasure (prescribedGreedyProbability Φ A H B L) :=
  FiniteHistoryProcess.probability_isProbability (abortedEmbedding W V)
    (prescribedGreedyStep Φ A H B L)

theorem prescribedGreedyStep_mean_le (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θB L η : ℝ}
    (hB : IsGraphBounded B θB) (hθB : 0 ≤ θB) (hL : 0 ≤ L) (hη : 0 < η)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θB + H.card * L) ≤ η / 2)
    (t : ℕ) (hA : HasCandidateLowerBound Φ A H L η t)
    (n : ℕ) (hn : n < t) (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (e f : Block W (r + 1)) (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (S : Block V r) :
    (∫ a, stateFaceIndicator a e S.val ∂(prescribedGreedyStep Φ A H B L n h).toMeasure) ≤
      rootFaceWeight (Φ n) e f hf S / η := by
  classical
  unfold prescribedGreedyStep
  split_ifs with hgood hs
  · exact uniformExtension_state_mean_le_scaled (Φ n) _ hs hη
      (historyCandidateLegal_card_half (Φ n) H B h (A n h) hB hθB hL
        (hA n hn h hgood.1 hgood.2) hsmall hgood.2) hnpos e f hf hcover S
  · rw [PMF.toMeasure_pure, integral_dirac, stateFaceIndicator_aborted]
    exact div_nonneg (rootFaceWeight_nonneg (Φ n) e f hf S) hη.le
  · rw [PMF.toMeasure_pure, integral_dirac, stateFaceIndicator_aborted]
    exact div_nonneg (rootFaceWeight_nonneg (Φ n) e f hf S) hη.le

theorem prescribedGreedyStep_choose_of_good (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θB L η : ℝ}
    (hB : IsGraphBounded B θB) (hθB : 0 ≤ θB) (hL : 0 ≤ L) (hη : 0 < η)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θB + H.card * L) ≤ η / 2)
    (n : ℕ) (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (hsuccess : historySuccessful h) (hgood : historyGood H F L h)
    (hA : η * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ (A n h).card)
    (a : EmbeddingState W V) (ha : a ∈ (prescribedGreedyStep Φ A H B L n h).support) :
    ∃ f : EmbeddingExtension (Φ n), a = chosenEmbedding f.val ∧ f ∈ A n h ∧
      f ∈ legalExtensions (Φ n) H (historyForbidden H B F h) := by
  classical
  have hs := candidateLegalExtensions_nonempty (Φ n) H (historyForbidden H B F h) (A n h)
    (historyForbidden_bounded H B h hB hL hgood) (by positivity) hη hnpos hA hsmall
  unfold prescribedGreedyStep at ha
  rw [if_pos ⟨hsuccess, hgood⟩, dif_pos hs] at ha
  obtain ⟨f, hf, hfa⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  refine ⟨f, hfa.symm, ?_⟩
  apply (mem_candidateLegalExtensions _ _ _ _ _).mp
  simpa only [PMF.support_uniformOfFinset, Finset.mem_coe] using hf

end Arxiv2411_18291
