import Arxiv.Arxiv2411_18291.UnstoppedGreedyProcess
import Arxiv.Arxiv2411_18291.PrescribedGreedyHighProbability

/-! # The ordinary greedy process with history-dependent candidate restrictions -/

open Finset MeasureTheory ProbabilityTheory Preorder Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

omit [Fintype W] in
theorem prescribedGreedyFamilyEvent_congr_prefix (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ)
    {ω ω' : ℕ → EmbeddingState W V} (hh : frestrictLe t ω = frestrictLe t ω') :
    ω ∈ prescribedGreedyFamilyEvent Φ A H B L t ↔
      ω' ∈ prescribedGreedyFamilyEvent Φ A H B L t := by
  have hc (i : Fin t) : ω (i + 1) = ω' (i + 1) :=
    congrFun hh ⟨(i : ℕ) + 1, mem_Iic.mpr (Nat.succ_le_of_lt i.isLt)⟩
  have hp (i : Fin t) : frestrictLe (i : ℕ) ω = frestrictLe (i : ℕ) ω' :=
    congrArg (frestrictLe₂ (π := fun _ => EmbeddingState W V) i.isLt.le) hh
  constructor
  · rintro ⟨Ψ, hΨ, hmem, hmatch⟩
    refine ⟨Ψ, hΨ, ?_, fun i => (hc i).symm.trans (hmatch i)⟩
    intro i
    rw [← hp i]
    exact hmem i
  · rintro ⟨Ψ, hΨ, hmem, hmatch⟩
    refine ⟨Ψ, hΨ, ?_, fun i => (hc i).trans (hmatch i)⟩
    intro i
    rw [hp i]
    exact hmem i

omit [Fintype W] in
theorem prescribedGreedyFamilyEvent_historyGood (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ)
    {ω : ℕ → EmbeddingState W V} (hω : ω ∈ prescribedGreedyFamilyEvent Φ A H B L t) :
    historyGood H F L (frestrictLe t ω) := by
  obtain ⟨Ψ, hΨ, _, hmatch⟩ := hω
  exact greedyFamilyEvent_historyGood Φ H B L t ⟨Ψ, hΨ, hmatch⟩

def unstoppedPrescribedGreedyStep (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (n : ℕ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n) : PMF (EmbeddingState W V) := by
  classical
  exact if historySuccessful h then
    if hs : (candidateLegalExtensions (Φ n) H (historyForbidden H B F h) (A n h)).Nonempty then
      (PMF.uniformOfFinset _ hs).map (fun f => chosenEmbedding f.val)
    else PMF.pure (abortedEmbedding W V)
  else PMF.pure (abortedEmbedding W V)

def unstoppedPrescribedGreedyProbability (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) :
    Measure (ℕ → EmbeddingState W V) :=
  FiniteHistoryProcess.probability (abortedEmbedding W V) (unstoppedPrescribedGreedyStep Φ A H B)

instance unstoppedPrescribedGreedyProbability_isProbability (Φ : ℕ → F ↪ V)
    (A : CandidateFamilies Φ) (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) :
    IsProbabilityMeasure (unstoppedPrescribedGreedyProbability Φ A H B) :=
  FiniteHistoryProcess.probability_isProbability (abortedEmbedding W V)
    (unstoppedPrescribedGreedyStep Φ A H B)

theorem unstoppedPrescribedGreedyStep_eq_of_good (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (n : ℕ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (hgood : historyGood H F L h) :
    unstoppedPrescribedGreedyStep Φ A H B n h = prescribedGreedyStep Φ A H B L n h := by
  classical
  simp only [unstoppedPrescribedGreedyStep, prescribedGreedyStep, hgood, and_true]

theorem unstopped_prescribed_greedy_family_probability_eq (Φ : ℕ → F ↪ V)
    (A : CandidateFamilies Φ) (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1))
    (L : ℝ) (t : ℕ) :
    (unstoppedPrescribedGreedyProbability Φ A H B).real
        (prescribedGreedyFamilyEvent Φ A H B L t) =
      (prescribedGreedyProbability Φ A H B L).real
        (prescribedGreedyFamilyEvent Φ A H B L t) := by
  apply congrArg ENNReal.toReal
  apply FiniteHistoryProcess.probability_event_eq_of_prefix_agreement
    (abortedEmbedding W V) (unstoppedPrescribedGreedyStep Φ A H B)
    (prescribedGreedyStep Φ A H B L) t (fun ω => ω ∈ prescribedGreedyFamilyEvent Φ A H B L t)
  · intro ω ω' hh
    exact prescribedGreedyFamilyEvent_congr_prefix Φ A H B L t hh
  · intro ω hω i hi
    apply unstoppedPrescribedGreedyStep_eq_of_good
    exact historyGood_prefix_mono H F L ω hi.le
      (prescribedGreedyFamilyEvent_historyGood Φ A H B L t hω)

theorem unstopped_prescribed_greedy_family_success_probability
    (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ θB η : ℝ}
    (hB : IsGraphBounded B θB) (hθ : 0 ≤ θ) (hθB : 0 ≤ θB) (hη : 0 < η)
    (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θB + H.card * (4 * (r + 1).factorial * θ / η)) ≤ η / 2)
    (t : ℕ) (hA : HasCandidateLowerBound Φ A H (4 * (r + 1).factorial * θ / η) η t)
    (hadm : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    1 - H.card * Fintype.card (Block V r) *
        Real.exp (-((2 * (r + 1).factorial * θ * Fintype.card V / η) / 3)) ≤
      (unstoppedPrescribedGreedyProbability Φ A H B).real
        (prescribedGreedyFamilyEvent Φ A H B (4 * (r + 1).factorial * θ / η) t) := by
  rw [unstopped_prescribed_greedy_family_probability_eq]
  exact prescribed_greedy_family_success_probability Φ A H B hB hθ hθB hη hnpos
    hsmall t hA hadm hroots

theorem eventually_unstopped_prescribed_greedy_success_probability
    (H : Hypergraph W (r + 1)) (hadm : IsAdmissible H F) {a b c β : ℝ}
    (hba : 2 * a < b) (hca : a < c) (hb1 : b - a < 1) (hβ : β < 1 - (b - a)) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n, ∀ A : CandidateFamilies Φ,
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B ((n : ℝ) ^ (-c)) →
      (∀ f ∈ H, ∀ hf : f.val ⊆ F,
        IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) ((n : ℝ) ^ (-b))) →
      HasCandidateLowerBound Φ A H (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)))
        ((n : ℝ) ^ (-a)) t →
      1 - Real.exp (-((n : ℝ) ^ β)) <
        (unstoppedPrescribedGreedyProbability Φ A H B).real
          (prescribedGreedyFamilyEvent Φ A H B
            (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a))) t) := by
  filter_upwards [eventually_prescribed_greedy_success_probability H hadm hba hca hb1 hβ]
    with n hn
  intro t Φ A B hB hroots hA
  rw [unstopped_prescribed_greedy_family_probability_eq]
  exact hn t Φ A B hB hroots hA

end Arxiv2411_18291
