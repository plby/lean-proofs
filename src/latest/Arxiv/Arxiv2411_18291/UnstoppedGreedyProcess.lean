import Arxiv.Arxiv2411_18291.FiniteHistoryAgreement
import Arxiv.Arxiv2411_18291.GreedyHighProbability

/-!
# Removing the degree stop from the greedy algorithm

The ordinary process stops only after an abort or when no legal embedding
exists. On the event that its chosen family is bounded, every earlier
degree is below the cap. The ordinary and degree-stopped processes therefore
give this event exactly the same probability.
-/

open Finset MeasureTheory ProbabilityTheory Preorder Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

omit [Fintype W] in
theorem greedyFamilyEvent_congr_prefix (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) {ω ω' : ℕ → EmbeddingState W V}
    (hh : frestrictLe t ω = frestrictLe t ω') :
    ω ∈ greedyFamilyEvent Φ H B L t ↔ ω' ∈ greedyFamilyEvent Φ H B L t := by
  have hc (i : Fin t) : ω (i + 1) = ω' (i + 1) :=
    congrFun hh ⟨(i : ℕ) + 1, mem_Iic.mpr (Nat.succ_le_of_lt i.isLt)⟩
  constructor
  · rintro ⟨Ψ, hΨ, hmatch⟩
    exact ⟨Ψ, hΨ, fun i => (hc i).symm.trans (hmatch i)⟩
  · rintro ⟨Ψ, hΨ, hmatch⟩
    exact ⟨Ψ, hΨ, fun i => (hc i).trans (hmatch i)⟩

omit [Fintype W] in
theorem greedyFamilyEvent_historyGood (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) {ω : ℕ → EmbeddingState W V}
    (hω : ω ∈ greedyFamilyEvent Φ H B L t) :
    historyGood H F L (frestrictLe t ω) := by
  obtain ⟨Ψ, hΨ, hmatch⟩ := hω
  intro e he S
  rw [historyDegree_prefix]
  have hh := hΨ.bounded e he S
  change (familyDegree (fun i : Fin t => mapBlock (Ψ i).val e) S.val : ℝ) < _ at hh
  rw [familyDegree_eq_trajectoryDegree (fun i => (Ψ i).val) ω hmatch] at hh
  exact hh

def unstoppedGreedyStep (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (n : ℕ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n) : PMF (EmbeddingState W V) := by
  classical
  exact if historySuccessful h then
    if hs : (legalExtensions (Φ n) H (historyForbidden H B F h)).Nonempty then
      (uniformLegalExtension (Φ n) H (historyForbidden H B F h) hs).map
        (fun f => chosenEmbedding f.val)
    else PMF.pure (abortedEmbedding W V)
  else PMF.pure (abortedEmbedding W V)

def unstoppedGreedyProbability (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) : Measure (ℕ → EmbeddingState W V) :=
  FiniteHistoryProcess.probability (abortedEmbedding W V) (unstoppedGreedyStep Φ H B)

instance unstoppedGreedyProbability_isProbability (Φ : ℕ → F ↪ V)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) :
    IsProbabilityMeasure (unstoppedGreedyProbability Φ H B) :=
  FiniteHistoryProcess.probability_isProbability (abortedEmbedding W V)
    (unstoppedGreedyStep Φ H B)

theorem unstoppedGreedyStep_eq_of_good (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (n : ℕ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (hgood : historyGood H F L h) :
    unstoppedGreedyStep Φ H B n h = greedyStep Φ H B L n h := by
  classical
  simp only [unstoppedGreedyStep, greedyStep, hgood, and_true]

theorem unstopped_greedy_family_probability_eq (Φ : ℕ → F ↪ V)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) :
    (unstoppedGreedyProbability Φ H B).real (greedyFamilyEvent Φ H B L t) =
      (greedyProbability Φ H B L).real (greedyFamilyEvent Φ H B L t) := by
  apply congrArg ENNReal.toReal
  apply FiniteHistoryProcess.probability_event_eq_of_prefix_agreement
    (abortedEmbedding W V) (unstoppedGreedyStep Φ H B) (greedyStep Φ H B L) t
    (fun ω => ω ∈ greedyFamilyEvent Φ H B L t)
  · intro ω ω' hh
    exact greedyFamilyEvent_congr_prefix Φ H B L t hh
  · intro ω hω i hi
    apply unstoppedGreedyStep_eq_of_good
    exact historyGood_prefix_mono H F L ω hi.le (greedyFamilyEvent_historyGood Φ H B L t hω)

theorem unstopped_greedy_family_success_probability (Φ : ℕ → F ↪ V)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ : ℝ}
    (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θ + H.card * (4 * (r + 1).factorial * θ)) ≤ 1 / 4)
    (t : ℕ) (hA : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    1 - H.card * Fintype.card (Block V r) *
        Real.exp (-(2 * (r + 1).factorial * θ * Fintype.card V / 3)) ≤
      (unstoppedGreedyProbability Φ H B).real
        (greedyFamilyEvent Φ H B (4 * (r + 1).factorial * θ) t) := by
  rw [unstopped_greedy_family_probability_eq]
  exact greedy_family_success_probability Φ H B hB hθ hn hnpos hsmall t hA hroots

theorem eventually_unstopped_greedy_success_probability (H : Hypergraph W (r + 1))
    (hA : IsAdmissible H F) {ρ β : ℝ} (hρ : ρ < 1) (hβ : β < 1 - ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n,
      ∀ B : Hypergraph (Fin n) (r + 1), ∀ θ : ℝ,
        (n : ℝ) ^ (-ρ) ≤ θ → θ ≤ greedyDensityBound H.card r →
        IsGraphBounded B θ →
        (∀ f ∈ H, ∀ hf : f.val ⊆ F,
          IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) →
        1 - Real.exp (-((n : ℝ) ^ β)) <
          (unstoppedGreedyProbability Φ H B).real
            (greedyFamilyEvent Φ H B (4 * (r + 1).factorial * θ) t) := by
  filter_upwards [eventually_greedy_success_probability H hA hρ hβ] with n hn
  intro t Φ B θ hlower hupper hB hroots
  rw [unstopped_greedy_family_probability_eq]
  exact hn t Φ B θ hlower hupper hB hroots

/-- Corrected Lemma 5.5 with its output constant and a conservative upper density bound. -/
theorem eventually_greedy_paper_probability_corrected (H : Hypergraph W (r + 1))
    (hA : IsAdmissible H F) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ Φ : ℕ → F ↪ Fin n,
      ∀ B : Hypergraph (Fin n) (r + 1), ∀ θ : ℝ,
        (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ → θ ≤ greedyDensityBound H.card r →
        IsGraphBounded B θ →
        (∀ f ∈ H, ∀ hf : f.val ⊆ F,
          IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) →
        1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
          (unstoppedGreedyProbability Φ H B).real
            (allEdgesGreedyFamilyEvent Φ H B
              ((2 : ℝ) ^ (r + 2) * (r + 1).factorial * θ) t) := by
  filter_upwards [eventually_unstopped_greedy_success_probability H hA
    (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 / 10 : ℝ) < 1 - 1 / 2)] with n hn
  intro t Φ B θ hlower hupper hB hroots
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlower
  obtain ⟨hθL, hL⟩ := greedy_paper_output_bound r hθ
  rw [allEdgesGreedyFamilyEvent_eq Φ H B t (hθL.trans hL) hroots]
  exact (hn t Φ B θ hlower hupper hB hroots).trans_le
    (measureReal_mono (greedyFamilyEvent_mono Φ H B t hL))

end Arxiv2411_18291
