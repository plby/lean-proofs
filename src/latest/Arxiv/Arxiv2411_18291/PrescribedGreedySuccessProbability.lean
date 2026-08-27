import Arxiv.Arxiv2411_18291.GreedySuccessProbability
import Arxiv.Arxiv2411_18291.PrescribedGreedyExistence

/-! # Success probabilities retain the prescribed candidate restrictions -/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

def prescribedGreedyFamilyEvent (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) :
    Set (ℕ → EmbeddingState W V) :=
  {ω | ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
    IsGreedyFamily (fun i => Φ i) H B Ψ L ∧
      (∀ i : Fin t, Ψ i ∈ A i (frestrictLe (i : ℕ) ω)) ∧
        ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val}

omit [Fintype W] in
theorem measurableSet_prescribedGreedyFamilyEvent [Finite W]
    (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) :
    MeasurableSet (prescribedGreedyFamilyEvent Φ A H B L t) := by
  classical
  let : Fintype W := Fintype.ofFinite W
  unfold prescribedGreedyFamilyEvent
  simp only [Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro Ψ
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · by_cases h : IsGreedyFamily (fun i => Φ i) H B Ψ L <;> simp [h]
  · apply MeasurableSet.iInter
    intro i
    exact (Set.toFinite {h | Ψ i ∈ A i h}).measurableSet.preimage
      (measurable_frestrictLe (i : ℕ))
  · apply MeasurableSet.iInter
    intro i
    exact (measurableSet_singleton (chosenEmbedding (Ψ i).val)).preimage
      (measurable_pi_apply ((i : ℕ) + 1))

theorem prescribed_greedy_family_failure_probability
    (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ θB η : ℝ}
    (hB : IsGraphBounded B θB) (hθ : 0 ≤ θ) (hθB : 0 ≤ θB) (hη : 0 < η)
    (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θB + H.card * (4 * (r + 1).factorial * θ / η)) ≤ η / 2)
    (t : ℕ) (hA : HasCandidateLowerBound Φ A H (4 * (r + 1).factorial * θ / η) η t)
    (hadm : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    (prescribedGreedyProbability Φ A H B (4 * (r + 1).factorial * θ / η)).real
        (prescribedGreedyFamilyEvent Φ A H B (4 * (r + 1).factorial * θ / η) t)ᶜ ≤
      H.card * Fintype.card (Block V r) *
        Real.exp (-((2 * (r + 1).factorial * θ * Fintype.card V / η) / 3)) := by
  let L : ℝ := 4 * (r + 1).factorial * θ / η
  let P := prescribedGreedyProbability Φ A H B L
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hsupport : ∀ᵐ ω : ℕ → EmbeddingState W V ∂P, ∀ n,
      ω (n + 1) ∈ (prescribedGreedyStep Φ A H B L n (frestrictLe n ω)).support :=
    ae_all_iff.mpr fun n => FiniteHistoryProcess.next_mem_support
      (abortedEmbedding W V) (prescribedGreedyStep Φ A H B L) n
  have hsub : (prescribedGreedyFamilyEvent Φ A H B L t)ᶜ ≤ᵐ[P]
      {ω | ¬ historyGood H F L (frestrictLe t ω)} := by
    filter_upwards [hsupport] with ω hω
    intro hbad hgood
    have hsteps := prescribed_steps_of_final_good Φ A H B hB hθB hL hη hnpos hsmall
      t hA ω hω hgood
    exact hbad (extract_prescribed_greedy_family Φ A H B L ω t hsteps hgood)
  have hevent : {ω | ¬ historyGood H F L (frestrictLe t ω)} =
      {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
        (4 * (r + 1).factorial * θ / η) * Fintype.card V ≤
          (trajectoryDegree ω t e S.val : ℝ)} := by
    ext ω
    simp only [historyGood, not_forall, not_lt, historyDegree_prefix, L,
      Set.mem_ofPred_eq]
    constructor <;> rintro ⟨e, he, S, hS⟩ <;> exact ⟨e, he, S, hS⟩
  have hmono : P.real (prescribedGreedyFamilyEvent Φ A H B L t)ᶜ ≤
      P.real {ω | ¬ historyGood H F L (frestrictLe t ω)} :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)
  rw [hevent] at hmono
  exact hmono.trans (prescribedGreedy_all_degrees_failure Φ A H B hB hθ hθB hL hη
    hnpos hsmall t hA hadm hroots)

theorem prescribed_greedy_family_success_probability
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
      (prescribedGreedyProbability Φ A H B (4 * (r + 1).factorial * θ / η)).real
        (prescribedGreedyFamilyEvent Φ A H B (4 * (r + 1).factorial * θ / η) t) := by
  have hf := prescribed_greedy_family_failure_probability Φ A H B hB hθ hθB hη
    hnpos hsmall t hA hadm hroots
  rw [measureReal_compl (measurableSet_prescribedGreedyFamilyEvent Φ A H B _ t),
    probReal_univ] at hf
  linarith only [hf]

end Arxiv2411_18291
