import Arxiv.Arxiv2411_18291.PrescribedGreedyProcess
import Arxiv.Arxiv2411_18291.GreedyDegreeConcentration

/-!
# Simultaneous degree bounds with restricted candidate families

The input root density and the forbidden graph density are separate
parameters. Candidate density `η` scales the cumulative conditional-mean
budget by `η⁻¹`, and the adaptive inequality applies to the actual process.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

theorem prescribedGreedyDegree_tail (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ θB L η : ℝ}
    (hB : IsGraphBounded B θB) (hθ : 0 ≤ θ) (hθB : 0 ≤ θB) (hL : 0 ≤ L) (hη : 0 < η)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θB + H.card * L) ≤ η / 2)
    (t : ℕ) (hA : HasCandidateLowerBound Φ A H L η t)
    (e f : Block W (r + 1)) (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (he : ¬ e.val ⊆ F)
    (hroot : IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) (S : Block V r) :
    (prescribedGreedyProbability Φ A H B L).real {ω |
      (4 * (r + 1).factorial * θ / η) * Fintype.card V ≤ (trajectoryDegree ω t e S.val : ℝ)} ≤
      Real.exp (-((2 * (r + 1).factorial * θ * Fintype.card V / η) / 3)) := by
  have hbudget : (∑ i ∈ range t, rootFaceWeight (Φ i) e f hf S / η) ≤
      2 * (r + 1).factorial * θ * Fintype.card V / η := by
    rw [Finset.sum_range (fun i => rootFaceWeight (Φ i) e f hf S / η)]
    exact sum_rootFaceWeight_scaled_le (fun i : Fin t => Φ i) e f hf hroot hθ hη.le hnpos he S
  have ht := FiniteHistoryProcess.indicator_double_tail (abortedEmbedding W V)
    (prescribedGreedyStep Φ A H B L) (fun _ a => stateFaceIndicator a e S.val) t
    (fun i => rootFaceWeight (Φ i) e f hf S / η)
    (fun _ _ a => stateFaceIndicator_bounds a e S.val)
    (fun i hi h => prescribedGreedyStep_mean_le Φ A H B hB hθB hL hη hnpos hsmall
      t hA i hi h e f hf hcover S) hbudget
  have htwo : 2 * (2 * ((r + 1).factorial : ℝ) * θ * Fintype.card V / η) =
      (4 * (r + 1).factorial * θ / η) * Fintype.card V := by ring
  simpa only [prescribedGreedyProbability, trajectoryDegree_real, htwo] using ht

theorem prescribedGreedy_all_degrees_failure (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ θB L η : ℝ}
    (hB : IsGraphBounded B θB) (hθ : 0 ≤ θ) (hθB : 0 ≤ θB) (hL : 0 ≤ L) (hη : 0 < η)
    (hnpos : 0 < Fintype.card V) (hsmall : H.card * (θB + H.card * L) ≤ η / 2)
    (t : ℕ) (hA : HasCandidateLowerBound Φ A H L η t) (hadm : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    (prescribedGreedyProbability Φ A H B L).real {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
      (4 * (r + 1).factorial * θ / η) * Fintype.card V ≤ (trajectoryDegree ω t e S.val : ℝ)} ≤
      H.card * Fintype.card (Block V r) *
        Real.exp (-((2 * (r + 1).factorial * θ * Fintype.card V / η) / 3)) := by
  apply trajectoryDegree_failure_le H F _ t _ _ (Real.exp_pos _).le
  intro e he S
  obtain ⟨heH, heF⟩ := (mem_newEdges H e).mp he
  obtain ⟨f, hfH, hfF, hcover⟩ := hadm e heH heF
  exact prescribedGreedyDegree_tail Φ A H B hB hθ hθB hL hη hnpos hsmall t hA
    e f hfF hcover heF (hroots f hfH hfF) S

end Arxiv2411_18291
