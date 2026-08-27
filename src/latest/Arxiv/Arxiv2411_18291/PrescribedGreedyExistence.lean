import Arxiv.Arxiv2411_18291.PrescribedGreedyConcentration
import Arxiv.Arxiv2411_18291.PrescribedGreedySuccess

/-!
# Existence of bounded greedy families within prescribed candidates

The input root density `θ`, forbidden density `θB`, and candidate density
`η` are separate. A finite numerical criterion gives a family of actual
embeddings satisfying the candidate restrictions, including restrictions
depending on earlier choices.
-/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

theorem exists_prescribed_greedy_family (Φ : ℕ → F ↪ V) (A : CandidateFamilies Φ)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ θB η : ℝ}
    (hB : IsGraphBounded B θB) (hθ : 0 ≤ θ) (hθB : 0 ≤ θB) (hη : 0 < η)
    (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θB + H.card * (4 * (r + 1).factorial * θ / η)) ≤ η / 2)
    (t : ℕ) (hA : HasCandidateLowerBound Φ A H (4 * (r + 1).factorial * θ / η) η t)
    (hadm : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ)
    (hfailure : H.card * Fintype.card (Block V r) *
      Real.exp (-((2 * (r + 1).factorial * θ * Fintype.card V / η) / 3)) < 1) :
    ∃ ω : ℕ → EmbeddingState W V, ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsGreedyFamily (fun i => Φ i) H B Ψ (4 * (r + 1).factorial * θ / η) ∧
      (∀ i : Fin t, Ψ i ∈ A i (frestrictLe (i : ℕ) ω)) ∧
      ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val := by
  classical
  let L : ℝ := 4 * (r + 1).factorial * θ / η
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbadlt : (prescribedGreedyProbability Φ A H B L).real
      {ω | ¬ historyGood H F L (frestrictLe t ω)} < 1 := by
    have hevent : {ω | ¬ historyGood H F L (frestrictLe t ω)} =
        {ω | ∃ e ∈ newEdges F H, ∃ S : Block V r,
          (4 * (r + 1).factorial * θ / η) * Fintype.card V ≤
            (trajectoryDegree ω t e S.val : ℝ)} := by
      ext ω
      simp only [historyGood, not_forall, not_lt, historyDegree_prefix, L,
        Set.mem_ofPred_eq]
      constructor <;> rintro ⟨e, he, S, hS⟩ <;> exact ⟨e, he, S, hS⟩
    rw [hevent]
    exact (prescribedGreedy_all_degrees_failure Φ A H B hB hθ hθB hL hη hnpos hsmall
      t hA hadm hroots).trans_lt hfailure
  obtain ⟨ω, hωsupport, hωgood⟩ := FiniteHistoryProcess.exists_supported_path
    (abortedEmbedding W V) (prescribedGreedyStep Φ A H B L)
    (fun ω => historyGood H F L (frestrictLe t ω)) hbadlt
  obtain ⟨Ψ, hΨ, hmem, hmatch⟩ := extract_prescribed_greedy_family Φ A H B L ω t
    (prescribed_steps_of_final_good Φ A H B hB hθB hL hη hnpos hsmall t hA ω hωsupport hωgood)
    hωgood
  exact ⟨ω, Ψ, hΨ, hmem, hmatch⟩

/-- The fixed-candidate version of the general construction. -/
theorem exists_greedy_family_in_candidates (Φ : ℕ → F ↪ V)
    (A : (i : ℕ) → Finset (EmbeddingExtension (Φ i)))
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ θB η : ℝ}
    (hB : IsGraphBounded B θB) (hθ : 0 ≤ θ) (hθB : 0 ≤ θB) (hη : 0 < η)
    (hnpos : 0 < Fintype.card V)
    (hsmall : H.card * (θB + H.card * (4 * (r + 1).factorial * θ / η)) ≤ η / 2)
    (t : ℕ) (hA : ∀ i < t,
      η * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ (A i).card)
    (hadm : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ)
    (hfailure : H.card * Fintype.card (Block V r) *
      Real.exp (-((2 * (r + 1).factorial * θ * Fintype.card V / η) / 3)) < 1) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsGreedyFamily (fun i => Φ i) H B Ψ (4 * (r + 1).factorial * θ / η) ∧
      ∀ i : Fin t, Ψ i ∈ A i := by
  have hsize : HasCandidateLowerBound Φ (fun i _ => A i) H
      (4 * (r + 1).factorial * θ / η) η t := fun i hi _ _ _ => hA i hi
  obtain ⟨ω, Ψ, hΨ, hmem, _⟩ := exists_prescribed_greedy_family Φ (fun i _ => A i) H B
    hB hθ hθB hη hnpos hsmall t hsize hadm hroots hfailure
  exact ⟨Ψ, hΨ, hmem⟩

end Arxiv2411_18291
