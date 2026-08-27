import Arxiv.Arxiv2411_18291.FaceCountConditionalDrift
import Arxiv.Arxiv2411_18291.PredictableLossVariance

/-! # Conditional variance of face-degree increments without comparison errors -/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem faceCountIncrement_condVar_le (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (f : Block V r) (c : ℕ → ℝ) (i : ℕ) :
    Var[faceCountIncrement G f c i; probability (r + 1) H | Filtration.piLE i]
      ≤ᵐ[probability (r + 1) H] fun ω =>
        ((q - r : ℕ) : ℝ) *
          ((∑ Q ∈ remainingCliques (r + 1) H (trajectoryCliques ω i),
            (cliqueFaceLoss (G \ cliqueSupport (r + 1) (trajectoryCliques ω i)) f Q : ℝ)) /
            (remainingCliques (r + 1) H (trajectoryCliques ω i)).card) := by
  let X : (ℕ → State V q) → ℝ := fun ω =>
    Option.elim (ω (i + 1)) 0 (faceLossStep G f i (frestrictLe i ω))
  have hXm : StronglyMeasurable X :=
    (FiniteHistoryProcess.stronglyMeasurable_step (S := State V q) i
      (fun h a => Option.elim a 0 (faceLossStep G f i h))).mono (Filtration.piLE.le (i + 1))
  have hXb : ∀ᵐ ω ∂probability (r + 1) H, 0 ≤ X ω ∧ X ω ≤ ((q - r : ℕ) : ℝ) := by
    apply ae_of_all
    intro ω
    cases hω : ω (i + 1) with
    | none => simp only [X, hω, Option.elim_none]; exact ⟨le_rfl, Nat.cast_nonneg _⟩
    | some Q =>
      simp only [X, hω, Option.elim_some]
      exact ⟨faceLossStep_nonneg G f i (frestrictLe i ω) Q,
        faceLossStep_le G f i (frestrictLe i ω) Q⟩
  have hvar := conditional_variance_of_bounded_loss (Filtration.piLE.le i) hXm hXb
    (integrable_const (μ := probability (r + 1) H) (c (i + 1) - c i)) stronglyMeasurable_const
  filter_upwards [hvar, condExp_chosen_step (r := r + 1) H (faceLossStep G f i)]
    with ω hv hm
  change Var[faceCountIncrement G f c i; probability (r + 1) H | Filtration.piLE i] ω ≤
    ((q - r : ℕ) : ℝ) * (probability (r + 1) H)[X | Filtration.piLE i] ω at hv
  rw [hm] at hv
  simpa only [faceLossStep, historyCliques_prefix] using hv

theorem faceCountIncrement_condVar_of_degree_bound (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (hH : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (f : Block V r) (c : ℕ → ℝ) (i : ℕ) (D : ℝ) :
    ∀ᵐ ω ∂probability (r + 1) H,
      let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
      let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
      (∀ e ∈ E, ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ D) →
      Var[faceCountIncrement G f c i; probability (r + 1) H | Filtration.piLE i] ω ≤
        ((q - r : ℕ) : ℝ) * (((E.filter fun e => f.val ⊆ e.val).card : ℝ) * D / R.card) := by
  filter_upwards [faceCountIncrement_condVar_le G H f c i] with ω hω
  dsimp only
  intro hd
  have hb := (cliqueFaceLoss_average_bounds _ _
    (remainingCliques_clique_subset G H hH (trajectoryCliques ω i)) f 0 D
    (fun e he => ⟨Nat.cast_nonneg _, hd e he⟩)).2
  exact hω.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))

end Arxiv2411_18291.CliqueRemovalProcess
