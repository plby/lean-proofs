import Arxiv.Arxiv2411_18291.FaceCountProcess

/-! # Exact conditional drift of face degrees -/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem faceCountIncrement_condExp (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (f : Block V r) (c : ℕ → ℝ) (i : ℕ) :
    (probability (r + 1) H)[faceCountIncrement G f c i | Filtration.piLE i]
      =ᵐ[probability (r + 1) H] fun ω =>
        -(∑ Q ∈ remainingCliques (r + 1) H (trajectoryCliques ω i),
          (cliqueFaceLoss (G \ cliqueSupport (r + 1) (trajectoryCliques ω i)) f Q : ℝ)) /
          (remainingCliques (r + 1) H (trajectoryCliques ω i)).card - (c (i + 1) - c i) := by
  have h := condExp_neg_chosen_step_sub_const (r := r + 1) H
    (faceLossStep G f i) (c (i + 1) - c i)
  unfold faceCountIncrement
  simpa only [faceLossStep, historyCliques_prefix] using h

theorem remainingCliques_clique_subset (G : Hypergraph V r) (H : Finset (Block V q))
    (hH : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) (D : Finset (Block V q)) :
    ∀ Q ∈ remainingCliques r H D, cliqueEdges r Q ⊆ G \ cliqueSupport r D := by
  intro Q hQ
  rw [remainingCliques_eq_graph_filter G H D hH] at hQ
  exact (mem_filter.mp hQ).2

theorem faceCountIncrement_condExp_degrees (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (hH : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (f : Block V r) (c : ℕ → ℝ) (i : ℕ) :
    (probability (r + 1) H)[faceCountIncrement G f c i | Filtration.piLE i]
      =ᵐ[probability (r + 1) H] fun ω =>
        let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
        let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i);
        -(∑ e ∈ E.filter (fun e => f.val ⊆ e.val),
          ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ)) / R.card - (c (i + 1) - c i) := by
  filter_upwards [faceCountIncrement_condExp G H f c i] with ω hω
  dsimp only
  rw [hω, sum_cliqueFaceLoss _ _ (remainingCliques_clique_subset G H hH (trajectoryCliques ω i))]

theorem faceCountIncrement_condExp_bounds (G : Hypergraph V (r + 1))
    (H : Finset (Block V q)) (hH : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (f : Block V r) (c : ℕ → ℝ) (i : ℕ) (dmin dmax : ℝ) :
    ∀ᵐ ω ∂probability (r + 1) H,
      let R := remainingCliques (r + 1) H (trajectoryCliques ω i)
      let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
      let d := ((E.filter fun e => f.val ⊆ e.val).card : ℝ)
      (∀ e ∈ E, dmin ≤ ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ∧
        ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ dmax) →
      -(d * dmax / R.card) - (c (i + 1) - c i) ≤
          (probability (r + 1) H)[faceCountIncrement G f c i | Filtration.piLE i] ω ∧
        (probability (r + 1) H)[faceCountIncrement G f c i | Filtration.piLE i] ω ≤
          -(d * dmin / R.card) - (c (i + 1) - c i) := by
  filter_upwards [faceCountIncrement_condExp G H f c i] with ω hω
  dsimp only
  intro hd
  obtain ⟨hlo, hhi⟩ := cliqueFaceLoss_average_bounds _ _
    (remainingCliques_clique_subset G H hH (trajectoryCliques ω i)) f dmin dmax hd
  rw [hω, neg_div]
  exact ⟨sub_le_sub (neg_le_neg hhi) le_rfl, sub_le_sub (neg_le_neg hlo) le_rfl⟩

end Arxiv2411_18291.CliqueRemovalProcess
