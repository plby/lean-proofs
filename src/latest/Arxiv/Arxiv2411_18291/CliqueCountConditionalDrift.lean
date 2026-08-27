import Arxiv.Arxiv2411_18291.CliqueCountProcess

/-! # Conditional drift of the actual available-clique count -/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r i : ℕ}

theorem condExp_neg_chosen_step_sub_const (H : Finset (Block V q))
    (f : FiniteHistoryProcess.History (State V q) i → Block V q → ℝ) (δ : ℝ) :
    (probability r H)[fun ω => -Option.elim (ω (i + 1)) 0 (f (frestrictLe i ω)) - δ |
      Filtration.piLE i] =ᵐ[probability r H] fun ω =>
        -(∑ Q ∈ remainingCliques r H (trajectoryCliques ω i), f (frestrictLe i ω) Q) /
          (remainingCliques r H (trajectoryCliques ω i)).card - δ := by
  let X : (ℕ → State V q) → ℝ := fun ω =>
    Option.elim (ω (i + 1)) 0 (f (frestrictLe i ω))
  have hX : Integrable X (probability r H) :=
    FiniteHistoryProcess.integrable_step (aborted V q) (step r H) i
      (fun h a => Option.elim a 0 (f h))
  have hs := condExp_sub hX.neg (integrable_const (μ := probability r H) δ)
    (Filtration.piLE i)
  have hn := condExp_neg (μ := probability r H) X (Filtration.piLE i)
  filter_upwards [hs, hn, condExp_chosen_step H f] with ω hs hn ha
  change (probability r H)[fun ω => -X ω - δ | Filtration.piLE i] ω = _ at hs ⊢
  simp only [Pi.sub_apply, Pi.neg_apply, condExp_const (Filtration.piLE.le i)] at hs hn
  rw [hs, hn]
  change -(probability r H)[X | Filtration.piLE i] ω - δ = _
  rw [ha, neg_div]

theorem cliqueCountIncrement_condExp (H : Finset (Block V q)) (c : ℕ → ℝ) (i : ℕ) :
    (probability r H)[cliqueCountIncrement r H c i | Filtration.piLE i]
      =ᵐ[probability r H] fun ω =>
        -(∑ Q ∈ remainingCliques r H (trajectoryCliques ω i),
          ((cliqueNeighborhood r (remainingCliques r H (trajectoryCliques ω i)) Q).card : ℝ)) /
          (remainingCliques r H (trajectoryCliques ω i)).card - (c (i + 1) - c i) := by
  have h := condExp_neg_chosen_step_sub_const (r := r) H
    (cliqueLossStep r H i) (c (i + 1) - c i)
  unfold cliqueCountIncrement
  simpa only [cliqueLossStep, historyCliques_prefix] using h

theorem cliqueCountIncrement_condExp_bounds (hqr : r < q) (G : Hypergraph V r)
    (H : Finset (Block V q)) (hHG : ∀ Q ∈ H, cliqueEdges r Q ⊆ G)
    (c : ℕ → ℝ) (i : ℕ) (m δ : ℝ) :
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      let E := G \ cliqueSupport r (trajectoryCliques ω i)
      R.Nonempty → E.Nonempty →
      (∀ e ∈ E, |((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) - m| ≤ δ) →
      -((q.choose r : ℝ) ^ 2 * R.card / E.card) - E.card * δ ^ 2 / R.card -
          (c (i + 1) - c i) ≤
          (probability r H)[cliqueCountIncrement r H c i | Filtration.piLE i] ω ∧
        (probability r H)[cliqueCountIncrement r H c i | Filtration.piLE i] ω ≤
          -((q.choose r : ℝ) ^ 2 * R.card / E.card) +
            (q.choose r : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (q - r - 1) - (c (i + 1) - c i) := by
  filter_upwards [cliqueCountIncrement_condExp H c i] with ω hω
  dsimp only
  intro hR hE hd
  let R := remainingCliques r H (trajectoryCliques ω i)
  let E := G \ cliqueSupport r (trajectoryCliques ω i)
  have hRE : ∀ Q ∈ R, cliqueEdges r Q ⊆ E := by
    intro Q hQ
    dsimp only [R] at hQ
    rw [remainingCliques_eq_graph_filter G H (trajectoryCliques ω i) hHG] at hQ
    exact (mem_filter.mp hQ).2
  obtain ⟨hlo, hhi⟩ := cliqueRemoval_average_loss_of_degree_deviation hqr E hE R hR hRE m δ hd
  rw [hω]
  dsimp only [R, E] at hlo hhi
  simp only [neg_div]
  constructor <;> linarith only [hlo, hhi]

end Arxiv2411_18291.CliqueRemovalProcess
