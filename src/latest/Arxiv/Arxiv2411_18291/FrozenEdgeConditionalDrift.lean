import Arxiv.Arxiv2411_18291.FrozenEdgeProcess

/-! # Conditional drift of the actual frozen edge process -/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem edgeIncrement_condExp_sum (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    (probability r H)[edgeIncrement H e c i | Filtration.piLE i] =ᵐ[probability r H]
      fun ω => (∑ Q ∈ remainingCliques r H (trajectoryCliques ω i),
        edgeStepValue H e c i (frestrictLe i ω) Q) /
          (remainingCliques r H (trajectoryCliques ω i)).card :=
  condExp_chosen_step H (edgeStepValue H e c i)

theorem edgeIncrement_condExp_of_removed (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    ∀ᵐ ω ∂probability r H, e ∈ cliqueSupport r (trajectoryCliques ω i) →
      (probability r H)[edgeIncrement H e c i | Filtration.piLE i] ω = 0 := by
  filter_upwards [edgeIncrement_condExp_sum H e c i] with ω hω
  intro he
  rw [hω]
  simp only [edgeStepValue, historyCliques_prefix, if_pos he, sum_const_zero, zero_div]

theorem edgeIncrement_condExp_of_alive (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      e ∉ cliqueSupport r (trajectoryCliques ω i) → R.Nonempty →
        (probability r H)[edgeIncrement H e c i | Filtration.piLE i] ω =
          -(∑ Q ∈ R, (frozenEdgeLoss R e Q : ℝ)) / R.card -
            (1 - ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) / R.card) * (c (i + 1) - c i) := by
  filter_upwards [edgeIncrement_condExp_sum H e c i] with ω hω
  dsimp only
  intro he hR
  rw [hω]
  simpa only [edgeStepValue, historyCliques_prefix, if_neg he] using
    frozenTrackingIncrement_average (remainingCliques r H (trajectoryCliques ω i)) hR e
      (c (i + 1) - c i)

theorem edgeIncrement_condExp_abs_sum (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    (probability r H)[fun ω => |edgeIncrement H e c i ω| | Filtration.piLE i]
      =ᵐ[probability r H] fun ω =>
        (∑ Q ∈ remainingCliques r H (trajectoryCliques ω i),
          |edgeStepValue H e c i (frestrictLe i ω) Q|) /
            (remainingCliques r H (trajectoryCliques ω i)).card := by
  have heq : (fun ω => |edgeIncrement H e c i ω|) =
      fun ω => Option.elim (ω (i + 1)) 0
        (fun Q => |edgeStepValue H e c i (frestrictLe i ω) Q|) := by
    funext ω
    cases hω : ω (i + 1) <;> simp [edgeIncrement, hω]
  rw [heq]
  exact condExp_chosen_step H (fun h Q => |edgeStepValue H e c i h Q|)

theorem edgeIncrement_condExp_abs_of_removed (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    ∀ᵐ ω ∂probability r H, e ∈ cliqueSupport r (trajectoryCliques ω i) →
      (probability r H)[fun ω => |edgeIncrement H e c i ω| | Filtration.piLE i] ω = 0 := by
  filter_upwards [edgeIncrement_condExp_abs_sum H e c i] with ω hω
  intro he
  rw [hω]
  simp only [edgeStepValue, historyCliques_prefix, if_pos he, abs_zero, sum_const_zero, zero_div]

theorem edgeIncrement_condExp_abs_of_alive (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      e ∉ cliqueSupport r (trajectoryCliques ω i) → R.Nonempty →
        (probability r H)[fun ω => |edgeIncrement H e c i ω| | Filtration.piLE i] ω ≤
          (∑ Q ∈ R, (frozenEdgeLoss R e Q : ℝ)) / R.card + |c (i + 1) - c i| := by
  filter_upwards [edgeIncrement_condExp_abs_sum H e c i] with ω hω
  dsimp only
  intro he hR
  rw [hω]
  simpa only [edgeStepValue, historyCliques_prefix, if_neg he] using
    frozenTrackingIncrement_abs_average_le (remainingCliques r H (trajectoryCliques ω i)) hR e
      (c (i + 1) - c i)

end Arxiv2411_18291.CliqueRemovalProcess
