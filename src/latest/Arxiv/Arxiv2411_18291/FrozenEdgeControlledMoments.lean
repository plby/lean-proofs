import Arxiv.Arxiv2411_18291.FrozenEdgeValue

/-! # Drift and variance of the frozen process under current degree bounds -/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem edgeIncrement_condExp_bounds (hqr : r < q) (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) (dmin dmax : ℝ) :
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      let d := ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) / R.card
      let k := ((q.choose r - 1 : ℕ) : ℝ)
      let C := ((q.choose r : ℝ) ^ 2 + q.choose r) * (Fintype.card V : ℝ) ^ (q - r - 1)
      e ∉ cliqueSupport r (trajectoryCliques ω i) → R.Nonempty →
      (∀ f : Block V r, (R.filter fun Q => f.val ⊆ Q.val).Nonempty →
        dmin ≤ ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
          ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ dmax) →
      -(d * k * dmax) - (1 - d) * (c (i + 1) - c i) ≤
          (probability r H)[edgeIncrement H e c i | Filtration.piLE i] ω ∧
        (probability r H)[edgeIncrement H e c i | Filtration.piLE i] ω ≤
          -(d * (k * dmin - C)) - (1 - d) * (c (i + 1) - c i) := by
  filter_upwards [edgeIncrement_condExp_of_alive H e c i] with ω hω
  dsimp only
  intro he hR hd
  rw [hω he hR]
  obtain ⟨hlo, hhi⟩ := frozenEdgeLoss_average_of_degree_bounds hqr
    (remainingCliques r H (trajectoryCliques ω i)) hR e hd
  constructor
  · simpa only [neg_div] using sub_le_sub (neg_le_neg hhi) le_rfl
  · simpa only [neg_div] using sub_le_sub (neg_le_neg hlo) le_rfl

theorem edgeIncrement_condVar_of_degree_bounds (hqr : r < q) (H : Finset (Block V q))
    (e : Block V r) (c : ℕ → ℝ) (i : ℕ) (dmin dmax : ℝ) :
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      let d := ((R.filter fun Q => e.val ⊆ Q.val).card : ℝ) / R.card
      let k := ((q.choose r - 1 : ℕ) : ℝ)
      e ∉ cliqueSupport r (trajectoryCliques ω i) → R.Nonempty →
      (∀ f : Block V r, (R.filter fun Q => f.val ⊆ Q.val).Nonempty →
        dmin ≤ ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ∧
          ((R.filter fun Q => f.val ⊆ Q.val).card : ℝ) ≤ dmax) →
      Var[edgeIncrement H e c i; probability r H | Filtration.piLE i] ω ≤
        ((q.choose r : ℝ) * (Fintype.card V : ℝ) ^ (q - r - 1) + |c (i + 1) - c i|) *
          (d * k * dmax + |c (i + 1) - c i|) := by
  filter_upwards [edgeIncrement_condVar_of_alive hqr H e c i] with ω hω
  dsimp only
  intro he hR hd
  have hhi := (frozenEdgeLoss_average_of_degree_bounds hqr
    (remainingCliques r H (trajectoryCliques ω i)) hR e hd).2
  exact (hω he hR).trans
    (mul_le_mul_of_nonneg_left (add_le_add hhi le_rfl) (by positivity))

end Arxiv2411_18291.CliqueRemovalProcess
