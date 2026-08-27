import Arxiv.Arxiv2411_18291.FrozenEdgeConditionalDrift
import Arxiv.Arxiv2411_18291.ConditionalVarianceBounds

/-! # Conditional variance bounds for the actual frozen process -/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem edgeIncrement_condVar_le (hqr : r < q) (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    Var[edgeIncrement H e c i; probability r H | Filtration.piLE i] ≤ᵐ[probability r H]
      fun ω => ((q.choose r : ℝ) * (Fintype.card V : ℝ) ^ (q - r - 1) + |c (i + 1) - c i|) *
        (probability r H)[fun ω => |edgeIncrement H e c i ω| | Filtration.piLE i] ω := by
  apply conditional_variance_le_mul_abs_mean (Filtration.piLE.le i)
    ((edgeIncrement_stronglyMeasurable H e c i).mono (Filtration.piLE.le (i + 1)))
  exact ae_of_all _ fun ω => edgeIncrement_abs_bound hqr H e c i ω

theorem edgeIncrement_condVar_of_alive (hqr : r < q) (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    ∀ᵐ ω ∂probability r H,
      let R := remainingCliques r H (trajectoryCliques ω i)
      e ∉ cliqueSupport r (trajectoryCliques ω i) → R.Nonempty →
        Var[edgeIncrement H e c i; probability r H | Filtration.piLE i] ω ≤
          ((q.choose r : ℝ) * (Fintype.card V : ℝ) ^ (q - r - 1) + |c (i + 1) - c i|) *
            ((∑ Q ∈ R, (frozenEdgeLoss R e Q : ℝ)) / R.card + |c (i + 1) - c i|) := by
  filter_upwards [edgeIncrement_condVar_le hqr H e c i,
    edgeIncrement_condExp_abs_of_alive H e c i] with ω hvar habs
  dsimp only
  intro he hR
  exact hvar.trans (mul_le_mul_of_nonneg_left (habs he hR) (by positivity))

theorem edgeIncrement_condVar_of_removed (hqr : r < q) (H : Finset (Block V q))
    (e : Block V r) (c : ℕ → ℝ) (i : ℕ) :
    ∀ᵐ ω ∂probability r H, e ∈ cliqueSupport r (trajectoryCliques ω i) →
      Var[edgeIncrement H e c i; probability r H | Filtration.piLE i] ω = 0 := by
  filter_upwards [edgeIncrement_condVar_le hqr H e c i,
    edgeIncrement_condExp_abs_of_removed H e c i,
    conditional_variance_nonneg (X := edgeIncrement H e c i) (m := Filtration.piLE i)]
    with ω hvar habs hnonneg
  intro he
  rw [habs he, mul_zero] at hvar
  exact le_antisymm hvar hnonneg

end Arxiv2411_18291.CliqueRemovalProcess
