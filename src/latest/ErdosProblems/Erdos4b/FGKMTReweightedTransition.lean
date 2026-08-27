/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTReweightedEdges

/-! # A coupled finite transition preserving the previous state marginal -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α Ξ : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def transitionMass (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (W : Ξ → Finset α)
    (τ : ℝ) (ρ : Ξ → ℝ) (s : Ξ) (ξ : I → Option Ω) : ℝ :=
  ρ s * ∏ i, F.reweightedMass P (W s) τ i (ξ i)

theorem transitionMass_nonneg (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (hP : ∀ v ∈ F.vertices, 0 < P v) (W : Ξ → Finset α) {τ : ℝ} (hτ : τ < 1)
    (ρ : Ξ → ℝ) (hρ : ∀ s, 0 ≤ ρ s) (s : Ξ) (ξ : I → Option Ω) :
    0 ≤ F.transitionMass P W τ ρ s ξ := by
  exact mul_nonneg (hρ s)
    (Finset.prod_nonneg fun i _hi => F.reweightedMass_nonneg hP (W s) hτ i (ξ i))

variable [DecidableEq I]

theorem transitionMass_marginal (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (W : Ξ → Finset α) {τ : ℝ} (hτ : τ < 1) (ρ : Ξ → ℝ) (s : Ξ) :
    (∑ ξ : I → Option Ω, F.transitionMass P W τ ρ s ξ) = ρ s := by
  have hnorm := assignmentWeight_sum (fun i o => F.reweightedMass P (W s) τ i o)
    (F.reweightedMass_sum_one P (W s) hτ)
  unfold transitionMass
  rw [← Finset.mul_sum, hnorm, mul_one]

variable [Fintype Ξ]

theorem transitionMass_sum_one (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (W : Ξ → Finset α) {τ : ℝ} (hτ : τ < 1) (ρ : Ξ → ℝ) (hρ : ∑ s, ρ s = 1) :
    (∑ s, ∑ ξ : I → Option Ω, F.transitionMass P W τ ρ s ξ) = 1 := by
  simp_rw [F.transitionMass_marginal P W hτ ρ]
  exact hρ

end

end Erdos4b.FGKMT.FiniteEdgeFamily
