import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Elementary assembly for Erdős Problem 823

This file contains the exact passage from pointwise density of equal-`σ`
quotients to the sequences asked for in the problem.  The number-theoretic
density theorem is proved in the other files of this development.
-/

namespace Erdos823

open Filter Topology
open scoped ArithmeticFunction.sigma

/-- Pointwise density of positive quotients belonging to one fiber of `σ`. -/
def SigmaQuotientsDense : Prop :=
  ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε →
    ∃ n m : ℕ,
      0 < n ∧ 0 < m ∧
      σ 1 n = σ 1 m ∧
      |(n : ℝ) / (m : ℝ) - α| < ε

/-- Pointwise density supplies a sequence of positive equal-`σ` pairs
converging to any prescribed positive real number. -/
theorem exists_sigma_sequences_of_dense
    (hdense : SigmaQuotientsDense) {α : ℝ} (hα : 0 < α) :
    ∃ n m : ℕ → ℕ,
      (∀ k, 0 < n k) ∧
      (∀ k, 0 < m k) ∧
      (∀ k, σ 1 (n k) = σ 1 (m k)) ∧
      Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (nhds α) := by
  have hε : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1 : ℕ) := by
    intro k
    positivity
  choose n m hn hm hσ happ using
    fun k : ℕ => hdense α hα (1 / (k + 1 : ℕ)) (hε k)
  refine ⟨n, m, hn, hm, hσ, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hεpos
  have hevent : ∀ᶠ k : ℕ in atTop, (1 : ℝ) / (k + 1 : ℕ) < ε := by
    have hlim : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_order.1 hlim).2 ε hεpos
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  exact (happ k).trans (hN k hk)

end Erdos823
