/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The expectation of a sign grid is the sum of its sign-change probabilities.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SignGridLowerBound
import ErdosProblems.Erdos521.NatTailMoments

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem measurable_powerSum (N : ℕ) (x : ℝ) : Measurable (fun ε : ℕ → ℝ ↦ powerSum ε N x) := by
  unfold powerSum
  fun_prop

theorem measurable_polynomial_eval (n : ℕ) (x : ℝ) :
    Measurable (fun ε : ℕ → ℝ ↦ (polynomial ε n).eval x) := by
  simp_rw [polynomial_eval]
  exact measurable_powerSum _ _

theorem signChange_le_one (u v : ℝ) : signChange u v ≤ 1 := by
  unfold signChange
  split_ifs <;> omega

theorem gridSignChanges_le (ε : ℕ → ℝ) (n : ℕ) (g : ℕ → ℝ) (N : ℕ) :
    gridSignChanges ε n g N ≤ N := by
  calc
    gridSignChanges ε n g N ≤ ∑ _i ∈ Finset.range N, 1 :=
      Finset.sum_le_sum (fun _ _ ↦ signChange_le_one _ _)
    _ = N := by simp

theorem gridSignChanges_pow_integrable (n p : ℕ) (g : ℕ → ℝ) (N : ℕ) :
    Integrable (fun ε ↦ (gridSignChanges ε n g N : ℝ) ^ p) sequenceLaw :=
  bounded_nat_pow_integrable sequenceLaw (gridSignChanges_aemeasurable n g N) N p
    (fun ε ↦ gridSignChanges_le ε n g N)

theorem polynomial_signChange_integrable (n : ℕ) (a b : ℝ) :
    Integrable (fun ε ↦ (signChange ((polynomial ε n).eval a) ((polynomial ε n).eval b) : ℝ)) sequenceLaw := by
  have hE : MeasurableSet {ε : ℕ → ℝ | (polynomial ε n).eval a * (polynomial ε n).eval b < 0} :=
    measurableSet_lt ((measurable_polynomial_eval n a).mul (measurable_polynomial_eval n b)) measurable_const
  have hmeas : Measurable (fun ε ↦ signChange ((polynomial ε n).eval a) ((polynomial ε n).eval b)) :=
    Measurable.ite hE measurable_const measurable_const
  simpa only [pow_one] using bounded_nat_pow_integrable sequenceLaw hmeas.aemeasurable 1 1
    (fun ε ↦ signChange_le_one _ _)

theorem integral_polynomial_signChange (n : ℕ) (a b : ℝ) :
    (∫ ε, (signChange ((polynomial ε n).eval a) ((polynomial ε n).eval b) : ℝ) ∂sequenceLaw) =
      sequenceLaw.real {ε | powerSum ε (n + 1) a * powerSum ε (n + 1) b < 0} := by
  have hE : MeasurableSet {ε : ℕ → ℝ | powerSum ε (n + 1) a * powerSum ε (n + 1) b < 0} :=
    measurableSet_lt ((measurable_powerSum _ a).mul (measurable_powerSum _ b)) measurable_const
  rw [← integral_indicator_one hE]
  apply integral_congr_ae
  filter_upwards [] with ε
  by_cases h : powerSum ε (n + 1) a * powerSum ε (n + 1) b < 0 <;>
    simp [signChange, polynomial_eval, h]

theorem integral_gridSignChanges (n N : ℕ) (g : ℕ → ℝ) :
    (∫ ε, (gridSignChanges ε n g N : ℝ) ∂sequenceLaw) =
      ∑ i ∈ Finset.range N, sequenceLaw.real {ε |
        powerSum ε (n + 1) (g i) * powerSum ε (n + 1) (g (i + 1)) < 0} := by
  simp only [gridSignChanges, Nat.cast_sum]
  rw [integral_finsetSum (Finset.range N) (fun i _ ↦ polynomial_signChange_integrable n (g i) (g (i + 1)))]
  simp only [integral_polynomial_signChange]

end Erdos521
