/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Summable polynomial weights for the local root-count exponential tail.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LocalTailDecay

namespace Erdos521

open scoped BigOperators

theorem local_moment_series_summable (p : ℕ) :
    Summable (fun j : ℕ ↦ (2 * ((j : ℝ) + 1)) ^ p * localTailConstant *
      Real.exp (-localTailRate * j)) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul p localTailRate_pos)
  have h' := h.mul_left ((2 : ℝ) ^ p * localTailConstant * Real.exp localTailRate)
  apply h'.congr
  intro j
  push_cast
  rw [mul_pow]
  have he : Real.exp localTailRate * Real.exp (-localTailRate * ((j : ℝ) + 1)) =
      Real.exp (-localTailRate * j) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ((2 : ℝ) ^ p * localTailConstant * Real.exp localTailRate) *
        (((j : ℝ) + 1) ^ p * Real.exp (-localTailRate * ((j : ℝ) + 1))) =
        (2 : ℝ) ^ p * ((j : ℝ) + 1) ^ p * localTailConstant *
          (Real.exp localTailRate * Real.exp (-localTailRate * ((j : ℝ) + 1))) := by ring
    _ = _ := by rw [he]

noncomputable def localMomentSeries (p : ℕ) : ℝ :=
  ∑' j : ℕ, (2 * ((j : ℝ) + 1)) ^ p * localTailConstant * Real.exp (-localTailRate * j)

theorem localMomentSeries_nonneg (p : ℕ) : 0 ≤ localMomentSeries p :=
  tsum_nonneg (fun _ ↦ by
    have := localTailConstant_pos
    positivity)

theorem local_moment_sum_le_series (p J : ℕ) :
    (∑ j ∈ Finset.Ico 8 J, (2 * ((j : ℝ) + 1)) ^ p * localTailConstant *
      Real.exp (-localTailRate * j)) ≤ localMomentSeries p :=
  Summable.sum_le_tsum _ (fun _ _ ↦ by
    have := localTailConstant_pos
    positivity) (local_moment_series_summable p)

end Erdos521
