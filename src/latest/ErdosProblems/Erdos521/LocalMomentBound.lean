/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Local root-count moments with an explicit finite-degree remainder.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.TailMomentIntegral
import ErdosProblems.Erdos521.LocalMomentSeries

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem localRootCount_le (ε : ℕ → ℝ) (n : ℕ) (x r : ℝ) : localRootCount ε n x r ≤ n :=
  (Finset.card_filter_le _ _).trans (rootCount_le ε n)

theorem localRootCount_pow_integrable (n p : ℕ) (x r : ℝ) :
    Integrable (fun ε ↦ (localRootCount ε n x r : ℝ) ^ p) sequenceLaw :=
  bounded_nat_pow_integrable sequenceLaw (localRootCount_aemeasurable n x r) n p
    (fun ε ↦ localRootCount_le ε n x r)

theorem integral_localRootCount_pow_le (n p J : ℕ) (hJ : 8 ≤ J) {x : ℝ}
    (hx : 9 / 10 ≤ x) (hx₁ : x < 1) (hgap : 32 * (J : ℝ) ≤ n * (1 - x)) :
    (∫ ε, (localRootCount ε n x ((1 - x) / 8) : ℝ) ^ p ∂sequenceLaw) ≤
      16 ^ p + localMomentSeries p + (n : ℝ) ^ p * localTailConstant * Real.exp (-localTailRate * J) := by
  have h := integral_nat_pow_le_tail_sum sequenceLaw
    (localRootCount_aemeasurable n x ((1 - x) / 8)) n J p
    (fun ε ↦ localRootCount_le ε n x ((1 - x) / 8))
  have htail := localRootCount_exponential_tail n J hJ hx hx₁ hgap
  have hsum : (∑ j ∈ Finset.Ico 8 J, (2 * ((j : ℝ) + 1)) ^ p *
      sequenceLaw.real {ε | 2 * j ≤ localRootCount ε n x ((1 - x) / 8)}) ≤
      ∑ j ∈ Finset.Ico 8 J, (2 * ((j : ℝ) + 1)) ^ p * localTailConstant *
        Real.exp (-localTailRate * j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjgap : 32 * (j : ℝ) ≤ n * (1 - x) :=
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.mem_Ico.mp hj).2.le)
        (by norm_num : (0 : ℝ) ≤ 32)).trans hgap
    have hprob := localRootCount_exponential_tail n j (Finset.mem_Ico.mp hj).1 hx hx₁ hjgap
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprob
      (by positivity : 0 ≤ (2 * ((j : ℝ) + 1)) ^ p)
  have hlast := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ (n : ℝ) ^ p)
  have hseries := local_moment_sum_le_series p J
  nlinarith

end Erdos521
