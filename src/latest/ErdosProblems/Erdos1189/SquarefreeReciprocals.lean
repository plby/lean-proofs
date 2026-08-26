/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The reciprocal sum of squarefree seeds.
Informal argument: the proved quarter-density bound and finite Abel summation.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.SquarefreeSupply
import ErdosProblems.Erdos1189.ReciprocalAbel

namespace Erdos1189

open Finset

lemma initialSum_squarefree (N : ℕ) :
    initialSum (fun n => if Squarefree n then 1 else 0) N =
      ((squarefreeUpto N).card : ℝ) := by
  simp [initialSum_eq_sum_Ioc, squarefreeUpto]

lemma squarefree_reciprocal_sum (N : ℕ) :
    (∑ i ∈ range N, (if Squarefree (i + 1) then 1 else 0 : ℝ) / (i + 1 : ℝ)) =
      ∑ d ∈ squarefreeUpto N, (d : ℝ)⁻¹ := by
  rw [reciprocal_sum_eq_sum_Ioc (fun n => if Squarefree n then 1 else 0)]
  simp only [ite_div, one_div, zero_div, squarefreeUpto, sum_filter]

/-- A squarefree harmonic sum is at least one quarter of the full harmonic sum. -/
theorem squarefree_reciprocals_ge_quarter_harmonic (N : ℕ) :
    (1 / 4 : ℝ) * (harmonic N : ℝ) ≤ ∑ d ∈ squarefreeUpto N, (d : ℝ)⁻¹ := by
  rw [← squarefree_reciprocal_sum]
  apply reciprocal_lower_of_prefix (f := fun n => if Squarefree n then 1 else 0)
  intro n _
  rw [initialSum_squarefree]
  have h : (n : ℝ) ≤ 4 * (squarefreeUpto n).card := by
    exact_mod_cast squarefree_count_quarter n
  linarith

theorem squarefree_reciprocals_ge_quarter_log {q : ℕ} (hq : 0 < q) :
    (1 / 4 : ℝ) * Real.log q ≤ ∑ d ∈ squarefreeUpto (q - 1), (d : ℝ)⁻¹ := by
  have hlog := log_add_one_le_harmonic (q - 1)
  rw [Nat.sub_add_cancel hq] at hlog
  exact (mul_le_mul_of_nonneg_left hlog (by norm_num)).trans
    (squarefree_reciprocals_ge_quarter_harmonic (q - 1))

end Erdos1189
