import Arxiv.Arxiv2411_18291.CliqueCountConditionalDrift

/-! # A finite-horizon variance budget for the available-clique count -/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem cliqueCountIncrement_condVar_le (H : Finset (Block V q)) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ D)
    (c : ℕ → ℝ) (i : ℕ) :
    Var[cliqueCountIncrement r H c i; probability r H | Filtration.piLE i]
      ≤ᵐ[probability r H] fun _ => ((q.choose r : ℝ) * D + |c (i + 1) - c i|) ^ 2 := by
  apply conditional_variance_le_sq_bound (Filtration.piLE.le i)
    ((cliqueCountIncrement_stronglyMeasurable H c i).mono (Filtration.piLE.le (i + 1)))
  exact ae_of_all _ fun ω => cliqueCountIncrement_abs_bound H D hD hd c i ω

theorem cliqueCountIncrement_variance_budget (H : Finset (Block V q)) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ D)
    (c : ℕ → ℝ) (n : ℕ) (B : ℝ) (hc : ∀ i < n, |c (i + 1) - c i| ≤ B) :
    ∀ᵐ ω ∂probability r H, ∀ j ≤ n,
      (∑ i ∈ range j, Var[cliqueCountIncrement r H c i; probability r H | Filtration.piLE i] ω)
        ≤ n * ((q.choose r : ℝ) * D + B) ^ 2 := by
  filter_upwards [ae_all_iff.mpr (fun i => cliqueCountIncrement_condVar_le H D hD hd c i)]
    with ω hω
  intro j hj
  calc
    _ ≤ ∑ _i ∈ range j, ((q.choose r : ℝ) * D + B) ^ 2 := by
      apply sum_le_sum
      intro i hi
      exact (hω i).trans (pow_le_pow_left₀ (by positivity)
        (add_le_add le_rfl (hc i ((mem_range.mp hi).trans_le hj))) 2)
    _ = (j : ℝ) * ((q.choose r : ℝ) * D + B) ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (sq_nonneg _)

end Arxiv2411_18291.CliqueRemovalProcess
