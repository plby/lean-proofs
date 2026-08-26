/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The almost-sure bulk repulsion estimate for Littlewood polynomials.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RootRepulsion

namespace Erdos521

open MeasureTheory Filter

theorem ae_root_repulsion :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 < B ∧ ∀ᵐ ε ∂sequenceLaw, ∀ᶠ n : ℕ in atTop,
      ∀ x ∈ Set.Icc (9 / 10 : ℝ) (endpointCenter C n),
        (n : ℝ) ^ (-B) < max |(polynomial ε n).eval x| |(polynomial ε n).derivative.eval x| := by
  obtain ⟨C, hC, B, hB, hprob⟩ := root_repulsion_probability 2 (by norm_num)
  let E := fun n : ℕ ↦ smallValueDerivativeEvent n (9 / 10) (endpointCenter C n) ((n : ℝ) ^ (-B))
  have hs : Summable (fun n ↦ sequenceLaw.real (E n)) := by
    have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
    apply hp.of_norm_bounded_eventually_nat
    filter_upwards [hprob] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using hn
  have h := ae_eventually_notMem_of_summable_real sequenceLaw E hs
  refine ⟨C, hC, B, hB, ?_⟩
  filter_upwards [h] with ε hε
  filter_upwards [hε] with n hn
  intro x hx
  by_contra hh
  have hmax := le_of_not_gt hh
  exact hn ⟨x, hx, (le_max_left _ _).trans hmax, (le_max_right _ _).trans hmax⟩

end Erdos521
