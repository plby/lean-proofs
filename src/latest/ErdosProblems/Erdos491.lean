/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos491.Homogenization
import ErdosProblems.Erdos491.Rigidity

/-!
# Erdős Problem 491

The proof uses dyadic homogenization, finite affine valuation averages, and a
Chinese-remainder second-moment estimate. The original function need only be
additive on coprime arguments, and the residual bound is uniform in `n`.
-/

open Filter Asymptotics

namespace Erdos491

/-- A quantitative form of the conclusion, including every positive integer
and allowing arbitrary values at prime powers in the original function. -/
theorem logarithmic_uniform_bound {f : ℕ → ℝ} {M : ℝ}
    (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M) :
    ∃ c : ℝ, ∀ n : ℕ, 0 < n → |f n - c * Real.log (n : ℝ)| ≤ 2 * M := by
  obtain ⟨g, hg, happrox, hggap⟩ := homogenization hf hM hgap
  obtain ⟨c, hc⟩ := completely_additive_bounded_gap_rigidity g (5 * M) hg
    (by positivity) hggap
  refine ⟨c, fun n hn ↦ ?_⟩
  simpa only [hc n hn] using happrox n hn

end Erdos491

/-- Erdős Problem 491: bounded consecutive differences force a logarithmic
main term with a bounded residual. No rigidity or approximation assumption
is left as a hypothesis. -/
theorem erdos_491 (f : ℕ → ℝ)
    (hf : ∀ a b : ℕ, a.Coprime b → f (a * b) = f a + f b)
    (hgap : ∃ C : ℝ, ∀ n : ℕ, |f (n + 1) - f n| < C) :
    ∃ c : ℝ,
      (fun n : ℕ ↦ f n - c * Real.log (n : ℝ)) =O[atTop]
        (fun _ : ℕ ↦ (1 : ℝ)) := by
  obtain ⟨M, hM, hbound⟩ := Erdos491.exists_nonneg_adjacent_bound_of_strict hgap
  have hf' : Erdos491.CoprimeAdditive f := by
    intro a b hab
    exact hf a b hab
  obtain ⟨c, hc⟩ := Erdos491.logarithmic_uniform_bound hf' hM hbound
  exact Erdos491.hasLogarithmicMainTerm_of_explicit_bound
    ⟨c, 2 * M, by positivity, hc⟩
