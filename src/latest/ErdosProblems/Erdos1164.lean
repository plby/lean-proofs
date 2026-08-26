import ErdosProblems.Erdos1164.LowerInProbability
import ErdosProblems.Erdos1164.UpperInProbability

/-!
# Erdős problem 1164: the completely covered disc

For planar simple random walk started at the origin, `coveredRadius s n` is
the largest integer radius whose closed Euclidean lattice disc has been
visited by time `n`. The theorem below proves the two-sided order in
probability of its logarithm, with constants depending on the exceptional
probability and with both bounds holding at every sufficiently large time.

The lower tail uses return excursions and a union bound. The upper tail
uses well-separated targets, a positive logarithmic origin-visit cost
between targets, and a finite permutation-record generating function.
The deterministic-order weighted stopping-time argument is proved before
averaging over permutations, so it never conditions a Markov step on the
future trajectory. All spatial, return, and record estimates are discharged.

This development proves order in probability, not the sharp distributional
limit. For the known exponential limit, `exp (-4*x)` is the survival function,
whereas the CDF is `1 - exp (-4*x)` for positive `x`.

`Real.log 0 = 0` is Lean's convention. The lower-tail theorem explicitly
controls the radius-zero event, so this convention does not weaken the
asymptotic statement.
-/

open Filter MeasureTheory

namespace Erdos1164

/-- **Erdős 1164.** The logarithm of the pathwise completely covered disc
radius has two-sided order `sqrt (log n)` in probability, unconditionally. -/
theorem erdos_1164 :
    ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ᶠ n : ℕ in atTop,
        walkLaw.real {s | Real.log (coveredRadius s n : ℝ) <
          a * Real.sqrt (Real.log (n : ℝ))} < ε ∧
        walkLaw.real {s | b * Real.sqrt (Real.log (n : ℝ)) <
          Real.log (coveredRadius s n : ℝ)} < ε := by
  intro ε hε
  obtain ⟨a, ha, hlower⟩ := logRadius_lower_in_probability ε hε
  obtain ⟨b, _hb, hupper⟩ := logRadius_upper_in_probability ε hε
  refine ⟨a, max a b, ha, le_max_left _ _, ?_⟩
  filter_upwards [hlower, hupper] with n hnlow hnup
  refine ⟨hnlow, ?_⟩
  have hsub : {s : WalkPath | max a b * sqrtLogTime n < logRadius s n} ⊆
      {s | b * sqrtLogTime n < logRadius s n} := by
    intro s hs
    exact (mul_le_mul_of_nonneg_right (le_max_right a b) (sqrtLogTime_nonneg n)).trans_lt hs
  exact (measureReal_mono (μ := walkLaw) hsub (by finiteness)).trans_lt hnup

/-- Expanded statement of the main result, with the actual pathwise radius
and both probability tails visible in the theorem type. -/
theorem coveredRadius_log_order :
    ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ᶠ n : ℕ in atTop,
        walkLaw.real {s | Real.log (coveredRadius s n : ℝ) <
          a * Real.sqrt (Real.log (n : ℝ))} < ε ∧
        walkLaw.real {s | b * Real.sqrt (Real.log (n : ℝ)) <
          Real.log (coveredRadius s n : ℝ)} < ε :=
  erdos_1164

end Erdos1164
