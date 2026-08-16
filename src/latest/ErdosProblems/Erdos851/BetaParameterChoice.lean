/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.BetaSieveFundamental

/-!
# Choosing the beta-sieve depth

The concrete fundamental lemma has two numerical side conditions.  The
starting depth must dominate the fixed logarithmic Mertens constant, and its
quarter-geometric tail must be below the requested relative error.  Both
conditions hold simultaneously at a sufficiently large natural depth.
-/

open Filter
open scoped Topology

namespace Erdos851

/-- A single beta depth makes both the logarithmic Rosser condition and the
geometric boundary error as small as required. -/
theorem exists_betaDepth
    {A theta : ℝ} (_hA : 1 ≤ A) (htheta : 0 < theta) :
    ∃ S : ℕ, 101 ≤ S ∧
      Real.log A ≤ 2 * ((S - 100 : ℕ) : ℝ) / 99 ∧
      (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) < theta := by
  have hlinear : Tendsto (fun r : ℕ ↦ (2 / 99 : ℝ) * (r : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 99)
  have hlog : ∀ᶠ r : ℕ in atTop,
      Real.log A ≤ 2 * (r : ℝ) / 99 := by
    have h := hlinear.eventually_ge_atTop (Real.log A)
    filter_upwards [h] with r hr
    nlinarith
  have htailTendsto : Tendsto
      (fun r : ℕ ↦ (4 * A / 3) * (1 / 4 : ℝ) ^ r)
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).const_mul (4 * A / 3)
  have htail : ∀ᶠ r : ℕ in atTop,
      (4 * A / 3) * (1 / 4 : ℝ) ^ r < theta :=
    (tendsto_order.1 htailTendsto).2 theta htheta
  have hexists : ∃ r : ℕ,
      1 ≤ r ∧ Real.log A ≤ 2 * (r : ℝ) / 99 ∧
        (4 * A / 3) * (1 / 4 : ℝ) ^ r < theta :=
    (eventually_ge_atTop 1 |>.and (hlog.and htail)).exists
  obtain ⟨r, hr, hlogr, htailr⟩ := hexists
  refine ⟨r + 100, by omega, ?_, ?_⟩
  · simpa using hlogr
  · simpa using htailr

end Erdos851
