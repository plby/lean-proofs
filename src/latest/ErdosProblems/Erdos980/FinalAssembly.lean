/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.GoodPrimeBridge
import ErdosProblems.Erdos980.ElliottTail.FinalAssembly

/-!
# Final analytic assembly for Erdős problem 980

This file specializes the abstract uniform-integrability theorem to the exact
least-`k`-th-power-nonresidue model.  It also isolates a positivity argument:
every eligible prime contributes at least two, so the positive density of the
eligible primes forces the limiting mean to be positive.
-/

namespace Erdos980

open scoped BigOperators
open Asymptotics Filter

noncomputable section

/-- The exact sum in Erdős problem 980, with strict natural cutoff. -/
def leastKthPowerNonresidueSum (k x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range x).filter Nat.Prime,
    (leastKthPowerNonresidue k p : ℝ)

/-- The number of eligible primes strictly below the natural cutoff. -/
noncomputable def eligiblePrimeCount (k x : ℕ) : ℝ := by
  classical
  exact (((Finset.range x).filter (Eligible k)).card : ℝ)

@[simp]
theorem leastKthPowerNonresidueSum_eq_primeValueSum (k x : ℕ) :
    leastKthPowerNonresidueSum k x =
      primeValueSum (leastKthPowerNonresidueModel k) x := by
  rw [primeValueSum_leastKthPowerNonresidueModel]
  rfl

/-- Every eligible prime contributes at least two to the exact sum. -/
theorem two_mul_eligiblePrimeCount_le_sum
    {k : ℕ} (hk : 2 ≤ k) (x : ℕ) :
    2 * eligiblePrimeCount k x ≤ leastKthPowerNonresidueSum k x := by
  classical
  rw [leastKthPowerNonresidueSum, eligiblePrimeCount]
  calc
    2 * (((Finset.range x).filter (Eligible k)).card : ℝ) =
        ∑ p ∈ (Finset.range x).filter (Eligible k), (2 : ℝ) := by
          simp [nsmul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ (Finset.range x).filter (Eligible k),
          (leastKthPowerNonresidue k p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have helig : Eligible k p := (Finset.mem_filter.mp hp).2
      exact_mod_cast (leastKthPowerNonresidue_prime hk helig).two_le
    _ ≤ ∑ p ∈ (Finset.range x).filter Nat.Prime,
          (leastKthPowerNonresidue k p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1⟩
      · intro p _ _
        positivity

/-- Ratio-limit form of Elliott's assembly.  Summability of the defining
series is a consequence of the uniform tail, not an assumption. -/
theorem leastKthPowerNonresidueSum_normalized_tendsto
    {k : ℕ} (hk : 2 ≤ k)
    (hpattern : ∀ j,
      Tendsto
        (fun x ↦ primePatternCount (leastKthPowerNonresidueModel k) j x /
          erdos980Scale x)
        atTop (nhds (patternWeight k j)))
    (htail : UniformlyNegligibleTail
      (primeValueTail (leastKthPowerNonresidueModel k)) erdos980Scale) :
    Tendsto
      (fun x ↦ leastKthPowerNonresidueSum k x / erdos980Scale x)
      atTop (nhds (elliottConstant k)) := by
  have h :=
    primeValueSum_normalized_tendsto_of_pattern_densities_and_uniformTail_of_nonneg
      (leastKthPowerNonresidueModel k) erdos980Scale (patternWeight k)
      erdos980Scale_eventually_pos
      (fun j ↦ by
        rw [leastKthPowerNonresidueModel_enumeration]
        positivity)
      hpattern
      (primeValueTail_nonneg_leastKthPowerNonresidueModel hk)
      htail
  simpa [leastKthPowerNonresidueSum_eq_primeValueSum,
    elliottConstant, constantTerm] using h

/-- Positive density of eligible primes forces positivity of Elliott's
limiting mean. -/
theorem elliottConstant_pos_of_eligiblePrimeDensity
    {k : ℕ} (hk : 2 ≤ k)
    (hpattern : ∀ j,
      Tendsto
        (fun x ↦ primePatternCount (leastKthPowerNonresidueModel k) j x /
          erdos980Scale x)
        atTop (nhds (patternWeight k j)))
    (htail : UniformlyNegligibleTail
      (primeValueTail (leastKthPowerNonresidueModel k)) erdos980Scale)
    (d : ℝ)
    (heligible : Tendsto
      (fun x ↦ eligiblePrimeCount k x / erdos980Scale x)
      atTop (nhds d))
    (hd : 0 < d) :
    0 < elliottConstant k := by
  have htotal := leastKthPowerNonresidueSum_normalized_tendsto hk hpattern htail
  have hlower : Tendsto
      (fun x ↦ (2 * eligiblePrimeCount k x) / erdos980Scale x)
      atTop (nhds (2 * d)) := by
    simpa [mul_div_assoc] using tendsto_const_nhds.mul heligible
  apply normalized_limit_pos_of_eventually_le
    (leastKthPowerNonresidueSum k)
    (fun x ↦ 2 * eligiblePrimeCount k x)
    erdos980Scale (elliottConstant k) (2 * d)
    erdos980Scale_eventually_pos htotal hlower
  · exact Filter.Eventually.of_forall (two_mul_eligiblePrimeCount_le_sum hk)
  · positivity

/-- Exact asymptotic-equivalence form once fixed-pattern density, uniform
integrability, and positive eligible-prime density have been established. -/
theorem leastKthPowerNonresidueSum_isEquivalent
    {k : ℕ} (hk : 2 ≤ k)
    (hpattern : ∀ j,
      Tendsto
        (fun x ↦ primePatternCount (leastKthPowerNonresidueModel k) j x /
          erdos980Scale x)
        atTop (nhds (patternWeight k j)))
    (htail : UniformlyNegligibleTail
      (primeValueTail (leastKthPowerNonresidueModel k)) erdos980Scale)
    (d : ℝ)
    (heligible : Tendsto
      (fun x ↦ eligiblePrimeCount k x / erdos980Scale x)
      atTop (nhds d))
    (hd : 0 < d) :
    leastKthPowerNonresidueSum k ~[atTop]
      (fun x ↦ elliottConstant k * erdos980Scale x) := by
  apply primeValueSum_isEquivalent_of_pattern_densities_and_uniformTail_of_nonneg
    (leastKthPowerNonresidueModel k) erdos980Scale (patternWeight k)
    erdos980Scale_eventually_pos
  · intro j
    rw [leastKthPowerNonresidueModel_enumeration]
    positivity
  · exact hpattern
  · exact primeValueTail_nonneg_leastKthPowerNonresidueModel hk
  · exact htail
  · simpa [elliottConstant, constantTerm] using
      elliottConstant_pos_of_eligiblePrimeDensity
        hk hpattern htail d heligible hd

/-- All of the algebraic and fixed-pattern inputs for Elliott's theorem have
been discharged unconditionally.  Thus the single remaining analytic input,
the medium estimate for each prime exponent, implies the exact positive
asymptotic for every `k ≥ 2`. -/
theorem leastKthPowerNonresidueSum_isEquivalent_of_all_primeExponentMedium
    (hmedium : ∀ ell : ℕ, ell.Prime →
      ElliottTail.PrimeExponentMediumEstimate ell)
    (k : ℕ) (hk : 2 ≤ k) :
    0 < elliottConstant k ∧
      leastKthPowerNonresidueSum k ~[atTop]
        (fun x ↦ elliottConstant k * erdos980Scale x) := by
  have hpattern : ∀ j,
      Tendsto
        (fun x ↦ primePatternCount (leastKthPowerNonresidueModel k) j x /
          erdos980Scale x)
        atTop (nhds (patternWeight k j)) :=
    GoodPrimeBridge.primePatternCount_leastKthPowerNonresidueModel_ratio_tendsto hk
  have htail : UniformlyNegligibleTail
      (primeValueTail (leastKthPowerNonresidueModel k)) erdos980Scale := by
    exact ElliottTail.uniformlyNegligibleTail_of_all_primeExponentMedium
      hmedium k hk
  have heligible : Tendsto
      (fun x ↦ eligiblePrimeCount k x / erdos980Scale x)
      atTop (nhds (splittingDensity k 0)) := by
    simpa only [eligiblePrimeCount,
      GoodPrimeBridge.eligiblePrimeCountBridge] using
        GoodPrimeBridge.eligiblePrimeCountBridge_ratio_tendsto hk
  have hpositive := elliottConstant_pos_of_eligiblePrimeDensity
    hk hpattern htail (splittingDensity k 0) heligible
      (GoodPrimeBridge.splittingDensity_zero_pos k)
  exact ⟨hpositive,
    leastKthPowerNonresidueSum_isEquivalent hk hpattern htail
      (splittingDensity k 0) heligible
      (GoodPrimeBridge.splittingDensity_zero_pos k)⟩

end

end Erdos980
