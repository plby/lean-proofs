/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.Basic
import ErdosProblems.Erdos980.Assembly
import ErdosProblems.Erdos980.KummerPatterns

/-!
# The concrete prime-value model for Erdős problem 980

This file connects the total least-`k`-th-power-nonresidue function to the
abstract fixed-pattern assembly interface.  The zero value is represented by
`none`; every nonzero value is a rational prime and is represented by its
zero-based index in the increasing sequence of rational primes.
-/

namespace Erdos980

open Filter

noncomputable section

/-- The level of the least `k`-th-power nonresidue at `p`.  The totalized zero
case has no level.  A nonzero value has the unique level supplied by counting
the rational primes strictly below it. -/
def leastKthPowerNonresidueLevel (k p : ℕ) : Option ℕ :=
  let n := leastKthPowerNonresidue k p
  if n = 0 then none else some (Nat.count Nat.Prime n)

theorem leastKthPowerNonresidueLevel_eq_none_iff (k p : ℕ) :
    leastKthPowerNonresidueLevel k p = none ↔
      leastKthPowerNonresidue k p = 0 := by
  simp [leastKthPowerNonresidueLevel]

theorem leastKthPowerNonresidueLevel_eq_some_iff
    {k p j : ℕ} (hk : 2 ≤ k) :
    leastKthPowerNonresidueLevel k p = some j ↔
      leastKthPowerNonresidue k p = rationalPrime j := by
  let n := leastKthPowerNonresidue k p
  by_cases hn : n = 0
  · simp [leastKthPowerNonresidueLevel, n, hn,
      (rationalPrime_pos j).ne]
  · have helig : Eligible k p := by
      have h := (leastKthPowerNonresidue_eq_zero_iff k p).not.mp hn
      exact (not_not.mp h).2
    have hnprime : n.Prime := by
      exact leastKthPowerNonresidue_prime hk helig
    simp only [leastKthPowerNonresidueLevel, n, hn, if_false]
    constructor
    · intro h
      have hj : Nat.count Nat.Prime n = j := Option.some.inj h
      rw [← hj, rationalPrime, Nat.nth_count hnprime]
    · intro h
      apply Option.some.inj
      simpa [h, rationalPrime] using
        Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime j

/-- The exact abstract model associated to the least `k`-th-power
nonresidue. -/
def leastKthPowerNonresidueModel (k : ℕ) : PrimeValueModel where
  value p := (leastKthPowerNonresidue k p : ℝ)
  level p := leastKthPowerNonresidueLevel k p
  enumeration j := (rationalPrime j : ℝ)
  enumeration_mono := by
    intro i j hij
    change (rationalPrime i : ℝ) ≤ (rationalPrime j : ℝ)
    exact_mod_cast rationalPrime_strictMono.monotone hij
  value_spec p := by
    let n := leastKthPowerNonresidue k p
    by_cases hn : n = 0
    · simp [leastKthPowerNonresidueLevel, n, hn]
    · have helig : Eligible k p := by
        have h := (leastKthPowerNonresidue_eq_zero_iff k p).not.mp hn
        exact (not_not.mp h).2
      have hk : 2 ≤ k := by
        have h := (leastKthPowerNonresidue_eq_zero_iff k p).not.mp hn
        exact (not_not.mp h).1
      have hnprime : n.Prime := leastKthPowerNonresidue_prime hk helig
      simp only [leastKthPowerNonresidueLevel, n, hn, if_false]
      rw [rationalPrime, Nat.nth_count hnprime]

/-- A hypothesis-indexed spelling convenient in the final theorem, where
`2 ≤ k` is already in context. -/
abbrev leastNonresidueModel (k : ℕ) (_hk : 2 ≤ k) : PrimeValueModel :=
  leastKthPowerNonresidueModel k

@[simp]
theorem leastKthPowerNonresidueModel_value (k p : ℕ) :
    (leastKthPowerNonresidueModel k).value p =
      (leastKthPowerNonresidue k p : ℝ) := rfl

@[simp]
theorem leastKthPowerNonresidueModel_level (k p : ℕ) :
    (leastKthPowerNonresidueModel k).level p =
      leastKthPowerNonresidueLevel k p := rfl

@[simp]
theorem leastKthPowerNonresidueModel_enumeration (k j : ℕ) :
    (leastKthPowerNonresidueModel k).enumeration j =
      (rationalPrime j : ℝ) := rfl

/-- The modeled prime sum is definitionally the exact strict-cutoff sum in
Erdős problem 980. -/
theorem primeValueSum_leastKthPowerNonresidueModel (k x : ℕ) :
    primeValueSum (leastKthPowerNonresidueModel k) x =
      ∑ p ∈ (Finset.range x).filter Nat.Prime,
        (leastKthPowerNonresidue k p : ℝ) := by
  rfl

/-- The `j`th modeled pattern is exactly the event that the least nonresidue
is the `j`th rational prime. -/
theorem primePatternCount_leastKthPowerNonresidueModel
    {k : ℕ} (hk : 2 ≤ k) (j x : ℕ) :
    primePatternCount (leastKthPowerNonresidueModel k) j x =
      (((Finset.range x).filter
        (fun p ↦ p.Prime ∧
          leastKthPowerNonresidue k p = rationalPrime j)).card : ℝ) := by
  classical
  change
    (((Finset.range x).filter
      (fun p ↦ p.Prime ∧ leastKthPowerNonresidueLevel k p = some j)).card : ℝ) = _
  norm_cast
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [leastKthPowerNonresidueLevel_eq_some_iff hk]

/-- The primes below `x` occupying one fixed least-nonresidue level. -/
private def leastKthPowerNonresiduePatternPrimes
    (k j x : ℕ) : Finset ℕ :=
  (Finset.range x).filter
    (fun p ↦ p.Prime ∧ leastKthPowerNonresidueLevel k p = some j)

private theorem patternContribution_eq_sum
    {k : ℕ} (hk : 2 ≤ k) (j x : ℕ) :
    (leastKthPowerNonresidueModel k).enumeration j *
        primePatternCount (leastKthPowerNonresidueModel k) j x =
      ∑ p ∈ leastKthPowerNonresiduePatternPrimes k j x,
        (leastKthPowerNonresidue k p : ℝ) := by
  rw [leastKthPowerNonresidueModel_enumeration,
    primePatternCount_leastKthPowerNonresidueModel hk]
  let s := (Finset.range x).filter
    (fun p ↦ p.Prime ∧
      leastKthPowerNonresidue k p = rationalPrime j)
  change (rationalPrime j : ℝ) * (s.card : ℝ) =
    ∑ p ∈ leastKthPowerNonresiduePatternPrimes k j x,
      (leastKthPowerNonresidue k p : ℝ)
  have hs : leastKthPowerNonresiduePatternPrimes k j x = s := by
    ext p
    simp only [leastKthPowerNonresiduePatternPrimes, s,
      Finset.mem_filter, Finset.mem_range]
    rw [leastKthPowerNonresidueLevel_eq_some_iff hk]
  rw [hs]
  calc
    (rationalPrime j : ℝ) * (s.card : ℝ) =
        ∑ _p ∈ s, (rationalPrime j : ℝ) := by
      simp [nsmul_eq_mul, mul_comm]
    _ = ∑ p ∈ s, (leastKthPowerNonresidue k p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.2.symm

private theorem patternPrimeFinsets_pairwiseDisjoint
    (k M x : ℕ) :
    (↑(Finset.range M) : Set ℕ).PairwiseDisjoint
      (fun j ↦ leastKthPowerNonresiduePatternPrimes k j x) := by
  intro i hi j hj hij
  change Disjoint
    (leastKthPowerNonresiduePatternPrimes k i x)
    (leastKthPowerNonresiduePatternPrimes k j x)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hleveli := (Finset.mem_filter.mp hpi).2.2
  have hlevelj := (Finset.mem_filter.mp hpj).2.2
  exact hij (Option.some.inj (hleveli.symm.trans hlevelj))

private theorem primePatternHead_eq_sum_biUnion
    {k : ℕ} (hk : 2 ≤ k) (M x : ℕ) :
    primePatternHead (leastKthPowerNonresidueModel k) M x =
      ∑ p ∈ (Finset.range M).biUnion
          (fun j ↦ leastKthPowerNonresiduePatternPrimes k j x),
        (leastKthPowerNonresidue k p : ℝ) := by
  rw [primePatternHead]
  apply Eq.trans (Finset.sum_congr rfl fun j _ ↦
    patternContribution_eq_sum hk j x)
  exact (Finset.sum_biUnion
    (patternPrimeFinsets_pairwiseDisjoint k M x)).symm

/-- The finite pattern head is a sub-sum of the exact prime sum. -/
theorem primePatternHead_le_primeValueSum_leastKthPowerNonresidueModel
    {k : ℕ} (hk : 2 ≤ k) (M x : ℕ) :
    primePatternHead (leastKthPowerNonresidueModel k) M x ≤
      primeValueSum (leastKthPowerNonresidueModel k) x := by
  rw [primePatternHead_eq_sum_biUnion hk,
    primeValueSum_leastKthPowerNonresidueModel]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · rw [Finset.biUnion_subset_iff_forall_subset]
    intro j hj p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1⟩
  · intro p hp hpmissing
    positivity

/-- Removing finitely many fixed, nonnegative patterns leaves a nonnegative
remainder in the exact least-nonresidue model. -/
theorem primeValueTail_nonneg_leastKthPowerNonresidueModel
    {k : ℕ} (hk : 2 ≤ k) (M x : ℕ) :
    0 ≤ primeValueTail (leastKthPowerNonresidueModel k) M x := by
  rw [primeValueTail]
  exact sub_nonneg.mpr
    (primePatternHead_le_primeValueSum_leastKthPowerNonresidueModel hk M x)

theorem primeValueTail_nonneg_leastNonresidueModel
    {k : ℕ} (hk : 2 ≤ k) (M x : ℕ) :
    0 ≤ primeValueTail (leastNonresidueModel k hk) M x :=
  primeValueTail_nonneg_leastKthPowerNonresidueModel hk M x

theorem leastKthPowerNonresidue_patternPiece_nonneg
    (k j x : ℕ) :
    0 ≤ (leastKthPowerNonresidueModel k).enumeration j *
      primePatternCount (leastKthPowerNonresidueModel k) j x := by
  rw [leastKthPowerNonresidueModel_enumeration]
  exact mul_nonneg (by positivity) (by
    unfold primePatternCount
    positivity)

/-- The prime-number-theorem normalizing scale at a natural cutoff. -/
def erdos980Scale (x : ℕ) : ℝ :=
  (x : ℝ) / Real.log (x : ℝ)

@[simp]
theorem erdos980Scale_apply (x : ℕ) :
    erdos980Scale x = (x : ℝ) / Real.log (x : ℝ) := rfl

theorem erdos980Scale_eventually_pos :
    ∀ᶠ x : ℕ in atTop, 0 < erdos980Scale x := by
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [erdos980Scale]
  apply div_pos
  · exact_mod_cast (by omega : 0 < x)
  · apply Real.log_pos
    exact_mod_cast (by omega : 1 < x)

theorem erdos980Scale_eventually_ne_zero :
    ∀ᶠ x : ℕ in atTop, erdos980Scale x ≠ 0 := by
  filter_upwards [erdos980Scale_eventually_pos] with x hx
  exact hx.ne'

end

end Erdos980
