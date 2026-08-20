/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperCrowdingMass
import ErdosProblems.Erdos446.UpperExceptionalKthLayer

/-!
# Erdős Problem 446: uniform barriers as reciprocal-factorial mass

The probability normalization for the finite Smirnov region contains a
factor `k! / v^k`.  Combining it with the unconditional `1/(k+1)`
probability estimate therefore gives exactly a `(k+1)!` denominator.  This
file records that conversion for arbitrary subfamilies, so exceptional-cover
arguments never need to discard the extra factorial.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem reciprocalFactorialMassOver_smirnovOccupancies
    (k u v : ℕ) :
    reciprocalFactorialMassOver (smirnovOccupancies k u v) =
      smirnovOccupancyMass k u v := by
  rfl

/-- Any subfamily of one affine Smirnov barrier has the sharp
reciprocal-factorial normalization. -/
theorem reciprocalFactorialMassOver_le_uniformSmirnov
    {k u v w : ℕ} {I : Finset (Fin v → ℕ)}
    (hk : 0 < k) (hv : 0 < v) (hw : 0 < w)
    (hrel : u + v = k + w)
    (hI : I ⊆ smirnovOccupancies k u v) :
    reciprocalFactorialMassOver I ≤
      2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 * (v : ℝ) ^ k /
        ((k + 1).factorial : ℝ) := by
  have hmono : reciprocalFactorialMassOver I ≤
      smirnovOccupancyMass k u v := by
    rw [← reciprocalFactorialMassOver_smirnovOccupancies]
    exact reciprocalFactorialMassOver_mono hI
  have hprob := smirnovProbability_le_uniform hk hw hrel
  have hnorm := smirnovOccupancyMass_eq_probability_mul hv
    (k := k) (u := u)
  rw [hnorm] at hmono
  apply hmono.trans
  calc
    smirnovProbability k u v * (v : ℝ) ^ k / (k.factorial : ℝ) ≤
        (2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 /
            (k + 1 : ℕ)) * (v : ℝ) ^ k / (k.factorial : ℝ) := by
      gcongr
    _ = 2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 * (v : ℝ) ^ k /
        ((k + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp

/-- Endpoint-safe version of the same estimate.  Empty-object and
empty-cell cases are discharged by the full multinomial mass, so callers
splitting an occupancy at a rank do not need separate boundary cases. -/
theorem reciprocalFactorialMassOver_le_uniformSmirnov_unconditional
    {k u v w : ℕ} {I : Finset (Fin v → ℕ)}
    (hw : 0 < w) (hrel : u + v = k + w)
    (hI : I ⊆ smirnovOccupancies k u v) :
    reciprocalFactorialMassOver I ≤
      2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 * (v : ℝ) ^ k /
        ((k + 1).factorial : ℝ) := by
  have hmono : reciprocalFactorialMassOver I ≤
      smirnovOccupancyMass k u v := by
    rw [← reciprocalFactorialMassOver_smirnovOccupancies]
    exact reciprocalFactorialMassOver_mono hI
  by_cases hk0 : k = 0
  · subst k
    have hleOne : reciprocalFactorialMassOver I ≤ 1 := by
      exact hmono.trans (by
        simpa using smirnovOccupancyMass_le_total 0 u v)
    have huOne : (1 : ℝ) ≤ (u + 1 : ℝ) := by
      exact_mod_cast (Nat.le_add_left 1 u)
    have hwOne : (1 : ℝ) ≤ (w + 1 : ℝ) := by
      exact_mod_cast (Nat.le_add_left 1 w)
    have hwSqOne : (1 : ℝ) ≤ (w + 1 : ℝ) ^ 2 :=
      one_le_pow₀ hwOne
    have hprodOne : (1 : ℝ) ≤
        (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 := by
      simpa only [one_mul] using
        mul_le_mul huOne hwSqOne (by norm_num) (by positivity)
    have hR : (1 : ℝ) ≤
        2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 := by
      calc
        (1 : ℝ) ≤ 2400 * 1 * 1 := by norm_num
        _ ≤ 2400 * ((u + 1 : ℝ) * (w + 1 : ℝ) ^ 2) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hprodOne (by norm_num : (0 : ℝ) ≤ 2400)
        _ = 2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 := by ring
    exact hleOne.trans (by simpa using hR)
  by_cases hv0 : v = 0
  · subst v
    have hzero : smirnovOccupancyMass k u 0 ≤ 0 := by
      simpa [hk0] using smirnovOccupancyMass_le_total k u 0
    exact (hmono.trans hzero).trans_eq (by simp [hk0])
  exact reciprocalFactorialMassOver_le_uniformSmirnov
    (Nat.pos_of_ne_zero hk0) (Nat.pos_of_ne_zero hv0) hw hrel hI

/-- Direct arithmetic-layer consequence when the discrete Ford set is
covered by one affine Smirnov barrier.  More elaborate exceptional covers
apply the same estimate to each piece before using the generic kth-layer
bridge. -/
theorem blockIntegerDyadicLayer_mass_le_of_fordWeightedSmirnov
    {M k v m u w : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmk : m ≤ k)
    (hM : k + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hk : 0 < k) (hv : 0 < v) (hw : 0 < w)
    (hrel : u + v = k + w)
    (hford : fordWeightedOccupancies k v m ⊆
      smirnovOccupancies k u v) :
    blockClusterMassOver M (blockIntegerDyadicLayer k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
          (2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 * (v : ℝ) ^ k /
            ((k + 1).factorial : ℝ)) := by
  apply blockIntegerDyadicLayer_mass_le_of_fordWeightedMass_uniform
    hC hmk hM hmass
  exact reciprocalFactorialMassOver_le_uniformSmirnov
    hk hv hw hrel hford

end Erdos446
