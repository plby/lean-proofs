/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperUniformOccupancyMass
import ErdosProblems.Erdos446.UpperDiscreteLiteralLinearCore

/-!
# Erdős Problem 446: the affine part of Ford's finite T-cover

The closed discrete cover has an affine part and a crowding part.  This file
discharges the affine part without any abstract hypotheses.  Above the
critical depth its final strict barrier is impossible.  Below that depth the
uniform Smirnov estimate supplies the extra factor `1 / (k+1)`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Members of the weighted Ford set which fall in its affine alternative. -/
noncomputable def fordAffineOccupancies (k v γ r : ℕ) :
    Finset (Fin v → ℕ) := by
  classical
  exact (fordWeightedOccupancies k v γ).filter
    (SatisfiesFordAffineBarrier γ r)

theorem mem_fordAffineOccupancies {k v γ r : ℕ} {c : Fin v → ℕ} :
    c ∈ fordAffineOccupancies k v γ r ↔
      c ∈ fordWeightedOccupancies k v γ ∧
        SatisfiesFordAffineBarrier γ r c := by
  simp [fordAffineOccupancies]

/-- The affine prefix inequalities are exactly a discrete Smirnov barrier. -/
theorem fordAffineOccupancies_subset_smirnov (k v γ r : ℕ) :
    fordAffineOccupancies k v γ r ⊆
      smirnovOccupancies k (γ + r) v := by
  intro c hc
  have hc' := mem_fordAffineOccupancies.mp hc
  have htotal := (mem_fordWeightedOccupancies.mp hc'.1).1
  rw [mem_smirnovOccupancies]
  refine ⟨htotal, ?_⟩
  intro q hq0 hqv
  rw [← blockPrefixCount_eq_occupancyPrefix c hqv]
  exact hc'.2 q hqv

/-- If the affine offset reaches exactly the terminal total, its strict final
barrier makes the affine family empty. -/
theorem fordAffineOccupancies_eq_empty_of_terminal
    {k v γ r : ℕ} (hv : 0 < v) (huv : γ + r + v ≤ k) :
    fordAffineOccupancies k v γ r = ∅ := by
  classical
  ext c
  rw [mem_fordAffineOccupancies]
  constructor
  · intro hcaff
    rcases hcaff with ⟨hc, haff⟩
    have hsm := fordAffineOccupancies_subset_smirnov k v γ r
      (mem_fordAffineOccupancies.mpr ⟨hc, haff⟩)
    have hempty := smirnovOccupancies_empty_of_add_le
      (k := k) (u := γ + r) (v := v) hv huv
    rw [hempty] at hsm
    simpa using hsm
  · intro hempty
    simpa using hempty

/-- In the high-deficit case `k-v ≥ γ+5`, Ford's canonical affine
alternative is empty. -/
theorem fordCanonicalAffineOccupancies_eq_empty_high
    {k v γ : ℕ} (hv : 0 < v) (hhigh : v + γ + 5 ≤ k) :
    fordAffineOccupancies k v γ
      (fordDiscreteCoverRadius k v γ) = ∅ := by
  have hr : fordDiscreteCoverRadius k v γ = k - v - γ := by
    rw [fordDiscreteCoverRadius, max_eq_right]
    omega
  apply fordAffineOccupancies_eq_empty_of_terminal hv
  rw [hr]
  omega

/-- Below the critical depth, the affine alternative has Ford's natural
`v^k/(k+1)!` normalization.  The explicit constant absorbs the harmless
shifts `γ+6` and `w+1`, where `w=γ+5+v-k` is positive. -/
theorem fordCanonicalAffineOccupancies_mass_le_low
    {k v γ : ℕ} (hlow : k < γ + 5 + v) :
    reciprocalFactorialMassOver
        (fordAffineOccupancies k v γ
          (fordDiscreteCoverRadius k v γ)) ≤
      57600 * ((γ + 1 : ℕ) : ℝ) *
        ((γ + 5 + v - k : ℕ) : ℝ) ^ 2 * (v : ℝ) ^ k /
          ((k + 1).factorial : ℝ) := by
  let w := γ + 5 + v - k
  have hw : 0 < w := by dsimp [w]; omega
  have hr : fordDiscreteCoverRadius k v γ = 5 := by
    rw [fordDiscreteCoverRadius, max_eq_left]
    omega
  have hrel : (γ + 5) + v = k + w := by
    dsimp [w]
    omega
  have hbase := reciprocalFactorialMassOver_le_uniformSmirnov_unconditional
    (k := k) (u := γ + 5) (v := v) (w := w)
    hw hrel (fordAffineOccupancies_subset_smirnov k v γ 5)
  rw [hr]
  apply hbase.trans
  have hγ : ((γ + 6 : ℕ) : ℝ) ≤ 6 * ((γ + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show γ + 6 ≤ 6 * (γ + 1) by omega)
  have hw1 : (((w + 1 : ℕ) : ℝ) : ℝ) ≤ 2 * (w : ℝ) := by
    exact_mod_cast (show w + 1 ≤ 2 * w by omega)
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hvpow : (0 : ℝ) ≤ (v : ℝ) ^ k := by positivity
  have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  apply (div_le_div_iff_of_pos_right hfac).2
  have hsq : (((w + 1 : ℕ) : ℝ) : ℝ) ^ 2 ≤
      4 * (w : ℝ) ^ 2 := by nlinarith
  have hcore :
      2400 * (((γ + 5) + 1 : ℕ) : ℝ) *
          (((w + 1 : ℕ) : ℝ) : ℝ) ^ 2 ≤
        57600 * ((γ + 1 : ℕ) : ℝ) * (w : ℝ) ^ 2 := by
    have hwSq : 0 ≤ (w : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have := mul_le_mul_of_nonneg_right hcore hvpow
  simpa [w, mul_assoc] using this

end Erdos446
