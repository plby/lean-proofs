/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.AbelConvolution
import ErdosProblems.Erdos446.CappedCompositions

/-!
# Erdős Problem 446: the finite Smirnov occupancy model

Ford's order-statistics region can be partitioned into `v` equal intervals.
An occupancy vector `c : Fin v → ℕ` then has multinomial weight
`1 / ∏ i, c i !`, and the lower barriers on the ordered coordinates become
the strict prefix inequalities

`sum_{i < h} c i < u + h` for `1 ≤ h ≤ v`.

This file defines that exact finite model and records its normalization and
monotonicity properties.  The subsequent parking/Smirnov estimate can
therefore be proved entirely by finite Abel convolutions.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Number of occupied slots among the first `h` of `v` equal cells. -/
def occupancyPrefix {v : ℕ} (c : Fin v → ℕ) (h : ℕ) : ℕ :=
  ∑ i ∈ (Finset.univ.filter fun i : Fin v ↦ i.val < h), c i

theorem occupancyPrefix_zero {v : ℕ} (c : Fin v → ℕ) :
    occupancyPrefix c 0 = 0 := by
  simp [occupancyPrefix]

theorem occupancyPrefix_mono {v : ℕ} (c : Fin v → ℕ) :
    Monotone (occupancyPrefix c) := by
  intro h h' hh'
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  · intro i hi _
    exact Nat.zero_le _

theorem occupancyPrefix_eq_sum_of_ge {v : ℕ} (c : Fin v → ℕ)
    {h : ℕ} (hvh : v ≤ h) :
    occupancyPrefix c h = ∑ i, c i := by
  rw [occupancyPrefix]
  congr 1
  ext i
  simp [i.isLt.trans_le hvh]

theorem occupancyPrefix_at_length {v : ℕ} (c : Fin v → ℕ) :
    occupancyPrefix c v = ∑ i, c i :=
  occupancyPrefix_eq_sum_of_ge c le_rfl

/-- Occupancy vectors of total mass `k` satisfying Ford's integer
order-statistic barriers. -/
def smirnovOccupancies (k u v : ℕ) : Finset (Fin v → ℕ) :=
  (compositionsOf v k).filter fun c ↦
    ∀ h : ℕ, 1 ≤ h → h ≤ v → occupancyPrefix c h < u + h

theorem mem_smirnovOccupancies {k u v : ℕ} {c : Fin v → ℕ} :
    c ∈ smirnovOccupancies k u v ↔
      (∑ i, c i = k) ∧
        ∀ h : ℕ, 1 ≤ h → h ≤ v → occupancyPrefix c h < u + h := by
  simp [smirnovOccupancies, mem_compositionsOf]

/-- Reciprocal-factorial mass of the finite Smirnov region.  Multiplication
by `k! / v^k` gives the probability of the corresponding multinomial event.
-/
noncomputable def smirnovOccupancyMass (k u v : ℕ) : ℝ :=
  ∑ c ∈ smirnovOccupancies k u v, 1 / compositionFactorial c

private theorem inv_compositionFactorial_nonneg {v : ℕ}
    (c : Fin v → ℕ) : 0 ≤ 1 / compositionFactorial c := by
  apply one_div_nonneg.mpr
  dsimp [compositionFactorial]
  positivity

theorem smirnovOccupancyMass_nonneg (k u v : ℕ) :
    0 ≤ smirnovOccupancyMass k u v := by
  apply Finset.sum_nonneg
  intro c hc
  exact inv_compositionFactorial_nonneg c

theorem smirnovOccupancies_mono_u (k v : ℕ) :
    Monotone fun u ↦ smirnovOccupancies k u v := by
  intro u u' huu'
  intro c hc
  rw [mem_smirnovOccupancies] at hc ⊢
  refine ⟨hc.1, ?_⟩
  intro h hh hv
  exact hc.2 h hh hv |>.trans_le (Nat.add_le_add_right huu' h)

theorem smirnovOccupancyMass_mono_u (k v : ℕ) :
    Monotone fun u ↦ smirnovOccupancyMass k u v := by
  intro u u' huu'
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact smirnovOccupancies_mono_u k v huu'
  · intro c hc _
    exact inv_compositionFactorial_nonneg c

/-- The constrained mass is no larger than the full multinomial mass. -/
theorem smirnovOccupancyMass_le_total (k u v : ℕ) :
    smirnovOccupancyMass k u v ≤
      (v : ℝ) ^ k / (k.factorial : ℝ) := by
  calc
    smirnovOccupancyMass k u v ≤
        ∑ c ∈ compositionsOf v k, 1 / compositionFactorial c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro c hc _
        exact inv_compositionFactorial_nonneg c
    _ = (v : ℝ) ^ k / (k.factorial : ℝ) :=
      sum_inv_compositionFactorial_compositionsOf v k

/-- If the terminal slack vanishes, the strict final barrier is impossible.
-/
theorem smirnovOccupancies_empty_of_add_le
    {k u v : ℕ} (hv : 0 < v) (huv : u + v ≤ k) :
    smirnovOccupancies k u v = ∅ := by
  by_contra hne
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hmem := mem_smirnovOccupancies.mp hc
  have hfinal := hmem.2 v (by omega) le_rfl
  rw [occupancyPrefix_at_length, hmem.1] at hfinal
  omega

theorem smirnovOccupancyMass_eq_zero_of_add_le
    {k u v : ℕ} (hv : 0 < v) (huv : u + v ≤ k) :
    smirnovOccupancyMass k u v = 0 := by
  rw [smirnovOccupancyMass, smirnovOccupancies_empty_of_add_le hv huv]
  simp

/-! ## Probability normalization -/

/-- The probability of the finite occupancy event.  This is exactly
`k!` times the associated ordered-simplex volume: each occupancy vector has
multinomial probability `k! / (v^k * ∏ cᵢ!)`. -/
noncomputable def smirnovProbability (k u v : ℕ) : ℝ :=
  (k.factorial : ℝ) * smirnovOccupancyMass k u v / (v : ℝ) ^ k

theorem smirnovProbability_nonneg (k u v : ℕ) :
    0 ≤ smirnovProbability k u v := by
  exact div_nonneg
    (mul_nonneg (by positivity) (smirnovOccupancyMass_nonneg k u v))
    (pow_nonneg (by positivity) k)

theorem smirnovProbability_le_one {k u v : ℕ} (hv : 0 < v) :
    smirnovProbability k u v ≤ 1 := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hpow : (0 : ℝ) < (v : ℝ) ^ k := pow_pos hvR k
  calc
    smirnovProbability k u v ≤
        (k.factorial : ℝ) *
            ((v : ℝ) ^ k / (k.factorial : ℝ)) / (v : ℝ) ^ k := by
      dsimp [smirnovProbability]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (smirnovOccupancyMass_le_total k u v) hfac.le)
        hpow.le
    _ = 1 := by field_simp [hfac.ne', hpow.ne']

theorem smirnovProbability_eq_zero_of_add_le
    {k u v : ℕ} (hv : 0 < v) (huv : u + v ≤ k) :
    smirnovProbability k u v = 0 := by
  simp [smirnovProbability,
    smirnovOccupancyMass_eq_zero_of_add_le hv huv]

end Erdos446
