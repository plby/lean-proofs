/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovSplitMass

/-!
# Erdős Problem 446: Pyke's exact finite occupancy formula

The good Smirnov occupancies and the last-failure fibers partition all weak
compositions.  Combining that partition with the Raney evaluation of the
zero-offset suffix gives Pyke's exact finite formula.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Occupancies of total mass `k` which fail at least one offset-`u` barrier. -/
noncomputable def failedSmirnovOccupancies (k u v : ℕ) :
    Finset (Fin v → ℕ) := by
  classical
  exact (compositionsOf v k).filter fun c ↦
    ¬ SatisfiesSmirnovBarrier u c

theorem mem_failedSmirnovOccupancies {k u v : ℕ} {c : Fin v → ℕ} :
    c ∈ failedSmirnovOccupancies k u v ↔
      (∑ i, c i = k) ∧ ¬ SatisfiesSmirnovBarrier u c := by
  classical
  simp [failedSmirnovOccupancies, mem_compositionsOf]

theorem sum_failedSmirnovOccupancies_eq_fibers
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) :
    (∑ c ∈ failedSmirnovOccupancies k u v,
      1 / compositionFactorial c) =
      ∑ h ∈ Finset.Icc 1 (k - u),
        ∑ c ∈ lastFailureFiber k u v h,
          1 / compositionFactorial c := by
  classical
  have hmaps : ∀ c ∈ failedSmirnovOccupancies k u v,
      lastFailedPrefix u c ∈ Finset.Icc 1 (k - u) := by
    intro c hc
    have hcData := mem_failedSmirnovOccupancies.mp hc
    have hpos := lastFailedPrefix_pos_of_not_barrier hcData.2
    have hexact := occupancyPrefix_lastFailedPrefix_eq
      hw hrel hcData.1 hcData.2
    have hprefixLe : occupancyPrefix c (lastFailedPrefix u c) ≤ k := by
      rw [← hcData.1]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          )
        (by intro i _hi _hnot; exact Nat.zero_le _)
    rw [Finset.mem_Icc]
    constructor
    · omega
    · omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  ext c
  simp only [Finset.mem_filter, mem_failedSmirnovOccupancies,
    mem_lastFailureFiber]
  aesop

theorem smirnovOccupancyMass_add_failure_mass
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) :
    smirnovOccupancyMass k u v +
        ∑ h ∈ Finset.Icc 1 (k - u),
          ((h : ℝ) ^ (u + h) / ((u + h).factorial : ℝ)) *
            smirnovOccupancyMass (k - (u + h)) 0 (v - h) =
      (v : ℝ) ^ k / (k.factorial : ℝ) := by
  classical
  have hgood : smirnovOccupancies k u v =
      (compositionsOf v k).filter (SatisfiesSmirnovBarrier u) := by
    ext c
    simp [mem_smirnovOccupancies_iff_barrier]
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (compositionsOf v k) (SatisfiesSmirnovBarrier u)
      (fun c ↦ 1 / compositionFactorial c)
  rw [← hgood] at hpartition
  change smirnovOccupancyMass k u v +
      (∑ c ∈ failedSmirnovOccupancies k u v,
        1 / compositionFactorial c) =
      (∑ c ∈ compositionsOf v k,
        1 / compositionFactorial c) at hpartition
  rw [sum_failedSmirnovOccupancies_eq_fibers hw hrel huk] at hpartition
  calc
    smirnovOccupancyMass k u v +
        ∑ h ∈ Finset.Icc 1 (k - u),
          ((h : ℝ) ^ (u + h) / ((u + h).factorial : ℝ)) *
            smirnovOccupancyMass (k - (u + h)) 0 (v - h) =
        smirnovOccupancyMass k u v +
          ∑ h ∈ Finset.Icc 1 (k - u),
            ∑ c ∈ lastFailureFiber k u v h,
              1 / compositionFactorial c := by
      apply congrArg (smirnovOccupancyMass k u v + ·)
      apply Finset.sum_congr rfl
      intro h hh
      have hhData := Finset.mem_Icc.mp hh
      exact (sum_lastFailureFiber_inv_factorial hw hrel
        hhData.1 (by
          have hv : k < u + v := by omega
          omega) (by omega)).symm
    _ = ∑ c ∈ compositionsOf v k,
          1 / compositionFactorial c := hpartition
    _ = (v : ℝ) ^ k / (k.factorial : ℝ) :=
      sum_inv_compositionFactorial_compositionsOf v k

/-- The last-failure identity after evaluating every zero-offset suffix by
Raney's lemma. -/
theorem smirnovOccupancyMass_add_abel_failure_mass
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) :
    smirnovOccupancyMass k u v +
        ∑ h ∈ Finset.Icc 1 (k - u),
          ((h : ℝ) ^ (u + h) / ((u + h).factorial : ℝ)) *
            ((w : ℝ) * abelKernel (w : ℝ) (k - (u + h)) /
              ((k - (u + h)).factorial : ℝ)) =
      (v : ℝ) ^ k / (k.factorial : ℝ) := by
  rw [← smirnovOccupancyMass_add_failure_mass hw hrel huk]
  apply congrArg (smirnovOccupancyMass k u v + ·)
  apply Finset.sum_congr rfl
  intro h hh
  have hhData := Finset.mem_Icc.mp hh
  have huhk : u + h ≤ k := by omega
  have hlen : v - h = w + (k - (u + h)) := by omega
  rw [hlen, smirnovOccupancyMass_zero_eq_abelKernel hw]

theorem factorial_mul_abel_failure_term
    {k u h w : ℕ} (huhk : u + h ≤ k) :
    (k.factorial : ℝ) *
        (((h : ℝ) ^ (u + h) / ((u + h).factorial : ℝ)) *
          ((w : ℝ) * abelKernel (w : ℝ) (k - (u + h)) /
            ((k - (u + h)).factorial : ℝ))) =
      (k.choose (u + h) : ℝ) *
        (w : ℝ) * abelKernel (w : ℝ) (k - (u + h)) *
          (h : ℝ) ^ (u + h) := by
  have hfac := Nat.choose_mul_factorial_mul_factorial huhk
  have hfacR :
      (k.choose (u + h) : ℝ) * ((u + h).factorial : ℝ) *
          ((k - (u + h)).factorial : ℝ) = (k.factorial : ℝ) := by
    exact_mod_cast hfac
  have hleft : ((u + h).factorial : ℝ) ≠ 0 := by positivity
  have hright : ((k - (u + h)).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hleft, hright]
  rw [← hfacR]
  ring

/-- Pyke's exact formula, indexed by the last failed prefix length. -/
theorem smirnovOccupancyMass_pyke_last_failure
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) :
    (k.factorial : ℝ) * smirnovOccupancyMass k u v +
        ∑ h ∈ Finset.Icc 1 (k - u),
          (k.choose (u + h) : ℝ) * (w : ℝ) *
            abelKernel (w : ℝ) (k - (u + h)) *
              (h : ℝ) ^ (u + h) =
      (v : ℝ) ^ k := by
  have hmass := smirnovOccupancyMass_add_abel_failure_mass
    hw hrel huk
  calc
    (k.factorial : ℝ) * smirnovOccupancyMass k u v +
        ∑ h ∈ Finset.Icc 1 (k - u),
          (k.choose (u + h) : ℝ) * (w : ℝ) *
            abelKernel (w : ℝ) (k - (u + h)) *
              (h : ℝ) ^ (u + h) =
        (k.factorial : ℝ) *
          (smirnovOccupancyMass k u v +
            ∑ h ∈ Finset.Icc 1 (k - u),
              ((h : ℝ) ^ (u + h) / ((u + h).factorial : ℝ)) *
                ((w : ℝ) * abelKernel (w : ℝ) (k - (u + h)) /
                  ((k - (u + h)).factorial : ℝ))) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      exact factorial_mul_abel_failure_term
        (k := k) (u := u) (h := h) (w := w) (by
        have hhData := Finset.mem_Icc.mp hh
        omega) |>.symm
    _ = (k.factorial : ℝ) *
        ((v : ℝ) ^ k / (k.factorial : ℝ)) := by rw [hmass]
    _ = (v : ℝ) ^ k := by
      field_simp

end Erdos446
