/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovPyke
import ErdosProblems.Erdos446.SmirnovNumerics
import ErdosProblems.Erdos446.SmirnovAbelTail

/-!
# Erdős Problem 446: normalized consequences of Pyke's formula

This file isolates the one quantitative estimate still required after the
exact finite last-failure identity.  The quantity `pykeFailureMass` is the
factorial-scaled mass of the complement of the Smirnov barrier.  Pyke's
formula says that the Smirnov probability is exactly one minus this mass,
normalized by `v ^ k`.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- The factorial-scaled mass of the last-failure fibers in Pyke's formula. -/
noncomputable def pykeFailureMass (k u w : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 (k - u),
    (k.choose (u + h) : ℝ) * (w : ℝ) *
      abelKernel (w : ℝ) (k - (u + h)) *
        (h : ℝ) ^ (u + h)

theorem pykeFailureMass_nonneg (k u w : ℕ) :
    0 ≤ pykeFailureMass k u w := by
  apply Finset.sum_nonneg
  intro h hh
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by positivity) (by positivity))
      (abelKernel_nonneg (by positivity) _))
    (by positivity)

/-- Pyke's formula in probability normalization. -/
theorem smirnovProbability_add_normalized_pykeFailureMass
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) (hv : 0 < v) :
    smirnovProbability k u v +
        pykeFailureMass k u w / (v : ℝ) ^ k = 1 := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hpow : (v : ℝ) ^ k ≠ 0 := (pow_pos hvR k).ne'
  have hpyke := smirnovOccupancyMass_pyke_last_failure
    hw hrel huk
  change (k.factorial : ℝ) * smirnovOccupancyMass k u v +
      pykeFailureMass k u w = (v : ℝ) ^ k at hpyke
  dsimp [smirnovProbability]
  rw [← add_div]
  rw [hpyke]
  exact div_self hpow

theorem smirnovProbability_eq_one_sub_normalized_pykeFailureMass
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) (hv : 0 < v) :
    smirnovProbability k u v =
      1 - pykeFailureMass k u w / (v : ℝ) ^ k := by
  linarith [smirnovProbability_add_normalized_pykeFailureMass
    hw hrel huk hv]

/-! ## The zero-offset endpoint -/

/-- At zero offset Raney's lemma gives the particularly simple probability
`w / (k+w)`.  This is the endpoint case of Daniels' exact formula. -/
theorem smirnovProbability_zero_eq
    {k v w : ℕ} (hw : 0 < w) (hrel : v = w + k) :
    smirnovProbability k 0 v = (w : ℝ) / (v : ℝ) := by
  have hv : 0 < v := by omega
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [hrel, smirnovProbability, smirnovOccupancyMass_zero_eq_abelKernel hw]
  have hpow : abelKernel (w : ℝ) k =
      (w + k : ℕ) ^ k / ((w + k : ℕ) : ℝ) := by
    cases k with
    | zero => simp [abelKernel]
    | succ k =>
        rw [abelKernel_eq_pow (by omega)]
        push_cast
        field_simp
        rw [pow_succ]
        ring
  rw [hpow]
  push_cast
  field_simp

/-- The desired uniform bound at offset zero, with room to spare. -/
theorem smirnovProbability_zero_le_twentyfour
    {k v w : ℕ} (hk : 0 < k) (hw : 0 < w) (hrel : v = w + k) :
    smirnovProbability k 0 v ≤
      24 * (w + 1 : ℝ) ^ 2 / (k : ℝ) := by
  rw [smirnovProbability_zero_eq hw hrel]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hvR : (0 : ℝ) < v := by rw [hrel]; positivity
  apply (div_le_div_iff₀ hvR hkR).2
  rw [hrel]
  push_cast
  nlinarith [sq_nonneg (w : ℝ), sq_nonneg ((w : ℝ) + 1)]

/-- At offset one the reflected Abel tail has only one nonzero term. -/
theorem smirnovProbability_one_eq
    {k v w : ℕ} (hk : 1 ≤ k) (hw : 0 < w)
    (hrel : 1 + v = k + w) :
    smirnovProbability k 1 v =
      (w : ℝ) * (w + k : ℕ) ^ (k - 1) / (v : ℝ) ^ k := by
  rw [smirnovProbability_eq_reflectedAbelTail hw hrel hk]
  rw [show 1 + 1 = 2 by norm_num, Finset.sum_range_succ,
    Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.cast_one, one_mul, Nat.cast_zero, zero_sub, pow_zero,
    mul_one, Nat.choose_one_right]
  norm_num
  rw [abelKernel_eq_pow (by omega : k ≠ 0)]

/-- The desired uniform bound at offset one. -/
theorem smirnovProbability_one_le_twentyfour
    {k v w : ℕ} (hk : 1 ≤ k) (hw : 0 < w)
    (hrel : 1 + v = k + w) :
    smirnovProbability k 1 v ≤
      24 * (1 + 1 : ℝ) * (w + 1 : ℝ) ^ 2 / (k : ℝ) := by
  rw [smirnovProbability_one_eq hk hw hrel]
  have hkR : (0 : ℝ) < k := by positivity
  have hv : 0 < v := by omega
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvk : k ≤ v := by omega
  have hvkR : (k : ℝ) ≤ v := by exact_mod_cast hvk
  have hvRelation : w + k = v + 1 := by omega
  have hbaseNonneg : 0 ≤ ((v + 1 : ℕ) : ℝ) / (v : ℝ) := by
    positivity
  have hbaseExp :
      ((v + 1 : ℕ) : ℝ) / (v : ℝ) ≤
        Real.exp (1 / (v : ℝ)) := by
    have hadd := Real.add_one_le_exp (1 / (v : ℝ))
    calc
      ((v + 1 : ℕ) : ℝ) / (v : ℝ) =
          1 + 1 / (v : ℝ) := by
            push_cast
            field_simp
      _ ≤ Real.exp (1 / (v : ℝ)) := by
        simpa [add_comm] using hadd
  have hexponent : ((k - 1 : ℕ) : ℝ) / (v : ℝ) ≤ 1 := by
    apply (div_le_one hvR).2
    exact_mod_cast (show k - 1 ≤ v by omega)
  have hfactor :
      (((v + 1 : ℕ) : ℝ) / (v : ℝ)) ^ (k - 1) ≤ 3 := by
    calc
      (((v + 1 : ℕ) : ℝ) / (v : ℝ)) ^ (k - 1) ≤
          (Real.exp (1 / (v : ℝ))) ^ (k - 1) :=
        pow_le_pow_left₀ hbaseNonneg hbaseExp _
      _ = Real.exp (((k - 1 : ℕ) : ℝ) * (1 / (v : ℝ))) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (((k - 1 : ℕ) : ℝ) / (v : ℝ)) := by
        congr 1
        ring
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hexponent
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hnormalize :
      (w : ℝ) * (w + k : ℕ) ^ (k - 1) / (v : ℝ) ^ k =
        ((w : ℝ) / (v : ℝ)) *
          (((v + 1 : ℕ) : ℝ) / (v : ℝ)) ^ (k - 1) := by
    rw [hvRelation]
    have hkSplit : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hvPow : (v : ℝ) ^ k =
        (v : ℝ) ^ (k - 1) * (v : ℝ) := by
      conv_lhs => rw [← hkSplit, pow_succ]
    rw [hvPow, div_pow]
    field_simp
  rw [hnormalize]
  have hfirst :
      ((w : ℝ) / (v : ℝ)) *
          (((v + 1 : ℕ) : ℝ) / (v : ℝ)) ^ (k - 1) ≤
        3 * (w : ℝ) / (v : ℝ) := by
    calc
      ((w : ℝ) / (v : ℝ)) *
          (((v + 1 : ℕ) : ℝ) / (v : ℝ)) ^ (k - 1) ≤
          ((w : ℝ) / (v : ℝ)) * 3 :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = 3 * (w : ℝ) / (v : ℝ) := by ring
  refine hfirst.trans ?_
  apply (div_le_div_iff₀ hvR hkR).2
  nlinarith [sq_nonneg (w : ℝ), sq_nonneg ((w : ℝ) + 1)]

/-- The precise finite-sum lower bound which implies Ford's exponential
comparison.  Keeping this implication separate makes clear that no measure
normalization or order-statistic identity remains to be proved. -/
theorem smirnovProbability_le_exponentialComplement_of_failure_lower
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) (hv : 0 < v)
    (hfailure :
      Real.exp (2 * (w : ℝ) + 2) *
          ((v : ℝ) - (2 * (w : ℝ) + 2)) ^ k ≤
        pykeFailureMass k u w) :
    smirnovProbability k u v ≤
      1 - Real.exp (2 * (w : ℝ) + 2) *
        (1 - (2 * (w : ℝ) + 2) / (v : ℝ)) ^ k := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hpow : (0 : ℝ) < (v : ℝ) ^ k := pow_pos hvR k
  rw [smirnovProbability_eq_one_sub_normalized_pykeFailureMass
    hw hrel huk hv]
  have hdiv := div_le_div_of_nonneg_right hfailure hpow.le
  have hrewrite :
      Real.exp (2 * (w : ℝ) + 2) *
            ((v : ℝ) - (2 * (w : ℝ) + 2)) ^ k /
          (v : ℝ) ^ k =
        Real.exp (2 * (w : ℝ) + 2) *
          (1 - (2 * (w : ℝ) + 2) / (v : ℝ)) ^ k := by
    rw [mul_div_assoc, ← div_pow]
    congr 1
    field_simp [hvR.ne']
  rw [hrewrite] at hdiv
  linarith

/-- Once the explicit Pyke failure sum has Ford's lower bound, the numerical
estimate already proved in `SmirnovNumerics` supplies the required uniform
constant. -/
theorem smirnovProbability_le_twentyfour_of_failure_lower
    {k u v w : ℕ} (hk : 100 ≤ k) (hu : 10 * u ≤ k)
    (hwSq : w * w ≤ k) (hw : 0 < w) (hrel : u + v = k + w)
    (hfailure :
      Real.exp (2 * (w : ℝ) + 2) *
          ((v : ℝ) - (2 * (w : ℝ) + 2)) ^ k ≤
        pykeFailureMass k u w) :
    smirnovProbability k u v ≤
      24 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 / (k : ℝ) := by
  have huk : u ≤ k := by omega
  have hv : 0 < v := by omega
  exact (smirnovProbability_le_exponentialComplement_of_failure_lower
      hw hrel huk hv hfailure).trans
    (fordSmirnovExponentialComplement_le hk hu hwSq hrel)

end Erdos446
