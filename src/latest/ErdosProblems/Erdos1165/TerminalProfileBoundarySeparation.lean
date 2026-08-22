/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.TerminalSpliceProfileGeometry

/-! # Separation of adjacent HLOZ profile boundaries -/

open Set

namespace Erdos1165.TerminalProfileBoundarySeparation

open ThickPoint TerminalSpliceProfileGeometry

noncomputable section

/-- At every nonzero profile coordinate, adjacent radii are separated by a
full nearest-neighbor step once `n ≥ 2`. -/
lemma scaleRadius_add_one_le_previous
    {n k : ℕ} (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k ≤ n + 1) :
    scaleRadius n k + 1 ≤ scaleRadius n (k - 1) := by
  by_cases hkn : k ≤ n
  · rw [scaleRadius_of_le hkn,
      scaleRadius_of_le (by omega : k - 1 ≤ n)]
    unfold regularRadius
    have harg : (n : ℝ) - ((k - 1 : ℕ) : ℝ) =
        ((n : ℝ) - (k : ℝ)) + 1 := by
      push_cast
      have hkcast : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      push_cast
      ring
    rw [harg, Real.exp_add]
    have hexpOne : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h
      exact h
    have hexpNonneg : 0 ≤ Real.exp ((n : ℝ) - (k : ℝ)) :=
      (Real.exp_pos _).le
    have hargNonneg : (0 : ℝ) ≤ (n : ℝ) - (k : ℝ) := by
      apply sub_nonneg.mpr
      exact_mod_cast hkn
    have hexpBase : (1 : ℝ) ≤ Real.exp ((n : ℝ) - (k : ℝ)) :=
      Real.one_le_exp hargNonneg
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn.trans' (by omega)
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 9 := one_le_pow₀ hnOne
    have hbaseProduct : (1 : ℝ) ≤
        Real.exp ((n : ℝ) - (k : ℝ)) * (n : ℝ) ^ 9 :=
      one_le_mul_of_one_le_of_one_le hexpBase hpow
    have htwice : 2 *
        (Real.exp ((n : ℝ) - (k : ℝ)) * (n : ℝ) ^ 9) ≤
      Real.exp 1 *
        (Real.exp ((n : ℝ) - (k : ℝ)) * (n : ℝ) ^ 9) :=
      mul_le_mul_of_nonneg_right hexpOne (by positivity)
    nlinarith
  · have hkeq : k = n + 1 := by omega
    subst k
    rw [scaleRadius_succ_self, Nat.add_sub_cancel,
      scaleRadius_of_le le_rfl, regularRadius_self]
    have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnOne : (1 : ℝ) ≤ n := hnReal.trans' (by norm_num)
    have hpowSix : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hnOne
    have hpowThree : (2 : ℝ) ≤ (n : ℝ) ^ 3 := by
      calc
        (2 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
        _ ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hnReal 3
    have hfactor : (n : ℝ) ^ 9 = (n : ℝ) ^ 6 * (n : ℝ) ^ 3 := by
      ring
    rw [hfactor]
    nlinarith

/-- Distinct adjacent profile boundaries are disjoint at all coordinates
used by `excursionProfile`. -/
lemma profileBoundaries_disjoint
    {n k : ℕ} (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k ≤ n + 1)
    (x : Point) :
    Disjoint (discBoundary x (scaleRadius n (k - 1)))
      (discBoundary x (scaleRadius n k)) := by
  rw [Set.disjoint_left]
  intro z hzOuter hzInner
  exact (not_mem_discBoundary_of_mem_disc_of_add_one_le hzInner.1
    (scaleRadius_add_one_le_previous hn hk0 hk)) hzOuter

/-- Fin-indexed form used by the whole-profile scan theorem. -/
lemma profileBoundaries_disjoint_fin
    {n : ℕ} (hn : 2 ≤ n) (x : Point)
    (k : Fin (n + 2)) (hk0 : (k : ℕ) ≠ 0) :
    Disjoint
      (discBoundary x (scaleRadius n ((k : ℕ) - 1)))
      (discBoundary x (scaleRadius n (k : ℕ))) := by
  apply profileBoundaries_disjoint hn (Nat.pos_of_ne_zero hk0)
  omega

end

end Erdos1165.TerminalProfileBoundarySeparation
