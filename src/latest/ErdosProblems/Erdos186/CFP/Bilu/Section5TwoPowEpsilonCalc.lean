/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5EpsilonCalc

/-!
# The epsilon calculus for Freiman's `2^n` theorem

The existing epsilon calculus has the source's central cube cardinality
`2 ^ n` replaced by `2 * n`.  The concavity argument is independent of this
leading coefficient.  This module reinstates the correct coefficient while
reusing the already-proved cell-count estimates.
-/

namespace Erdos186.CFP.Bilu.Section5TwoPowEpsilonCalc

open Section5EpsilonCalc
open scoped BigOperators

noncomputable section

/-- The error term in the genuine `2^n` induction. -/
def twoPowNEpsilon (n : ℕ) (density delta : ℝ) : ℝ :=
  ((2 ^ n : ℕ) : ℝ) *
    ((4 * (n : ℝ) * delta) / density) ^ epsilonExponent n density

theorem twoPowNEpsilon_pos {n : ℕ} {density delta : ℝ}
    (hn : 0 < n) (hdensity : 0 < density) (hdelta : 0 < delta) :
    0 < twoPowNEpsilon n density delta := by
  unfold twoPowNEpsilon
  have hbase : 0 < 4 * (n : ℝ) * delta / density := by positivity
  positivity

/-- At the cutoff density the exponential error is exactly `2 ^ n`. -/
theorem twoPowNEpsilon_cutoff {n : ℕ} {density : ℝ}
    (hn : 0 < n) (hdensity : 0 < density) :
    twoPowNEpsilon n density (density / (4 * n)) = (2 ^ n : ℕ) := by
  unfold twoPowNEpsilon
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hd0 : density ≠ 0 := hdensity.ne'
  have hbase :
      4 * (n : ℝ) * (density / (4 * (n : ℝ))) / density = 1 := by
    field_simp
  rw [hbase, Real.one_rpow, mul_one]

/-- Above the cutoff, the lower bound is vacuous. -/
theorem two_pow_le_twoPowNEpsilon_of_cutoff_le
    {n : ℕ} {density delta : ℝ}
    (hn : 0 < n) (hdensity : 0 < density)
    (hcutoff : density / (4 * n) ≤ delta) :
    ((2 ^ n : ℕ) : ℝ) ≤ twoPowNEpsilon n density delta := by
  rw [← twoPowNEpsilon_cutoff hn hdensity]
  unfold twoPowNEpsilon
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow
  · positivity
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcutoff (by positivity)) hdensity.le
  · exact (epsilonExponent_pos hn hdensity).le

/-- Scaling identity for an outside cell of relative size `eta`. -/
theorem twoPowNEpsilon_div_mul
    {n : ℕ} {density delta eta : ℝ}
    (hdensity : 0 < density) (hdelta : 0 < delta) (heta : 0 < eta) :
    twoPowNEpsilon n density (delta / eta) * eta =
      twoPowNEpsilon n density delta *
        eta ^ (1 - epsilonExponent n density) := by
  unfold twoPowNEpsilon
  have hA : 0 ≤ 4 * (n : ℝ) * delta / density := by positivity
  have heta0 : 0 ≤ eta := heta.le
  rw [show 4 * (n : ℝ) * (delta / eta) / density =
      (4 * (n : ℝ) * delta / density) / eta by field_simp]
  rw [Real.div_rpow hA heta0]
  rw [Real.rpow_sub heta 1 (epsilonExponent n density), Real.rpow_one]
  field_simp

/-- The complete weighted error estimate, now with leading coefficient
`2 ^ n`. -/
theorem sum_twoPowNEpsilon_div_mul_lt_of_nonneg
    {ι : Type*} [DecidableEq ι] {n : ℕ} {density delta : ℝ}
    (s : Finset ι) (eta : ι → ℝ)
    (hn : 0 < n) (hdensity0 : 0 < density) (hdensity1 : density ≤ 1)
    (hdelta : 0 < delta)
    (heta : ∀ i ∈ s, 0 ≤ eta i)
    (hcard : s.card ≤ cellCount n)
    (hsum : ∑ i ∈ s, eta i ≤ 1 - density / 2) :
    ∑ i ∈ s, twoPowNEpsilon n density (delta / eta i) * eta i <
      twoPowNEpsilon n density delta := by
  let t := s.filter fun i ↦ 0 < eta i
  have hteta : ∀ i ∈ t, 0 < eta i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have htcard : t.card ≤ cellCount n :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  have htsum : ∑ i ∈ t, eta i = ∑ i ∈ s, eta i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i his hit
    have hi0 := heta i his
    have hnpos : ¬ 0 < eta i := by
      intro hipos
      exact hit (Finset.mem_filter.mpr ⟨his, hipos⟩)
    simp [le_antisymm (not_lt.mp hnpos) hi0]
  have htbound : ∑ i ∈ t, eta i ≤ 1 - density / 2 :=
    htsum.trans_le hsum
  by_cases ht : t.Nonempty
  · have hsum0 : 0 ≤ ∑ i ∈ t, eta i :=
      Finset.sum_nonneg fun i hi ↦ (hteta i hi).le
    have hJ := sum_rpow_one_sub_le t eta ht
      (fun i hi ↦ (hteta i hi).le)
      (epsilonExponent_pos hn hdensity0).le
      (epsilonExponent_le_one hn hdensity1)
    have hcardR : (t.card : ℝ) ≤ cellCount n := by exact_mod_cast htcard
    have hcard0 : (0 : ℝ) ≤ t.card := by positivity
    have hcardPow :
        (t.card : ℝ) ^ epsilonExponent n density ≤
          (cellCount n : ℝ) ^ epsilonExponent n density :=
      Real.rpow_le_rpow hcard0 hcardR
        (epsilonExponent_pos hn hdensity0).le
    have hfactor :
        (t.card : ℝ) ^ epsilonExponent n density *
            (∑ i ∈ t, eta i) ^ (1 - epsilonExponent n density) < 1 :=
      (mul_le_mul_of_nonneg_right hcardPow
        (Real.rpow_nonneg hsum0 _)).trans_lt
          (cell_error_factor_lt_one hn hdensity0 hdensity1 hsum0 htbound)
    have hepsPos := twoPowNEpsilon_pos hn hdensity0 hdelta
    have htmain :
        ∑ i ∈ t, twoPowNEpsilon n density (delta / eta i) * eta i <
          twoPowNEpsilon n density delta := by
      calc
        ∑ i ∈ t, twoPowNEpsilon n density (delta / eta i) * eta i =
            twoPowNEpsilon n density delta *
              ∑ i ∈ t, eta i ^ (1 - epsilonExponent n density) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          exact twoPowNEpsilon_div_mul hdensity0 hdelta (hteta i hi)
        _ ≤ twoPowNEpsilon n density delta *
            ((t.card : ℝ) ^ epsilonExponent n density *
              (∑ i ∈ t, eta i) ^ (1 - epsilonExponent n density)) :=
          mul_le_mul_of_nonneg_left hJ hepsPos.le
        _ < twoPowNEpsilon n density delta * 1 :=
          mul_lt_mul_of_pos_left hfactor hepsPos
        _ = twoPowNEpsilon n density delta := mul_one _
    calc
      ∑ i ∈ s, twoPowNEpsilon n density (delta / eta i) * eta i =
          ∑ i ∈ t, twoPowNEpsilon n density (delta / eta i) * eta i := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i his hit
        have hi0 := heta i his
        have hnpos : ¬ 0 < eta i := by
          intro hipos
          exact hit (Finset.mem_filter.mpr ⟨his, hipos⟩)
        simp [le_antisymm (not_lt.mp hnpos) hi0]
      _ < twoPowNEpsilon n density delta := htmain
  · have htempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hzero : ∀ i ∈ s, eta i = 0 := by
      intro i hi
      have hi0 := heta i hi
      have hnpos : ¬ 0 < eta i := by
        intro hipos
        have : i ∈ t := Finset.mem_filter.mpr ⟨hi, hipos⟩
        simpa [htempty] using this
      exact le_antisymm (not_lt.mp hnpos) hi0
    rw [show ∑ i ∈ s, twoPowNEpsilon n density (delta / eta i) * eta i = 0 by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i hi]
      simp]
    exact twoPowNEpsilon_pos hn hdensity0 hdelta

end

end Erdos186.CFP.Bilu.Section5TwoPowEpsilonCalc

#print axioms
  Erdos186.CFP.Bilu.Section5TwoPowEpsilonCalc.sum_twoPowNEpsilon_div_mul_lt_of_nonneg
