/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5OutsideCells
import ErdosProblems.Erdos186.CFP.Bilu.Section5FullCube
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The epsilon calculus in Bilu's proof of the `2n` theorem

The induction in Section 5.2 is run with a density parameter `delta`.
An outside cell occupying a fraction `eta` of the original set inherits
density parameter `delta / eta`.  This file supplies the finite concavity
estimate which makes the resulting errors summable.

We use a deliberately conservative positive exponent.  Its only purpose is
to make the uniform estimate over the at most `3^n` coordinate cells
completely explicit.
-/

namespace Erdos186.CFP.Bilu.Section5EpsilonCalc

open scoped BigOperators

noncomputable section

/-- A harmless upper bound for the number of coordinate cells. -/
def cellCount (n : ℕ) : ℕ := 3 ^ n

/-- The small exponent in the density-error function. -/
def epsilonExponent (n : ℕ) (d : ℝ) : ℝ :=
  d / (100 * (n : ℝ) * (cellCount n : ℝ))

/-- The error attached to a requested hyperplane density `delta`. -/
def twoNEpsilon (n : ℕ) (d delta : ℝ) : ℝ :=
  2 * (n : ℝ) *
    ((4 * (n : ℝ) * delta) / d) ^ epsilonExponent n d

theorem cellCount_pos (n : ℕ) : 0 < cellCount n := by
  simp [cellCount]

theorem epsilonExponent_pos {n : ℕ} {d : ℝ}
    (hn : 0 < n) (hd : 0 < d) :
    0 < epsilonExponent n d := by
  unfold epsilonExponent
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (0 : ℝ) < cellCount n := by
    exact_mod_cast cellCount_pos n
  exact div_pos hd (by positivity)

theorem epsilonExponent_le_half {n : ℕ} {d : ℝ}
    (hn : 0 < n) (hd : d ≤ 1) :
    epsilonExponent n d ≤ 1 / 2 := by
  unfold epsilonExponent
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpNat : 1 ≤ cellCount n :=
    Nat.one_le_iff_ne_zero.mpr (cellCount_pos n).ne'
  have hp : (1 : ℝ) ≤ cellCount n := by exact_mod_cast hpNat
  have hden : (2 : ℝ) ≤ 100 * (n : ℝ) * (cellCount n : ℝ) := by
    nlinarith
  have hdenpos : 0 < 100 * (n : ℝ) * (cellCount n : ℝ) := by positivity
  apply (div_le_iff₀ hdenpos).2
  nlinarith

theorem epsilonExponent_le_one {n : ℕ} {d : ℝ}
    (hn : 0 < n) (hd : d ≤ 1) :
    epsilonExponent n d ≤ 1 :=
  (epsilonExponent_le_half hn hd).trans (by norm_num)

theorem twoNEpsilon_pos {n : ℕ} {d delta : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hdelta : 0 < delta) :
    0 < twoNEpsilon n d delta := by
  unfold twoNEpsilon
  have hbase : 0 < 4 * (n : ℝ) * delta / d := by positivity
  positivity

/-- At the cutoff density `d/(4n)`, the error is exactly `2n`. -/
theorem twoNEpsilon_cutoff {n : ℕ} {d : ℝ}
    (hn : 0 < n) (hd : 0 < d) :
    twoNEpsilon n d (d / (4 * n)) = 2 * n := by
  unfold twoNEpsilon
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hd0 : d ≠ 0 := hd.ne'
  have hbase : 4 * (n : ℝ) * (d / (4 * (n : ℝ))) / d = 1 := by
    field_simp
  rw [hbase, Real.one_rpow, mul_one]

/-- Above the cutoff density, the error is at least `2n`; hence the
corresponding inductive lower bound is vacuous. -/
theorem two_mul_le_twoNEpsilon_of_cutoff_le {n : ℕ} {d delta : ℝ}
    (hn : 0 < n) (hd : 0 < d)
    (hcutoff : d / (4 * n) ≤ delta) :
    2 * (n : ℝ) ≤ twoNEpsilon n d delta := by
  rw [← twoNEpsilon_cutoff hn hd]
  unfold twoNEpsilon
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow
  · positivity
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcutoff (by positivity)) hd.le
  · exact (epsilonExponent_pos hn hd).le

/-- Scaling identity used in every nonempty outside cell. -/
theorem twoNEpsilon_div_mul {n : ℕ} {d delta eta : ℝ}
    (hd : 0 < d) (hdelta : 0 < delta) (heta : 0 < eta) :
    twoNEpsilon n d (delta / eta) * eta =
      twoNEpsilon n d delta * eta ^ (1 - epsilonExponent n d) := by
  by_cases hn : n = 0
  · subst n
    simp [twoNEpsilon]
  unfold twoNEpsilon
  have hA : 0 ≤ 4 * (n : ℝ) * delta / d := by positivity
  have heta0 : 0 ≤ eta := heta.le
  rw [show 4 * (n : ℝ) * (delta / eta) / d =
      (4 * (n : ℝ) * delta / d) / eta by field_simp]
  rw [Real.div_rpow hA heta0]
  rw [Real.rpow_sub heta 1 (epsilonExponent n d), Real.rpow_one]
  field_simp

/-- Equal-weight Jensen in the form used in equation (5.14). -/
theorem sum_rpow_one_sub_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (eta : ι → ℝ) {nu : ℝ}
    (hs : s.Nonempty) (heta : ∀ i ∈ s, 0 ≤ eta i)
    (hnu0 : 0 ≤ nu) (hnu1 : nu ≤ 1) :
    ∑ i ∈ s, eta i ^ (1 - nu) ≤
      (s.card : ℝ) ^ nu * (∑ i ∈ s, eta i) ^ (1 - nu) := by
  let m : ℝ := s.card
  have hm : 0 < m := by
    simpa [m] using (show (0 : ℝ) < s.card by
      exact_mod_cast (Finset.card_pos.mpr hs))
  have hpow0 : 0 ≤ 1 - nu := by linarith
  have hpow1 : 1 - nu ≤ 1 := by linarith
  have hJ := (Real.concaveOn_rpow hpow0 hpow1).le_map_sum
    (t := s) (w := fun _ : ι ↦ (1 / m : ℝ)) (p := eta)
    (fun _ _ ↦ by positivity)
    (by simp [m, hm.ne'])
    (fun i hi ↦ heta i hi)
  have hJ' :
      (1 / m) * (∑ i ∈ s, eta i ^ (1 - nu)) ≤
        ((1 / m) * ∑ i ∈ s, eta i) ^ (1 - nu) := by
    simpa [smul_eq_mul, Finset.mul_sum] using hJ
  have hsum0 : 0 ≤ ∑ i ∈ s, eta i :=
    Finset.sum_nonneg heta
  calc
    ∑ i ∈ s, eta i ^ (1 - nu) ≤
        m * (((1 / m) * ∑ i ∈ s, eta i) ^ (1 - nu)) := by
      calc
        ∑ i ∈ s, eta i ^ (1 - nu) =
            m * ((1 / m) * ∑ i ∈ s, eta i ^ (1 - nu)) := by
          field_simp
        _ ≤ m * (((1 / m) * ∑ i ∈ s, eta i) ^ (1 - nu)) :=
          mul_le_mul_of_nonneg_left hJ' hm.le
    _ = (s.card : ℝ) ^ nu *
        (∑ i ∈ s, eta i) ^ (1 - nu) := by
      have hm0 : 0 ≤ m := hm.le
      rw [show (1 / m) * (∑ i ∈ s, eta i) =
          (∑ i ∈ s, eta i) / m by ring]
      rw [Real.div_rpow hsum0 hm0]
      have hmPowPos : 0 < m ^ (1 - nu) := Real.rpow_pos_of_pos hm _
      have hratio : m / m ^ (1 - nu) = m ^ nu := by
        apply (div_eq_iff hmPowPos.ne').2
        calc
          m = m ^ (1 : ℝ) := (Real.rpow_one m).symm
          _ = m ^ (nu + (1 - nu)) := by ring_nf
          _ = m ^ nu * m ^ (1 - nu) := Real.rpow_add hm _ _
      change m * ((∑ i ∈ s, eta i) ^ (1 - nu) /
          m ^ (1 - nu)) = m ^ nu * (∑ i ∈ s, eta i) ^ (1 - nu)
      rw [show m * ((∑ i ∈ s, eta i) ^ (1 - nu) /
          m ^ (1 - nu)) =
          (m / m ^ (1 - nu)) * (∑ i ∈ s, eta i) ^ (1 - nu) by ring,
        hratio]

/-- The cell-count factor is close to one because the exponent is tiny. -/
theorem cellCount_rpow_epsilonExponent_le {n : ℕ} {d : ℝ}
    (hn : 0 < n) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    (cellCount n : ℝ) ^ epsilonExponent n d ≤ 1 + d / 100 := by
  have hp1 : (1 : ℝ) ≤ cellCount n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (cellCount_pos n).ne')
  have hnu0 := (epsilonExponent_pos hn hd0).le
  have hnu1 := epsilonExponent_le_one hn hd1
  have hbern := rpow_one_add_le_one_add_mul_self
    (s := (cellCount n : ℝ) - 1) (by linarith) hnu0 hnu1
  ring_nf at hbern
  refine hbern.trans ?_
  unfold epsilonExponent
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < cellCount n := by
    exact_mod_cast cellCount_pos n
  have hden : 0 < 100 * (n : ℝ) * (cellCount n : ℝ) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hp0 : (cellCount n : ℝ) ≠ 0 := hpR.ne'
  have herr :
      (cellCount n : ℝ) * (d / (100 * (n : ℝ) * (cellCount n : ℝ))) -
          d / (100 * (n : ℝ) * (cellCount n : ℝ)) ≤ d / 100 := by
    field_simp
    nlinarith
  linarith

/-- Removing at least a `d/2` fraction and then taking any exponent between
`1/2` and `1` leaves a factor at most `1-d/4`. -/
theorem rpow_one_sub_le_one_sub_quarter {q d nu : ℝ}
    (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 - d / 2)
    (hnu0 : 0 ≤ nu) (hnuHalf : nu ≤ 1 / 2) :
    q ^ (1 - nu) ≤ 1 - d / 4 := by
  have hq1 : q ≤ 1 := by linarith
  have hqpos_or_zero : q = 0 ∨ 0 < q :=
    (eq_or_lt_of_le hq0).imp Eq.symm id
  have hexp : (1 / 2 : ℝ) ≤ 1 - nu := by linarith
  have hpow : q ^ (1 - nu) ≤ q ^ (1 / 2 : ℝ) := by
    rcases hqpos_or_zero with rfl | hqpos
    · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by norm_num)]
    · exact Real.rpow_le_rpow_of_exponent_ge hqpos hq1 hexp
  have hsqrt : q ^ (1 / 2 : ℝ) = Real.sqrt q := by
    rw [← Real.sqrt_eq_rpow]
  rw [hsqrt] at hpow
  refine hpow.trans ?_
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · calc
      q ≤ 1 - d / 2 := hq
      _ ≤ (1 - d / 4) ^ 2 := by nlinarith [sq_nonneg d]

/-- Quantitative heart of the outside-cell induction. -/
theorem cell_error_factor_lt_one {n : ℕ} {d q : ℝ}
    (hn : 0 < n) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 - d / 2) :
    (cellCount n : ℝ) ^ epsilonExponent n d *
        q ^ (1 - epsilonExponent n d) < 1 := by
  have hcell := cellCount_rpow_epsilonExponent_le hn hd0 hd1
  have hqpow := rpow_one_sub_le_one_sub_quarter hd0 hd1 hq0 hq
    (epsilonExponent_pos hn hd0).le (epsilonExponent_le_half hn hd1)
  have hcell0 : 0 ≤ (cellCount n : ℝ) ^ epsilonExponent n d :=
    Real.rpow_nonneg (by positivity) _
  have hqpow0 : 0 ≤ q ^ (1 - epsilonExponent n d) :=
    Real.rpow_nonneg hq0 _
  calc
    (cellCount n : ℝ) ^ epsilonExponent n d *
        q ^ (1 - epsilonExponent n d) ≤
        (1 + d / 100) * (1 - d / 4) :=
      mul_le_mul hcell hqpow hqpow0 (by linarith)
    _ < 1 := by nlinarith [sq_nonneg d]

/-- The complete weighted error estimate used after applying the induction
hypothesis to all nonempty outside cells. -/
theorem sum_twoNEpsilon_div_mul_lt {ι : Type*} [DecidableEq ι]
    {n : ℕ} {d delta : ℝ} (s : Finset ι) (eta : ι → ℝ)
    (hn : 0 < n) (hd0 : 0 < d) (hd1 : d ≤ 1) (hdelta : 0 < delta)
    (heta : ∀ i ∈ s, 0 < eta i)
    (hcard : s.card ≤ cellCount n)
    (hsum : ∑ i ∈ s, eta i ≤ 1 - d / 2) :
    ∑ i ∈ s, twoNEpsilon n d (delta / eta i) * eta i <
      twoNEpsilon n d delta := by
  by_cases hs : s.Nonempty
  · have hsum0 : 0 ≤ ∑ i ∈ s, eta i :=
      Finset.sum_nonneg fun i hi ↦ (heta i hi).le
    have hJ := sum_rpow_one_sub_le s eta hs
      (fun i hi ↦ (heta i hi).le)
      (epsilonExponent_pos hn hd0).le (epsilonExponent_le_one hn hd1)
    have hcardR : (s.card : ℝ) ≤ cellCount n := by exact_mod_cast hcard
    have hcard0 : (0 : ℝ) ≤ s.card := by positivity
    have hcardPow :
        (s.card : ℝ) ^ epsilonExponent n d ≤
          (cellCount n : ℝ) ^ epsilonExponent n d :=
      Real.rpow_le_rpow hcard0 hcardR (epsilonExponent_pos hn hd0).le
    have hfactor :
        (s.card : ℝ) ^ epsilonExponent n d *
            (∑ i ∈ s, eta i) ^ (1 - epsilonExponent n d) < 1 :=
      (mul_le_mul_of_nonneg_right hcardPow
        (Real.rpow_nonneg hsum0 _)).trans_lt
          (cell_error_factor_lt_one hn hd0 hd1 hsum0 hsum)
    have hepsPos := twoNEpsilon_pos hn hd0 hdelta
    calc
      ∑ i ∈ s, twoNEpsilon n d (delta / eta i) * eta i =
          twoNEpsilon n d delta *
            ∑ i ∈ s, eta i ^ (1 - epsilonExponent n d) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact twoNEpsilon_div_mul hd0 hdelta (heta i hi)
      _ ≤ twoNEpsilon n d delta *
          ((s.card : ℝ) ^ epsilonExponent n d *
            (∑ i ∈ s, eta i) ^ (1 - epsilonExponent n d)) :=
        mul_le_mul_of_nonneg_left hJ hepsPos.le
      _ < twoNEpsilon n d delta * 1 :=
        mul_lt_mul_of_pos_left hfactor hepsPos
      _ = twoNEpsilon n d delta := mul_one _
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs,
      twoNEpsilon_pos hn hd0 hdelta]

/-- Zero-size cells contribute zero, so the weighted estimate may be stated
directly over all coordinate cells. -/
theorem sum_twoNEpsilon_div_mul_lt_of_nonneg
    {ι : Type*} [DecidableEq ι] {n : ℕ} {d delta : ℝ}
    (s : Finset ι) (eta : ι → ℝ)
    (hn : 0 < n) (hd0 : 0 < d) (hd1 : d ≤ 1) (hdelta : 0 < delta)
    (heta : ∀ i ∈ s, 0 ≤ eta i)
    (hcard : s.card ≤ cellCount n)
    (hsum : ∑ i ∈ s, eta i ≤ 1 - d / 2) :
    ∑ i ∈ s, twoNEpsilon n d (delta / eta i) * eta i <
      twoNEpsilon n d delta := by
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
  have ht := sum_twoNEpsilon_div_mul_lt t eta hn hd0 hd1 hdelta
    hteta htcard (htsum.trans_le hsum)
  calc
    ∑ i ∈ s, twoNEpsilon n d (delta / eta i) * eta i =
        ∑ i ∈ t, twoNEpsilon n d (delta / eta i) * eta i := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i his hit
      have hi0 := heta i his
      have hnpos : ¬ 0 < eta i := by
        intro hipos
        exact hit (Finset.mem_filter.mpr ⟨his, hipos⟩)
      simp [le_antisymm (not_lt.mp hnpos) hi0]
    _ < twoNEpsilon n d delta := ht

end

end Erdos186.CFP.Bilu.Section5EpsilonCalc

#print axioms Erdos186.CFP.Bilu.Section5EpsilonCalc.sum_twoNEpsilon_div_mul_lt
