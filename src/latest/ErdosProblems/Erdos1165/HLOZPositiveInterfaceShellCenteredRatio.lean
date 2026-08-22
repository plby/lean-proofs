/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalWindowRatio
import ErdosProblems.Erdos1165.HLOZShellZeroReplacementWindows

/-!
# Shell-centred mass comparison for the positive interface

The external local time relevant to physical deficit shell `shell` is centred
at `m - shell * width`, rather than at `m`.  On that event, both rows in the
adjacent pair lie in the same fixed local-CLT window used by the literal
shell-zero argument.  This gives a uniform (deliberately coarse) ratio which
is independent of the shell and of the level.
-/

open scoped BigOperators

namespace Erdos1165.HLOZPositiveInterfaceShellCenteredRatio

open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroReplacementWindows
open NegativeBinomial
open NegativeBinomialLocalCLT
open ScreeningInstantiation
open SmallWindow

noncomputable section

/-- Both members of an adjacent physical pair are within two strip widths
of the centre belonging to the nearer strip. -/
theorem acceptedPhysicalFailure_shellCentered_deviation_le
    {m width i shell row v : ℕ} {centerRadius : ℝ}
    (hwidth : 0 < width)
    (hfit : (shell + 2) * width ≤ m)
    (hrow : row = shell ∨ row = shell + 1)
    (hcenter :
      |((m - shell * width : ℕ) : ℝ) -
          (16 / 15 : ℝ) * (i : ℝ)| ≤ centerRadius)
    (hv : v ∈ acceptedPhysicalDeficitFailureWindow m width i row) :
    |deviation i v| ≤ centerRadius + 2 * (width : ℝ) := by
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hv
  have hrowLe : row ≤ shell + 1 := by rcases hrow with rfl | rfl <;> omega
  have hdefLo : row * width ≤ m - (i + v) := by
    rw [← Nat.le_div_iff_mul_le hwidth, hv.2]
  have hdefHi : m - (i + v) < (row + 1) * width := by
    rw [← Nat.div_lt_iff_lt_mul hwidth, hv.2]
    omega
  have htotal : i + v ≤ m := Nat.le_of_lt hv.1
  have hshellRow : shell * width ≤ row * width := by
    apply Nat.mul_le_mul_right width
    rcases hrow with rfl | rfl <;> omega
  have hrowTwo : (row + 1) * width ≤ (shell + 2) * width := by
    apply Nat.mul_le_mul_right width
    exact Nat.add_le_add_right hrowLe 1
  have hshellFit : shell * width ≤ m :=
    (Nat.mul_le_mul_right width (show shell ≤ shell + 2 by omega)).trans hfit
  have hdefLoShell : shell * width ≤ m - (i + v) :=
    hshellRow.trans hdefLo
  have hdefHiTwo : m - (i + v) < (shell + 2) * width :=
    hdefHi.trans_le hrowTwo
  have hcenterTotal : i + v ≤ m - shell * width := by omega
  have htwo : (shell + 2) * width = shell * width + 2 * width := by ring
  have hgap' : (m - (i + v)) - shell * width ≤ 2 * width := by
    rw [htwo] at hdefHiTwo
    omega
  have hgap : (m - shell * width) - (i + v) ≤ 2 * width := by
    simpa only [Nat.sub_sub, add_comm] using hgap'
  have hcenterTotalR : (i : ℝ) + (v : ℝ) ≤
      ((m - shell * width : ℕ) : ℝ) := by
    exact_mod_cast hcenterTotal
  have hgapR : ((m - shell * width : ℕ) : ℝ) -
      ((i : ℝ) + (v : ℝ)) ≤ 2 * (width : ℝ) := by
    have hcast : (((m - shell * width) - (i + v) : ℕ) : ℝ) ≤
        ((2 * width : ℕ) : ℝ) := by exact_mod_cast hgap
    rw [Nat.cast_sub hcenterTotal] at hcast
    push_cast at hcast
    exact hcast
  have hdevEq : deviation i v =
      ((i : ℝ) + (v : ℝ)) - (16 / 15 : ℝ) * (i : ℝ) := by
    unfold deviation
    ring
  rw [hdevEq, abs_le]
  rw [abs_le] at hcenter
  constructor <;> linarith

/-- The two adjacent physical rows have a level- and shell-independent mass
ratio on the shell-centred balance event.  The factor `4/3` is only the exact
cardinality correction for the clipped first row; the analytic ratio is the
fixed constant already checked for the literal shell-zero comparison. -/
theorem acceptedPhysicalAdjacentWindowMass_le_shellCenteredConstant
    {m i shell : ℕ}
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ i)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hcenter :
      |((m - shell * shellWidth48 m : ℕ) : ℝ) -
          (16 / 15 : ℝ) * (i : ℝ)| ≤ geometricDeviation m) :
    windowMass i
        (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
          (shell + 1)) ≤
      (shellZeroLocalRatioConstant * (4 / 3 : ℝ)) *
        windowMass i
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i shell) := by
  let upper := acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
    (shell + 1)
  let lower := acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i shell
  by_cases hupper : upper.Nonempty
  · have hlower : lower.Nonempty :=
      acceptedPhysicalDeficitFailureWindow_nonempty_of_succ_nonempty
        (by omega) hupper
    have hiPos : 0 < i := (harithmetic.2.2 i hthick).1
    have hmoderate := (harithmetic.2.2 i hthick).2.1
    have hratio := (harithmetic.2.2 i hthick).2.2
    have hraw : windowMass i upper ≤
        (adjacentLocalRatio i (literalShellZeroDeviationRadius m)
            (shellZeroWindowSeparation (shellWidth48 m)) *
          (upper.card : ℝ) / (lower.card : ℝ)) * windowMass i lower := by
      apply adjacentWindowMass_le_adjacentLocalRatio_mul_cardRatio hiPos
        (by
          unfold literalShellZeroDeviationRadius shellZeroDeviationRadius
            shellZeroCenterRadius
          exact add_nonneg (Nat.cast_nonneg _)
            (add_nonneg (Nat.cast_nonneg _) (geometricDeviation_nonneg m)))
        (shellZeroWindowSeparation_nonneg _) hmoderate hlower
      · intro v hv
        have hdev := acceptedPhysicalFailure_shellCentered_deviation_le
          (by omega) hfit (Or.inr rfl) hcenter hv
        have hD : geometricDeviation m + 2 * (shellWidth48 m : ℝ) =
            literalShellZeroDeviationRadius m := by
          unfold literalShellZeroDeviationRadius shellZeroDeviationRadius
            shellZeroCenterRadius
          ring
        rwa [hD] at hdev
      · intro v hv
        have hdev := acceptedPhysicalFailure_shellCentered_deviation_le
          (by omega) hfit (Or.inl rfl) hcenter hv
        have hD : geometricDeviation m + 2 * (shellWidth48 m : ℝ) =
            literalShellZeroDeviationRadius m := by
          unfold literalShellZeroDeviationRadius shellZeroDeviationRadius
            shellZeroCenterRadius
          ring
        rwa [hD] at hdev
      · intro u hu l hl
        simpa [shellZeroWindowSeparation,
          physicalAdjacentWindowSeparation] using
          (acceptedPhysicalFailure_deviation_sub_le (by omega) hu hl)
    have hcard : (upper.card : ℝ) / (lower.card : ℝ) ≤ 4 / 3 :=
      acceptedPhysicalAdjacent_card_ratio_le_four_thirds_global hwidthFour
    have hcoefficient :
        adjacentLocalRatio i (literalShellZeroDeviationRadius m)
              (shellZeroWindowSeparation (shellWidth48 m)) *
            (upper.card : ℝ) / (lower.card : ℝ) ≤
          shellZeroLocalRatioConstant * (4 / 3 : ℝ) := by
      rw [mul_div_assoc]
      exact mul_le_mul hratio hcard
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        shellZeroLocalRatioConstant_pos.le
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoefficient
      (windowMass_nonneg i lower))
  · have hempty : upper = ∅ := Finset.not_nonempty_iff_eq_empty.mp hupper
    change windowMass i upper ≤
      (shellZeroLocalRatioConstant * (4 / 3 : ℝ)) * windowMass i lower
    rw [hempty]
    simp only [windowMass, Finset.sum_empty]
    exact mul_nonneg
      (mul_nonneg shellZeroLocalRatioConstant_pos.le (by norm_num))
      (windowMass_nonneg i lower)

/-- Contrapositive form used by the exceptional-pair split.  Once the two
displayed rows fit and the external count is in the thick half of the level,
failure of the uniform adjacent-row comparison forces the shell centre
outside the geometric-deviation window. -/
theorem geometricDeviation_lt_shellCenter_of_not_windowRatio
    {m i shell : ℕ}
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ i)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hbad : ¬ windowMass i
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
            (shell + 1)) ≤
        positiveInterfaceRatioConstant * windowMass i
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i shell)) :
    geometricDeviation m <
      |((m - shell * shellWidth48 m : ℕ) : ℝ) -
        (16 / 15 : ℝ) * (i : ℝ)| := by
  by_contra hnot
  have hcenter :
      |((m - shell * shellWidth48 m : ℕ) : ℝ) -
          (16 / 15 : ℝ) * (i : ℝ)| ≤ geometricDeviation m :=
    le_of_not_gt hnot
  apply hbad
  simpa only [positiveInterfaceRatioConstant, shellZeroLocalRatioConstant]
    using acceptedPhysicalAdjacentWindowMass_le_shellCenteredConstant
      harithmetic hwidthFour hthick hfit hcenter

end

end Erdos1165.HLOZPositiveInterfaceShellCenteredRatio
