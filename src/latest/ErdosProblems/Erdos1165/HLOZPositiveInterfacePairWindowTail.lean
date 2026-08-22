/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZNegativeBinomialTruncation
import ErdosProblems.Erdos1165.HLOZPositiveInterfaceShellCenteredRatio
import ErdosProblems.Erdos1165.HLOZSharpWindowProductClosure

/-!
# Tail payment for a failed positive-interface window ratio

Failure of the shell-centred adjacent-window comparison places the centre of
the displayed pair outside the geometric moderate-deviation window.  Since
the two physical rows lie within two strip widths of that centre, and the
strip width is eventually much smaller than the deviation, their whole
negative-binomial mass belongs to one of the two Chernoff tails.
-/

open Filter

namespace Erdos1165.HLOZPositiveInterfacePairWindowTail

open ExternalProposition44
open HLOZNegativeBinomialTruncation
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfaceShellCenteredRatio
open HLOZProposition48Candidates
open HLOZSharpWindowProductClosure
open ScreeningInstantiation
open SmallWindow

noncomputable section

/-- The `m^(11/32)` strip width is eventually at most one quarter of the
`9 m^(21/32)` geometric deviation. -/
theorem eventually_four_shellWidth48_le_geometricDeviation :
    ∀ᶠ m : ℕ in atTop,
      4 * (shellWidth48 m : ℝ) ≤ geometricDeviation m := by
  have hpower := eventually_const_mul_nat_rpow_le
    (8 / 9 : ℝ) kappaOne (1 - kappaOne) (by norm_num [kappaOne])
  filter_upwards [eventually_shellWidth48_cast_le_two_rpow, hpower] with
      m hwidth hpowerM
  unfold geometricDeviation
  nlinarith

/-- The strip width is in fact negligible compared with the geometric
deviation.  This sharper eventual comparison retains seventeen full copies
of the balancedness rate after allowing for the two displayed rows. -/
theorem eventually_twentyFour_shellWidth48_le_geometricDeviation :
    ∀ᶠ m : ℕ in atTop,
      24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m := by
  have hpower := eventually_const_mul_nat_rpow_le
    (16 / 3 : ℝ) kappaOne (1 - kappaOne) (by norm_num [kappaOne])
  filter_upwards [eventually_shellWidth48_cast_le_two_rpow, hpower] with
      m hwidth hpowerM
  unfold geometricDeviation
  nlinarith

/-- Every total in either displayed row lies at most two strip widths below
the centre `m - shell * width`. -/
theorem acceptedPhysicalFailure_total_mem_shellCenter_interval
    {m width i shell row v : ℕ}
    (hwidth : 0 < width)
    (hfit : (shell + 2) * width ≤ m)
    (hrow : row = shell ∨ row = shell + 1)
    (hv : v ∈ acceptedPhysicalDeficitFailureWindow m width i row) :
    (((m - shell * width : ℕ) : ℝ) - 2 * (width : ℝ) <
        (i : ℝ) + (v : ℝ)) ∧
      ((i : ℝ) + (v : ℝ) ≤ ((m - shell * width : ℕ) : ℝ)) := by
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hv
  have hrowLe : row ≤ shell + 1 := by
    rcases hrow with rfl | rfl <;> omega
  have hdefLo : row * width ≤ m - (i + v) := by
    rw [← Nat.le_div_iff_mul_le hwidth, hv.2]
  have hdefHi : m - (i + v) < (row + 1) * width := by
    rw [← Nat.div_lt_iff_lt_mul hwidth, hv.2]
    omega
  have hshellRow : shell * width ≤ row * width := by
    apply Nat.mul_le_mul_right width
    rcases hrow with rfl | rfl <;> omega
  have hrowTwo : (row + 1) * width ≤ (shell + 2) * width := by
    apply Nat.mul_le_mul_right width
    exact Nat.add_le_add_right hrowLe 1
  have hshellFit : shell * width ≤ m :=
    (Nat.mul_le_mul_right width (show shell ≤ shell + 2 by omega)).trans hfit
  have htotal : i + v ≤ m := Nat.le_of_lt hv.1
  have hcenterTotal : i + v ≤ m - shell * width := by
    have : shell * width ≤ m - (i + v) := hshellRow.trans hdefLo
    omega
  have hdefLoShell : shell * width ≤ m - (i + v) :=
    hshellRow.trans hdefLo
  have hdefHiTwo : m - (i + v) < (shell + 2) * width :=
    hdefHi.trans_le hrowTwo
  have htwo : (shell + 2) * width = shell * width + 2 * width := by ring
  have hgap : (m - shell * width) - (i + v) < 2 * width := by
    have hgap' : (m - (i + v)) - shell * width < 2 * width := by
      rw [htwo] at hdefHiTwo
      omega
    simpa only [Nat.sub_sub, add_comm] using hgap'
  have hcenterTotalR : (i : ℝ) + (v : ℝ) ≤
      ((m - shell * width : ℕ) : ℝ) := by
    exact_mod_cast hcenterTotal
  have hgapR : ((m - shell * width : ℕ) : ℝ) -
      ((i : ℝ) + (v : ℝ)) < 2 * (width : ℝ) := by
    have hcast : (((m - shell * width) - (i + v) : ℕ) : ℝ) <
        ((2 * width : ℕ) : ℝ) := by exact_mod_cast hgap
    rw [Nat.cast_sub hcenterTotal] at hcast
    push_cast at hcast
    exact hcast
  constructor <;> linarith

/-- The exponent obtained from half the geometric deviation still contains
five full copies of the balancedness rate. -/
theorem seventeen_balanceRateScale_le_sharp_geometric_rate
    {m : ℕ} (hm : 0 < m) :
    17 * balanceRateScale m ≤
      ((11 / 12 : ℝ) * geometricDeviation m) ^ 2 /
        (4 * (m : ℝ)) := by
  rw [show ((11 / 12 : ℝ) * geometricDeviation m) ^ 2 /
        (4 * (m : ℝ)) =
      (121 / 144 : ℝ) *
        (geometricDeviation m ^ 2 / (4 * (m : ℝ))) by ring,
    geometricDeviation_sq_div_four hm]
  have hnonneg := balanceRateScale_nonneg m
  nlinarith

/-- If the shell centre is outside the geometric window, the union of its
two displayed physical rows has exponentially small raw mass. -/
theorem acceptedPhysicalPairWindowMass_le_of_shellCenter_far
    {m i shell : ℕ}
    (hm : 0 < m)
    (hi : 0 < i)
    (him : i ≤ m)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hwidthDeviation :
      24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hfar : geometricDeviation m <
      |((m - shell * shellWidth48 m : ℕ) : ℝ) -
        (16 / 15 : ℝ) * (i : ℝ)|) :
    windowMass i
        (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i shell ∪
          acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
            (shell + 1)) ≤
      Real.exp (-17 * balanceRateScale m) := by
  let center : ℝ := ((m - shell * shellWidth48 m : ℕ) : ℝ)
  let meanTotal : ℝ := (16 / 15 : ℝ) * (i : ℝ)
  let a : ℝ := (11 / 12 : ℝ) * geometricDeviation m
  have hwidthPos : 0 < shellWidth48 m := by
    unfold shellWidth48
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact mul_nonneg (by norm_num) (geometricDeviation_nonneg m)
  have ham : a ≤ (m : ℝ) := by
    dsimp only [a]
    have hdev0 := geometricDeviation_nonneg m
    nlinarith
  have hrate : 17 * balanceRateScale m ≤ a ^ 2 / (4 * (m : ℝ)) := by
    simpa only [a] using seventeen_balanceRateScale_le_sharp_geometric_rate hm
  rw [lt_abs] at hfar
  rcases hfar with hupper | hlower
  · let k := Nat.ceil ((i : ℝ) / 15 + a)
    have hwindow : ∀ v ∈
        acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i shell ∪
          acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
            (shell + 1), k ≤ v := by
      intro v hv
      rw [Finset.mem_union] at hv
      have hinterval :
          (((m - shell * shellWidth48 m : ℕ) : ℝ) -
              2 * (shellWidth48 m : ℝ) < (i : ℝ) + (v : ℝ)) ∧
            (i : ℝ) + (v : ℝ) ≤
              ((m - shell * shellWidth48 m : ℕ) : ℝ) := by
        rcases hv with hv | hv
        · exact acceptedPhysicalFailure_total_mem_shellCenter_interval
            hwidthPos hfit (Or.inl rfl) hv
        · exact acceptedPhysicalFailure_total_mem_shellCenter_interval
            hwidthPos hfit (Or.inr rfl) hv
      apply Nat.ceil_le.mpr
      dsimp only [a]
      have hwidthSharp : 2 * (shellWidth48 m : ℝ) ≤
          geometricDeviation m / 12 := by nlinarith
      linarith
    have hraw := windowMass_le_exp_neg_upper_ambient hm hi him ha0 ham
      (Nat.le_ceil _) _ hwindow
    refine hraw.trans ?_
    apply Real.exp_le_exp.mpr
    have hneg := neg_le_neg hrate
    simpa only [neg_div, neg_mul] using hneg
  · by_cases hempty :
      acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i shell ∪
          acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
            (shell + 1) = ∅
    · rw [hempty, windowMass]
      simp only [Finset.sum_empty]
      positivity
    · obtain ⟨v0, hv0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      rw [Finset.mem_union] at hv0
      have hinterval0 :
          (((m - shell * shellWidth48 m : ℕ) : ℝ) -
              2 * (shellWidth48 m : ℝ) < (i : ℝ) + (v0 : ℝ)) ∧
            (i : ℝ) + (v0 : ℝ) ≤
              ((m - shell * shellWidth48 m : ℕ) : ℝ) := by
        rcases hv0 with hv0 | hv0
        · exact acceptedPhysicalFailure_total_mem_shellCenter_interval
            hwidthPos hfit (Or.inl rfl) hv0
        · exact acceptedPhysicalFailure_total_mem_shellCenter_interval
            hwidthPos hfit (Or.inr rfl) hv0
      have hmeanNonneg : 0 ≤ (i : ℝ) / 15 - a := by
        dsimp only [a]
        have hv0Nonneg : (0 : ℝ) ≤ v0 := by positivity
        linarith
      let k := Nat.floor ((i : ℝ) / 15 - a)
      have hwindow : ∀ v ∈
          acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i shell ∪
            acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
              (shell + 1), v ≤ k := by
        intro v hv
        apply Nat.le_floor
        rw [Finset.mem_union] at hv
        have hinterval :
            (((m - shell * shellWidth48 m : ℕ) : ℝ) -
                2 * (shellWidth48 m : ℝ) < (i : ℝ) + (v : ℝ)) ∧
              (i : ℝ) + (v : ℝ) ≤
                ((m - shell * shellWidth48 m : ℕ) : ℝ) := by
          rcases hv with hv | hv
          · exact acceptedPhysicalFailure_total_mem_shellCenter_interval
              hwidthPos hfit (Or.inl rfl) hv
          · exact acceptedPhysicalFailure_total_mem_shellCenter_interval
              hwidthPos hfit (Or.inr rfl) hv
        dsimp only [a]
        linarith
      have hraw := windowMass_le_exp_neg_lower_ambient hm hi him ha0 ham
        (Nat.floor_le hmeanNonneg) _ hwindow
      refine hraw.trans ?_
      apply Real.exp_le_exp.mpr
      have hneg := neg_le_neg hrate
      simpa only [neg_div, neg_mul] using hneg

/-- Direct form used by an arithmetic-obstruction witness: failure of the
adjacent-row ratio implies the preceding Chernoff payment. -/
theorem acceptedPhysicalPairWindowMass_le_of_not_windowRatio
    {m i shell : ℕ}
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ i)
    (him : i ≤ m)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hwidthDeviation :
      24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hbad : ¬ windowMass i
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
            (shell + 1)) ≤
        HLOZProposition48Candidates.positiveInterfaceRatioConstant *
          windowMass i
            (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
              shell)) :
    windowMass i
        (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i shell ∪
          acceptedPhysicalDeficitFailureWindow m (shellWidth48 m) i
            (shell + 1)) ≤
      Real.exp (-17 * balanceRateScale m) := by
  have hi : 0 < i := (harithmetic.2.2 i hthick).1
  exact acceptedPhysicalPairWindowMass_le_of_shellCenter_far
    (by
      have hwidthPos : 0 < shellWidth48 m := by omega
      omega)
    hi him hfit hwidthDeviation hdeviationLevel
      (geometricDeviation_lt_shellCenter_of_not_windowRatio harithmetic
        hwidthFour hthick hfit hbad)

end

end Erdos1165.HLOZPositiveInterfacePairWindowTail
