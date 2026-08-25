import Util.MaynardBFT.LargeFiberAbel
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Quantitative lower bounds for the large coordinate fiber
-/

namespace MaynardBFT.Sieve

open Erdos6.Maynard

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

theorem mul_log_one_add_le_log_one_add_mul
    {c x : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hx : 0 ≤ x) :
    c * Real.log (1 + x) ≤ Real.log (1 + c * x) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1 + x ∈ Set.Ioi (0 : ℝ) from
      Set.mem_Ioi.mpr (by linarith))
    (sub_nonneg.mpr hc1) hc0 (by ring : (1 - c) + c = (1 : ℝ))
  have h' : c * Real.log (1 + x) ≤
      Real.log ((1 - c) * 1 + c * (1 + x)) := by
    simpa only [Real.log_one, smul_eq_mul, mul_zero, zero_add] using h
  convert h' using 1 <;> ring

theorem integral_largeFiberProfile_interval {B : ℝ} (hB : 0 ≤ B) :
    (∫ x : ℝ in (0 : ℝ)..B, largeFiberProfile x) =
      Real.log (1 + largeFiberSlope * B) / largeFiberSlope := by
  calc
    (∫ x : ℝ in (0 : ℝ)..B, largeFiberProfile x) =
        ∫ x : ℝ in (0 : ℝ)..B, largeG (largeK * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 ≤ x := by
        rw [Set.uIcc_of_le hB] at hx
        exact hx.1
      exact largeFiberProfile_eq_largeG hx0
    _ = Real.log (1 + largeA * (largeK : ℝ) * B) /
        (largeA * (largeK : ℝ)) := integral_largeG_interval hB
    _ = Real.log (1 + largeFiberSlope * B) / largeFiberSlope := by
      rfl

theorem cutoff_mul_largeShortMass_le_fiberIntegral
    {c q : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hq : c * ((1 : ℝ) / 8) ≤ q) :
    c * largeShortMass ≤
      ∫ x : ℝ in (0 : ℝ)..q, largeFiberProfile x := by
  have hq0 : 0 ≤ q :=
    (mul_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 1 / 8)).trans hq
  have hslope : 0 < largeFiberSlope := largeFiberSlope_pos
  have hx : 0 ≤ largeFiberSlope * ((1 : ℝ) / 8) := by positivity
  have hconc := mul_log_one_add_le_log_one_add_mul hc0 hc1 hx
  have harg :
      1 + c * (largeFiberSlope * ((1 : ℝ) / 8)) ≤
        1 + largeFiberSlope * q := by
    nlinarith
  have hargPos : 0 < 1 + c * (largeFiberSlope * ((1 : ℝ) / 8)) := by
    positivity
  have hlogMono :
      Real.log (1 + c * (largeFiberSlope * ((1 : ℝ) / 8))) ≤
        Real.log (1 + largeFiberSlope * q) :=
    Real.strictMonoOn_log.monotoneOn hargPos
      (show 1 + largeFiberSlope * q ∈ Set.Ioi (0 : ℝ) from
        Set.mem_Ioi.mpr (by positivity)) harg
  rw [largeShortMass_eq, integral_largeFiberProfile_interval hq0]
  change c * (Real.log
      (1 + largeFiberSlope * ((1 : ℝ) / 8)) / largeFiberSlope) ≤ _
  calc
    c * (Real.log (1 + largeFiberSlope * (1 / 8)) / largeFiberSlope) =
        (c * Real.log (1 + largeFiberSlope * (1 / 8))) /
          largeFiberSlope := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (hconc.trans hlogMono) hslope.le

theorem coordinateFiberEndpoint_ratio_ge_complement_sub
    {H : Finset ℕ} {R W : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hR : 1 < R)
    (hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)) :
    1 - Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r) /
          Real.log R - Real.log 3 / Real.log R ≤
      Real.log (BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
        (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r)) /
          Real.log R := by
  let P := BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m r
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R P
  have hP : 0 < P :=
    BoundedGaps.Maynard.maynardS2OffCoordinateProduct_pos m r hr
  have hQnat : 1 < Q := by simpa [Q, P] using hQ
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQnat
  have hPone : 1 ≤ P := hP
  have hRpos : 0 < R := Nat.zero_lt_of_lt hR
  have hRlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hRQP : R - 1 < (Q + 1) * P := by
    unfold Q BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint
    exact (Nat.div_lt_iff_lt_mul hP).mp
      (Nat.lt_succ_self ((R - 1) / P))
  have htwice : Q + 1 ≤ 2 * Q := by omega
  have hRle : R ≤ 3 * Q * P := by
    have hQPP : 2 ≤ Q * P := by
      simpa using Nat.mul_le_mul hQnat hPone
    have hQPone : 1 ≤ Q * P := by omega
    have htwiceMul : (Q + 1) * P ≤ (2 * Q) * P :=
      Nat.mul_le_mul_right P htwice
    have hlt : R < 2 * Q * P + 1 := by
      calc
        R = (R - 1) + 1 := by omega
        _ < (Q + 1) * P + 1 := Nat.add_lt_add_right hRQP 1
        _ ≤ 2 * Q * P + 1 := by
          exact Nat.add_le_add_right
            (by simpa [Nat.mul_assoc] using htwiceMul) 1
    have hplus : 2 * Q * P + 1 ≤ 3 * Q * P := by
      calc
        2 * Q * P + 1 = 2 * (Q * P) + 1 := by ring
        _ ≤ 2 * (Q * P) + Q * P := Nat.add_le_add_left hQPone _
        _ = 3 * Q * P := by ring
    exact le_of_lt (hlt.trans_le hplus)
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hRpos
  have h3QP : (0 : ℝ) < 3 * Q * P := by positivity
  have hRleReal : (R : ℝ) ≤ 3 * Q * P := by exact_mod_cast hRle
  have hmono := Real.strictMonoOn_log.monotoneOn hRreal h3QP hRleReal
  rw [show (3 : ℝ) * Q * P = 3 * ((Q : ℝ) * P) by ring,
    Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (by exact_mod_cast (Nat.mul_pos hQpos hP).ne'),
    Real.log_mul (by exact_mod_cast hQpos.ne')
      (by exact_mod_cast hP.ne')] at hmono
  have hdiff : Real.log R - Real.log P - Real.log Q ≤ Real.log 3 := by
    linarith
  calc
    1 - Real.log P / Real.log R - Real.log 3 / Real.log R =
        (Real.log R - Real.log P - Real.log 3) / Real.log R := by
      field_simp [hRlog.ne']
    _ ≤ Real.log Q / Real.log R := by
      apply div_le_div_of_nonneg_right _ hRlog.le
      linarith

theorem largeOuterCutoff_mul_eighth_le_complement
    {s eps : ℝ} (heps : eps ≤ (1 : ℝ) / 56)
    (hq0 : 0 ≤ q)
    (hq : 1 - s - eps ≤ q) :
    largeOuterCutoff s * ((1 : ℝ) / 8) ≤ q := by
  by_cases hs : s ≤ (6 : ℝ) / 7
  · rw [largeOuterCutoff_eq_one hs]
    linarith
  · by_cases hs' : (7 : ℝ) / 8 ≤ s
    · rw [largeOuterCutoff_eq_zero hs']
      simpa using hq0
    · have hslo : (6 : ℝ) / 7 < s := lt_of_not_ge hs
      have hshi : s < (7 : ℝ) / 8 := lt_of_not_ge hs'
      have hcut : largeOuterCutoff s = 49 - 56 * s := by
        unfold largeOuterCutoff
        have h0 : 0 ≤ 49 - 56 * s := by linarith
        have h1 : 49 - 56 * s ≤ 1 := by linarith
        rw [max_eq_right h0, min_eq_right h1]
      rw [hcut]
      linarith

end

end MaynardBFT.Sieve
