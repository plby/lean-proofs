/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.BranchNumerics

/-! # Branch closure at the rounded geometric scales -/

open Set

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

def branchLogScale (delta : ℝ) : ℝ :=
  (dyadicLevelCount delta : ℝ) + 1

def branchLogCoefficient : ℝ :=
  2 / Real.log 2 + 1

theorem branchLogScale_pos (delta : ℝ) : 0 < branchLogScale delta := by
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one

theorem branchLogScale_le {delta : ℝ}
    (hdelta : 0 < delta) (hquarter : delta ≤ 1 / 4) :
    branchLogScale delta ≤ branchLogCoefficient * Real.log (1 / delta) := by
  have hlevel := dyadicLevelCount_cast_le_of_le_quarter hdelta hquarter
  have hinv : (4 : ℝ) ≤ 1 / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hlogFour := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hinv
  have hlogOne : 1 ≤ Real.log (1 / delta) := by
    have : (1 : ℝ) < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)]
      exact Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  simp only [branchLogScale, branchLogCoefficient]
  nlinarith

theorem graphWidth_rpow {d : ℕ} {epsilon c0 delta : ℝ}
    (hc0 : 0 < c0) (hdelta : 0 < delta) :
    graphWidth epsilon c0 delta ^ boundaryDimension d =
      c0 ^ boundaryDimension d *
        delta ^ (tau epsilon * boundaryDimension d) := by
  rw [graphWidth, Real.mul_rpow hc0.le
    (Real.rpow_nonneg hdelta.le _)]
  rw [← Real.rpow_mul hdelta.le]

theorem realGridScale_rpow (d : ℕ) {delta a : ℝ}
    (hdelta : 0 < delta) :
    realGridScale d delta ^ a =
      delta ^ (-(gridRate d * a)) := by
  rw [realGridScale, ← Real.rpow_mul hdelta.le]
  congr 1
  ring

/-- Simultaneous low/high closure with the exact real PZ scale.  The integral
graph mesh is compared to this scale only in the geometric caller. -/
theorem exists_deltaZero_branchClosuresAtScales
    {d : ℕ} {epsilon : ℝ}
    (hd : 2 ≤ d) (hepsilon : 0 < epsilon)
    (hepsilonLe : epsilon ≤ 1 / ((d : ℝ) + 1))
    {c C cK c0 : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hcK : 0 < cK) (hc0 : 0 < c0) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        ∀ K : ℝ, 0 < K → cK ≤ K * branchLogScale delta →
          (K ≤ realGridScale d delta ^ alpha d →
            etaLow d C (graphWidth epsilon c0 delta) K
                (realGridScale d delta) (branchLogScale delta) ∈
              Icc delta (delta ^ tau epsilon) ∧
            etaLow d C (graphWidth epsilon c0 delta) K
                (realGridScale d delta) (branchLogScale delta) ^
                  (alpha d + epsilon) ≤
              capturedFraction d c (graphWidth epsilon c0 delta) K
                (realGridScale d delta) (branchLogScale delta)) ∧
          (realGridScale d delta ^ alpha d ≤ K →
            etaHigh d C (graphWidth epsilon c0 delta)
                (realGridScale d delta) ∈
              Icc delta (delta ^ tau epsilon) ∧
            etaHigh d C (graphWidth epsilon c0 delta)
                (realGridScale d delta) ^ (alpha d + epsilon) ≤
              capturedFraction d c (graphWidth epsilon c0 delta) K
                (realGridScale d delta) (branchLogScale delta)) := by
  let D := branchLogCoefficient
  let A1 := lowDensityCoefficient d epsilon c C cK c0 * D ^ (2 : ℕ)
  let A2 := highDensityCoefficient d epsilon c C c0 * D
  let A3 := etaUpperCoefficient d C c0 * D
  let A4 := etaUpperCoefficient d C c0
  let A5 := lowEtaLowerCoefficient d C cK c0
  let A6 := highEtaLowerCoefficient d C c0
  obtain ⟨deltaPower, hpowerPos, hpowerOne, hpower⟩ :=
    exists_deltaZero_branchPowerBounds hd hepsilon hepsilonLe
      A1 A2 A3 A4 A5 A6
  let deltaZero := min deltaPower (1 / 4)
  refine ⟨deltaZero, by positivity, by
    calc deltaZero ≤ 1 / 4 := min_le_right _ _
         _ < 1 := by norm_num, ?_⟩
  intro delta hdelta hsmall K hK hcKL
  have hdeltaOne : delta ≤ 1 :=
    hsmall.le.trans (min_le_right _ _) |>.trans (by norm_num)
  have hquarter : delta ≤ 1 / 4 := hsmall.le.trans (min_le_right _ _)
  have hL := branchLogScale_le hdelta hquarter
  have hLpos := branchLogScale_pos delta
  have hu := graphWidth_pos (epsilon := epsilon) hc0 hdelta
  have hm := realGridScale_pos d hdelta
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6⟩ :=
    hpower delta hdelta (hsmall.trans_le (min_le_left _ _))
  have hLowBase : etaLowBaseline d C cK
      (graphWidth epsilon c0 delta) (realGridScale d delta) =
      (C * cK * c0 ^ boundaryDimension d) *
        delta ^ lowBaseRate d epsilon := by
    rw [etaLowBaseline, graphWidth_rpow hc0 hdelta,
      realGridScale_rpow d hdelta]
    rw [Real.rpow_neg hdelta.le, div_inv_eq_mul]
    calc
      C * cK * (c0 ^ boundaryDimension d *
            delta ^ (tau epsilon * boundaryDimension d)) *
          delta ^ (gridRate d * ((d : ℝ) + 1)) =
        (C * cK * c0 ^ boundaryDimension d) *
          (delta ^ (tau epsilon * boundaryDimension d) *
            delta ^ (gridRate d * ((d : ℝ) + 1))) := by ring
      _ = (C * cK * c0 ^ boundaryDimension d) *
          delta ^ (tau epsilon * boundaryDimension d +
            gridRate d * ((d : ℝ) + 1)) := by rw [Real.rpow_add hdelta]
      _ = _ := by rfl
  have hHighBase : etaHigh d C (graphWidth epsilon c0 delta)
      (realGridScale d delta) =
      (C * c0 ^ boundaryDimension d) *
        delta ^ highBaseRate d epsilon := by
    rw [etaHigh, graphWidth_rpow hc0 hdelta,
      realGridScale_rpow d hdelta]
    rw [Real.rpow_neg hdelta.le, div_inv_eq_mul]
    calc
      C * (c0 ^ boundaryDimension d *
            delta ^ (tau epsilon * boundaryDimension d)) *
          delta ^ (gridRate d * (d : ℝ)) =
        (C * c0 ^ boundaryDimension d) *
          (delta ^ (tau epsilon * boundaryDimension d) *
            delta ^ (gridRate d * (d : ℝ))) := by ring
      _ = (C * c0 ^ boundaryDimension d) *
          delta ^ (tau epsilon * boundaryDimension d +
            gridRate d * (d : ℝ)) := by rw [Real.rpow_add hdelta]
      _ = _ := by rfl
  have hLowLower : delta ≤ etaLowBaseline d C cK
      (graphWidth epsilon c0 delta) (realGridScale d delta) := by
    rw [hLowBase]
    have hcoefPos : 0 < C * cK * c0 ^ boundaryDimension d := by positivity
    have hbound : (C * cK * c0 ^ boundaryDimension d)⁻¹ *
        delta ^ (1 - lowBaseRate d epsilon) ≤ 1 := by
      simpa [A5, lowEtaLowerCoefficient, lowLowerSaving] using hB5
    rw [Real.rpow_sub hdelta] at hbound
    have hfrac : delta /
        (delta ^ lowBaseRate d epsilon *
          (C * cK * c0 ^ boundaryDimension d)) ≤ 1 := by
      calc
        delta / (delta ^ lowBaseRate d epsilon *
              (C * cK * c0 ^ boundaryDimension d)) =
            (C * cK * c0 ^ boundaryDimension d)⁻¹ *
              (delta / delta ^ lowBaseRate d epsilon) := by
              field_simp
        _ ≤ 1 := by simpa only [Real.rpow_one] using hbound
    have := (div_le_one
      (mul_pos (Real.rpow_pos_of_pos hdelta _) hcoefPos)).mp hfrac
    simpa [mul_comm] using this
  have hHighLower : delta ≤ etaHigh d C
      (graphWidth epsilon c0 delta) (realGridScale d delta) := by
    rw [hHighBase]
    have hcoefPos : 0 < C * c0 ^ boundaryDimension d := by positivity
    have hbound : (C * c0 ^ boundaryDimension d)⁻¹ *
        delta ^ (1 - highBaseRate d epsilon) ≤ 1 := by
      simpa [A6, highEtaLowerCoefficient, highLowerSaving] using hB6
    rw [Real.rpow_sub hdelta] at hbound
    have hfrac : delta /
        (delta ^ highBaseRate d epsilon *
          (C * c0 ^ boundaryDimension d)) ≤ 1 := by
      calc
        delta / (delta ^ highBaseRate d epsilon *
              (C * c0 ^ boundaryDimension d)) =
            (C * c0 ^ boundaryDimension d)⁻¹ *
              (delta / delta ^ highBaseRate d epsilon) := by
              field_simp
        _ ≤ 1 := by simpa only [Real.rpow_one] using hbound
    have := (div_le_one
      (mul_pos (Real.rpow_pos_of_pos hdelta _) hcoefPos)).mp hfrac
    simpa [mul_comm] using this
  have hLowUpper : etaLowEnvelope d C (graphWidth epsilon c0 delta)
      (realGridScale d delta) (branchLogScale delta) ≤
        delta ^ tau epsilon := by
    have := mul_le_mul_of_nonneg_right hL
      (Real.rpow_nonneg hdelta.le (lowUpperSaving d epsilon))
    have hcost : etaUpperCoefficient d C c0 * branchLogScale delta *
        delta ^ lowUpperSaving d epsilon ≤ 1 := by
      have hcoefNonneg : 0 ≤ etaUpperCoefficient d C c0 := by
        simp only [etaUpperCoefficient]
        positivity
      have hstep₁ := mul_le_mul_of_nonneg_left hL hcoefNonneg
      have hstep₂ := mul_le_mul_of_nonneg_right hstep₁
        (Real.rpow_nonneg hdelta.le (lowUpperSaving d epsilon))
      calc
        etaUpperCoefficient d C c0 * branchLogScale delta *
              delta ^ lowUpperSaving d epsilon ≤
            etaUpperCoefficient d C c0 *
              (D * Real.log (1 / delta)) *
                delta ^ lowUpperSaving d epsilon := hstep₂
        _ = (etaUpperCoefficient d C c0 * D) *
            Real.log (1 / delta) * delta ^ lowUpperSaving d epsilon := by ring
        _ ≤ 1 := by simpa [A3] using hB3
    have hEnvelope : etaLowEnvelope d C (graphWidth epsilon c0 delta)
        (realGridScale d delta) (branchLogScale delta) =
        etaUpperCoefficient d C c0 * branchLogScale delta *
          delta ^ (lowBaseRate d epsilon - gridRate d * alpha d) := by
      rw [etaLowEnvelope, graphWidth_rpow hc0 hdelta,
        realGridScale_rpow d hdelta, realGridScale_rpow d hdelta]
      rw [Real.rpow_neg hdelta.le, Real.rpow_neg hdelta.le,
        div_inv_eq_mul]
      calc
        C * (delta ^ (gridRate d * alpha d))⁻¹ * branchLogScale delta *
              (c0 ^ boundaryDimension d *
                delta ^ (tau epsilon * boundaryDimension d)) *
            delta ^ (gridRate d * ((d : ℝ) + 1)) =
          (C * c0 ^ boundaryDimension d) * branchLogScale delta *
            ((delta ^ (tau epsilon * boundaryDimension d) /
                delta ^ (gridRate d * alpha d)) *
              delta ^ (gridRate d * ((d : ℝ) + 1))) := by
                rw [div_eq_mul_inv]
                ring
        _ = (C * c0 ^ boundaryDimension d) * branchLogScale delta *
            delta ^ ((tau epsilon * boundaryDimension d -
              gridRate d * alpha d) + gridRate d * ((d : ℝ) + 1)) := by
                rw [← Real.rpow_sub hdelta, ← Real.rpow_add hdelta]
        _ = _ := by
          simp only [etaUpperCoefficient, lowBaseRate]
          congr 1
          ring_nf
    rw [hEnvelope]
    rw [show lowBaseRate d epsilon - gridRate d * alpha d =
      lowUpperSaving d epsilon + tau epsilon by
        simp only [lowUpperSaving]
        ring, Real.rpow_add hdelta]
    calc
      etaUpperCoefficient d C c0 * branchLogScale delta *
            (delta ^ lowUpperSaving d epsilon * delta ^ tau epsilon) =
          (etaUpperCoefficient d C c0 * branchLogScale delta *
            delta ^ lowUpperSaving d epsilon) * delta ^ tau epsilon := by ring
      _ ≤ 1 * delta ^ tau epsilon :=
        mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hdelta.le _)
      _ = delta ^ tau epsilon := one_mul _
  have hHighUpper : etaHigh d C (graphWidth epsilon c0 delta)
      (realGridScale d delta) ≤ delta ^ tau epsilon := by
    rw [hHighBase]
    have hcost : etaUpperCoefficient d C c0 *
        delta ^ highUpperSaving d epsilon ≤ 1 := by
      simpa [A4] using hB4
    rw [show highBaseRate d epsilon =
      highUpperSaving d epsilon + tau epsilon by
        simp only [highUpperSaving]
        ring, Real.rpow_add hdelta]
    calc
      C * c0 ^ boundaryDimension d *
            (delta ^ highUpperSaving d epsilon * delta ^ tau epsilon) =
          (etaUpperCoefficient d C c0 *
            delta ^ highUpperSaving d epsilon) * delta ^ tau epsilon := by
              simp only [etaUpperCoefficient]
              ring
      _ ≤ 1 * delta ^ tau epsilon :=
        mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hdelta.le _)
      _ = delta ^ tau epsilon := one_mul _
  constructor
  · intro hKsmall
    apply low_branch_closure hd hepsilon hepsilonLe hdelta hdeltaOne hc hC hcK
      hu hK hm hLpos hcKL hKsmall hLowLower hLowUpper
    have hLsq : branchLogScale delta ^ (2 : ℕ) ≤
        D ^ (2 : ℕ) * (Real.log (1 / delta)) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (D * Real.log (1 / delta) - branchLogScale delta)]
    rw [hLowBase, realGridScale, Real.rpow_neg hdelta.le]
    let coeff : ℝ := C * cK * c0 ^ boundaryDimension d
    let t : ℝ := alpha d + epsilon - 1
    let g : ℝ := 2 * gridRate d
    have hcoeffPos : 0 < coeff := by
      dsimp only [coeff]
      positivity
    have hEtaPow :
        (coeff * delta ^ lowBaseRate d epsilon) ^ t =
          coeff ^ t * delta ^ (lowBaseRate d epsilon * t) := by
      rw [Real.mul_rpow hcoeffPos.le (Real.rpow_nonneg hdelta.le _),
        ← Real.rpow_mul hdelta.le]
    have hB1' :
        (C / c) * coeff ^ t * D ^ (2 : ℕ) *
            Real.log (1 / delta) ^ (2 : ℕ) *
            delta ^ (g + lowBaseRate d epsilon * t) ≤ 1 := by
      simpa only [A1, lowDensityCoefficient, lowDensitySaving,
        coeff, t, g] using hB1
    rw [hEtaPow]
    have hCLsq := mul_le_mul_of_nonneg_left hLsq hC.le
    have hstep := mul_le_mul_of_nonneg_right hCLsq
      (mul_nonneg (Real.rpow_nonneg hcoeffPos.le t)
        (Real.rpow_nonneg hdelta.le (lowBaseRate d epsilon * t)))
    calc
      C * branchLogScale delta ^ 2 *
            (coeff ^ t * delta ^ (lowBaseRate d epsilon * t)) ≤
          C * (D ^ 2 * Real.log (1 / delta) ^ 2) *
            (coeff ^ t * delta ^ (lowBaseRate d epsilon * t)) := hstep
      _ = (c * (delta ^ g)⁻¹) *
          ((C / c) * coeff ^ t * D ^ 2 * Real.log (1 / delta) ^ 2 *
            delta ^ (g + lowBaseRate d epsilon * t)) := by
              rw [Real.rpow_add hdelta]
              field_simp
      _ ≤ (c * (delta ^ g)⁻¹) * 1 :=
        mul_le_mul_of_nonneg_left hB1' (by positivity)
      _ = c * (delta ^ g)⁻¹ := mul_one _
      _ = c * (delta ^ gridRate d)⁻¹ ^ 2 := by
        rw [show g = gridRate d * (2 : ℕ) by
          dsimp only [g]
          ring, Real.rpow_mul_natCast hdelta.le, inv_pow]
  · intro hKlarge
    apply high_branch_closure hd hepsilon hepsilonLe hc hC hu hK hm hLpos
      hKlarge hHighLower hHighUpper
    have hetaHighNonneg : 0 ≤ etaHigh d C (graphWidth epsilon c0 delta)
        (realGridScale d delta) := by
      rw [hHighBase]
      positivity
    have hCL := mul_le_mul_of_nonneg_left hL hC.le
    have hCLE := mul_le_mul_of_nonneg_right hCL
      (Real.rpow_nonneg hetaHighNonneg (alpha d + epsilon - 1))
    calc
      C * branchLogScale delta *
          etaHigh d C (graphWidth epsilon c0 delta)
              (realGridScale d delta) ^ (alpha d + epsilon - 1)
          ≤ C * (D * Real.log (1 / delta)) *
              etaHigh d C (graphWidth epsilon c0 delta)
                (realGridScale d delta) ^ (alpha d + epsilon - 1) := by
                simpa only [mul_assoc] using hCLE
      _ ≤ c * realGridScale d delta ^ (alpha d + 1) := by
        rw [hHighBase, realGridScale_rpow d hdelta]
        let coeff : ℝ := C * c0 ^ boundaryDimension d
        let t : ℝ := alpha d + epsilon - 1
        let g : ℝ := gridRate d * (alpha d + 1)
        have hcoeffPos : 0 < coeff := by
          dsimp only [coeff]
          positivity
        have hdeltaG : 0 < delta ^ g := Real.rpow_pos_of_pos hdelta _
        have hEtaPow :
            (coeff * delta ^ highBaseRate d epsilon) ^ t =
              coeff ^ t * delta ^ (highBaseRate d epsilon * t) := by
          rw [Real.mul_rpow hcoeffPos.le
            (Real.rpow_nonneg hdelta.le _), ← Real.rpow_mul hdelta.le]
        have hB2' :
            (C / c) * coeff ^ t * D * Real.log (1 / delta) *
                delta ^ (g + highBaseRate d epsilon * t) ≤ 1 := by
          simpa only [A2, highDensityCoefficient, highDensitySaving,
            coeff, t, g] using hB2
        rw [hEtaPow, Real.rpow_neg hdelta.le]
        calc
          C * (D * Real.log (1 / delta)) *
                (coeff ^ t * delta ^ (highBaseRate d epsilon * t)) =
              (c * (delta ^ g)⁻¹) *
                ((C / c) * coeff ^ t * D * Real.log (1 / delta) *
                  delta ^ (g + highBaseRate d epsilon * t)) := by
                    rw [Real.rpow_add hdelta]
                    field_simp
          _ ≤ (c * (delta ^ g)⁻¹) * 1 := by
            exact mul_le_mul_of_nonneg_left hB2' (by positivity)
          _ = c * (delta ^ g)⁻¹ := mul_one _

end
end Erdos186.PZ.ConvexDensity
