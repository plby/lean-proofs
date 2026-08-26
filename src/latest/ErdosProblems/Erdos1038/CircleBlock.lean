import ErdosProblems.Erdos1038.CircleFourier
import ErdosProblems.Erdos1038.BlockReductionArithmetic

/-!
# Algebraic conclusion of the circle block estimate

The rearrangement step supplies a normalized mixed-energy lower bound.  This
file performs the exact mass substitutions and isolates the scalar margin
whose positivity is checked by the uniform calibration certificate.
-/

namespace Erdos1038

noncomputable section

def circleBlockMargin (H aPi bPi Ceff Q R : ℝ) : ℝ :=
  Real.log (2 * H / (aPi * bPi)) +
    circleCorrection Q + circleCorrection R + circleSincSquareGap Q R -
      Real.pi * Ceff / (aPi * Q)

theorem circleBlockMargin_le_normalizedEnergyGap
    {H aPi bPi Ceff Q R q r E : ℝ}
    (hH : 0 < H) (haPi : 0 < aPi) (hbPi : 0 < bPi)
    (hQ : 0 < Q) (hR : 0 < R)
    (hq : q = aPi * Q / Real.pi)
    (hr : r = bPi * R / Real.pi)
    (henergy :
      Real.log H + circleSelfEnergy Q + circleSelfEnergy R +
          circleSincSquareGap Q R ≤ E / (q * r)) :
    circleBlockMargin H aPi bPi Ceff Q R ≤
      E / (q * r) - Real.log (q * r / 2) - Ceff / q := by
  have hqpos : 0 < q := by rw [hq]; positivity
  have hrpos : 0 < r := by rw [hr]; positivity
  have hlogmass :
      Real.log (q * r / 2) =
        Real.log aPi + Real.log Q - Real.log Real.pi +
          (Real.log bPi + Real.log R - Real.log Real.pi) - Real.log 2 := by
    rw [Real.log_div (mul_ne_zero hqpos.ne' hrpos.ne') (by norm_num),
      Real.log_mul hqpos.ne' hrpos.ne', hq, hr,
      Real.log_div (mul_ne_zero haPi.ne' hQ.ne') Real.pi_ne_zero,
      Real.log_div (mul_ne_zero hbPi.ne' hR.ne') Real.pi_ne_zero,
      Real.log_mul haPi.ne' hQ.ne', Real.log_mul hbPi.ne' hR.ne']
  have hlogprefactor :
      Real.log (2 * H / (aPi * bPi)) =
        Real.log 2 + Real.log H - (Real.log aPi + Real.log bPi) := by
    rw [Real.log_div (mul_ne_zero (by norm_num) hH.ne')
      (mul_ne_zero haPi.ne' hbPi.ne'),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hH.ne',
      Real.log_mul haPi.ne' hbPi.ne']
  have hC : Ceff / q = Real.pi * Ceff / (aPi * Q) := by
    rw [hq]
    field_simp [haPi.ne', hQ.ne', Real.pi_ne_zero]
  have hidentity :
      circleBlockMargin H aPi bPi Ceff Q R =
        Real.log H + circleSelfEnergy Q + circleSelfEnergy R +
          circleSincSquareGap Q R - Real.log (q * r / 2) - Ceff / q := by
    unfold circleBlockMargin
    rw [circleSelfEnergy_eq_log_div_add_circleCorrection hQ,
      circleSelfEnergy_eq_log_div_add_circleCorrection hR,
      Real.log_div hQ.ne' Real.pi_ne_zero,
      Real.log_div hR.ne' Real.pi_ne_zero,
      hlogmass, hlogprefactor, hC]
    ring
  rw [hidentity]
  linarith

theorem circleBlock_energy_bound_of_margin_nonneg
    {H aPi bPi Ceff Q R q r E : ℝ}
    (hH : 0 < H) (haPi : 0 < aPi) (hbPi : 0 < bPi)
    (hQ : 0 < Q) (hR : 0 < R)
    (hq : q = aPi * Q / Real.pi)
    (hr : r = bPi * R / Real.pi)
    (henergy :
      Real.log H + circleSelfEnergy Q + circleSelfEnergy R +
          circleSincSquareGap Q R ≤ E / (q * r))
    (hmargin : 0 ≤ circleBlockMargin H aPi bPi Ceff Q R) :
    q * r * Real.log (q * r / 2) + Ceff * r ≤ E := by
  have hqpos : 0 < q := by rw [hq]; positivity
  have hrpos : 0 < r := by rw [hr]; positivity
  have hgap := hmargin.trans
    (circleBlockMargin_le_normalizedEnergyGap hH haPi hbPi hQ hR
      hq hr henergy)
  have hnormalized : Real.log (q * r / 2) + Ceff / q ≤
      E / (q * r) := by
    linarith
  rw [le_div_iff₀ (mul_pos hqpos hrpos)] at hnormalized
  have hid :
      (Real.log (q * r / 2) + Ceff / q) * (q * r) =
        q * r * Real.log (q * r / 2) + Ceff * r := by
    field_simp [hqpos.ne']
  rwa [hid] at hnormalized

theorem circleBlock_strict_energy_bound_of_margin_pos
    {H aPi bPi Ceff Q R q r E : ℝ}
    (hH : 0 < H) (haPi : 0 < aPi) (hbPi : 0 < bPi)
    (hQ : 0 < Q) (hR : 0 < R)
    (hq : q = aPi * Q / Real.pi)
    (hr : r = bPi * R / Real.pi)
    (henergy :
      Real.log H + circleSelfEnergy Q + circleSelfEnergy R +
          circleSincSquareGap Q R ≤ E / (q * r))
    (hmargin : 0 < circleBlockMargin H aPi bPi Ceff Q R) :
    q * r * Real.log (q * r / 2) + Ceff * r < E := by
  have hqpos : 0 < q := by rw [hq]; positivity
  have hrpos : 0 < r := by rw [hr]; positivity
  have hgap := hmargin.trans_le
    (circleBlockMargin_le_normalizedEnergyGap hH haPi hbPi hQ hR
      hq hr henergy)
  have hnormalized : Real.log (q * r / 2) + Ceff / q <
      E / (q * r) := by
    linarith
  rw [lt_div_iff₀ (mul_pos hqpos hrpos)] at hnormalized
  have hid :
      (Real.log (q * r / 2) + Ceff / q) * (q * r) =
        q * r * Real.log (q * r / 2) + Ceff * r := by
    field_simp [hqpos.ne']
  rwa [hid] at hnormalized

end

end Erdos1038
