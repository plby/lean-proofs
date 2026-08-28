import Wikipedia.HopfProblem.RiemannSphereMobiusCircleAlgebra
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The explicit inverse of the unit-circle cross-ratio

The two rational formulas are inverse off their respective poles.  Their
analyticity is proved in the ordinary complex coordinates, and the inverse
has no pole on the closed half-plane selected by the unit-circle triple.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.RiemannSphere.MobiusCircle

/-- The affine inverse formula. Its pole is the image of infinity under
the sphere cross-ratio. -/
def inverseCrossRatio (a b c w : ℂ) : ℂ :=
  (c * w - coefficient a b c * a) / (w - coefficient a b c)

theorem crossRatio_mul_sub {a b c z : ℂ} (hzc : z ≠ c) :
    crossRatio a b c z * (z - c) = coefficient a b c * (z - a) := by
  rw [crossRatio_eq_coefficient, mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr hzc)]

theorem inverseCrossRatio_mul_sub {a b c w : ℂ} (hw : w ≠ coefficient a b c) :
    inverseCrossRatio a b c w * (w - coefficient a b c) =
      c * w - coefficient a b c * a := by
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr hw)

theorem crossRatio_ne_coefficient {a b c z : ℂ}
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hzc : z ≠ c) :
    crossRatio a b c z ≠ coefficient a b c := by
  intro h
  have he := crossRatio_mul_sub (a := a) (b := b) hzc
  rw [h] at he
  have hs := mul_left_cancel₀ (coefficient_ne_zero hba hbc) he
  exact hac (by simpa only [sub_right_inj] using hs.symm)

theorem inverseCrossRatio_ne_pole {a b c w : ℂ}
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hw : w ≠ coefficient a b c) :
    inverseCrossRatio a b c w ≠ c := by
  intro h
  have he := inverseCrossRatio_mul_sub hw
  rw [h] at he
  have hz : coefficient a b c * (a - c) = 0 := by
    calc
      coefficient a b c * (a - c) =
          c * (w - coefficient a b c) - (c * w - coefficient a b c * a) := by ring
      _ = 0 := sub_eq_zero.mpr he
  exact hac (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (coefficient_ne_zero hba hbc)))

/-- First exact inverse identity, on the complement of the cross-ratio pole. -/
theorem inverseCrossRatio_crossRatio {a b c z : ℂ}
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hzc : z ≠ c) :
    inverseCrossRatio a b c (crossRatio a b c z) = z := by
  have hp := sub_ne_zero.mpr (crossRatio_ne_coefficient hba hbc hac hzc)
  apply (div_eq_iff hp).mpr
  calc
    c * crossRatio a b c z - coefficient a b c * a =
        z * (crossRatio a b c z - coefficient a b c) +
          (coefficient a b c * (z - a) - crossRatio a b c z * (z - c)) := by ring
    _ = _ := by rw [crossRatio_mul_sub hzc]; ring

/-- Second exact inverse identity, on the complement of the inverse pole. -/
theorem crossRatio_inverseCrossRatio {a b c w : ℂ}
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hw : w ≠ coefficient a b c) :
    crossRatio a b c (inverseCrossRatio a b c w) = w := by
  rw [crossRatio_eq_coefficient, ← mul_div_assoc]
  apply (div_eq_iff (sub_ne_zero.mpr (inverseCrossRatio_ne_pole hba hbc hac hw))).mpr
  calc
    coefficient a b c * (inverseCrossRatio a b c w - a) =
        w * (inverseCrossRatio a b c w - c) +
          ((c * w - coefficient a b c * a) -
            inverseCrossRatio a b c w * (w - coefficient a b c)) := by ring
    _ = _ := by rw [inverseCrossRatio_mul_sub hw]; ring

theorem crossRatio_analyticAt {a b c z : ℂ} (hba : b ≠ a) (hzc : z ≠ c) :
    AnalyticAt ℂ (crossRatio a b c) z := by
  exact ((analyticAt_id.sub analyticAt_const).mul analyticAt_const).div
    ((analyticAt_id.sub analyticAt_const).mul analyticAt_const)
    (mul_ne_zero (sub_ne_zero.mpr hzc) (sub_ne_zero.mpr hba))

theorem inverseCrossRatio_analyticAt {a b c w : ℂ} (hw : w ≠ coefficient a b c) :
    AnalyticAt ℂ (inverseCrossRatio a b c) w := by
  exact ((analyticAt_const.mul analyticAt_id).sub analyticAt_const).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hw)

theorem crossRatio_contDiffAt {a b c z : ℂ} (hba : b ≠ a) (hzc : z ≠ c) :
    ContDiffAt ℂ ω (crossRatio a b c) z :=
  (crossRatio_analyticAt hba hzc).contDiffAt

theorem inverseCrossRatio_contDiffAt {a b c w : ℂ} (hw : w ≠ coefficient a b c) :
    ContDiffAt ℂ ω (inverseCrossRatio a b c) w :=
  (inverseCrossRatio_analyticAt hw).contDiffAt

theorem crossRatio_analyticOnNhd_compl_pole {a b c : ℂ} (hba : b ≠ a) :
    AnalyticOnNhd ℂ (crossRatio a b c) {c}ᶜ := by
  intro z hz
  exact crossRatio_analyticAt hba hz

theorem inverseCrossRatio_analyticOnNhd_compl_pole (a b c : ℂ) :
    AnalyticOnNhd ℂ (inverseCrossRatio a b c) {coefficient a b c}ᶜ := by
  intro w hw
  exact inverseCrossRatio_analyticAt hw

/-- The inverse pole lies in the opposite open half-plane, so even
the boundary of the desired half-plane avoids it. -/
theorem ne_coefficient_of_orientation_nonneg {a b c w : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    (hw : 0 ≤ orientation a b c * w.im) : w ≠ coefficient a b c := by
  intro he
  rw [he] at hw
  exact (not_le_of_gt (orientation_mul_coefficient_im_neg ha hb hc hba hbc hac)) hw

theorem inverseCrossRatio_analyticOnNhd_closedHalfPlane {a b c : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) :
    AnalyticOnNhd ℂ (inverseCrossRatio a b c)
      {w : ℂ | 0 ≤ orientation a b c * w.im} := by
  intro w hw
  exact inverseCrossRatio_analyticAt
    (ne_coefficient_of_orientation_nonneg ha hb hc hba hbc hac hw)

theorem inverseCrossRatio_contDiffOn_closedHalfPlane {a b c : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) :
    ContDiffOn ℂ ω (inverseCrossRatio a b c)
      {w : ℂ | 0 ≤ orientation a b c * w.im} := by
  intro w hw
  exact (inverseCrossRatio_analyticOnNhd_closedHalfPlane ha hb hc hba hbc hac w hw).contDiffAt
    |>.contDiffWithinAt

theorem inverseCrossRatio_norm_lt_one_iff {a b c w : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hw : w ≠ coefficient a b c) :
    ‖inverseCrossRatio a b c w‖ < 1 ↔ 0 < orientation a b c * w.im := by
  have h := orientation_mul_crossRatio_im_pos_iff ha hb hc hba hbc hac
    (inverseCrossRatio_ne_pole hba hbc hac hw)
  rw [crossRatio_inverseCrossRatio hba hbc hac hw] at h
  exact h.symm

theorem inverseCrossRatio_norm_eq_one_iff {a b c w : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hw : w ≠ coefficient a b c) :
    ‖inverseCrossRatio a b c w‖ = 1 ↔ w.im = 0 := by
  have h := crossRatio_im_eq_zero_iff ha hb hc hba hbc hac
    (inverseCrossRatio_ne_pole hba hbc hac hw)
  rw [crossRatio_inverseCrossRatio hba hbc hac hw] at h
  exact h.symm

theorem inverseCrossRatio_norm_le_one_iff {a b c w : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) (hw : w ≠ coefficient a b c) :
    ‖inverseCrossRatio a b c w‖ ≤ 1 ↔ 0 ≤ orientation a b c * w.im := by
  have h := orientation_mul_crossRatio_im_neg_iff ha hb hc hba hbc hac
    (inverseCrossRatio_ne_pole hba hbc hac hw)
  rw [crossRatio_inverseCrossRatio hba hbc hac hw] at h
  simpa only [not_lt] using (not_congr h).symm

theorem inverseCrossRatio_norm_le_one_of_orientation_nonneg {a b c w : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    (hw : 0 ≤ orientation a b c * w.im) : ‖inverseCrossRatio a b c w‖ ≤ 1 :=
  (inverseCrossRatio_norm_le_one_iff ha hb hc hba hbc hac
    (ne_coefficient_of_orientation_nonneg ha hb hc hba hbc hac hw)).mpr hw

theorem inverseCrossRatio_zero {a b c : ℂ}
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) : inverseCrossRatio a b c 0 = a := by
  simpa only [crossRatio_at_zero] using inverseCrossRatio_crossRatio hba hbc hac hac

theorem inverseCrossRatio_one {a b c : ℂ}
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) : inverseCrossRatio a b c 1 = b := by
  simpa only [crossRatio_at_one hba hbc] using inverseCrossRatio_crossRatio hba hbc hac hbc

end Wikipedia.HopfProblem.RiemannSphere.MobiusCircle
