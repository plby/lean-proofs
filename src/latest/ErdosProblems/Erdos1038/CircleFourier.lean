import ErdosProblems.Erdos1038.CircleCorrection
import Mathlib.Analysis.PSeries

/-!
# Fourier series for the centered-circle comparison

This file packages the absolutely convergent series that occurs after
rearranging two circle densities to centered arcs.  Frequencies are indexed
by `n : ℕ` and represent the positive integer `n + 1`.
-/

namespace Erdos1038

noncomputable section

def circleSincTerm (Q R : ℝ) (n : ℕ) : ℝ :=
  Real.sinc (((n + 1 : ℕ) : ℝ) * Q) *
      Real.sinc (((n + 1 : ℕ) : ℝ) * R) /
    ((n + 1 : ℕ) : ℝ)

def circleArcEnergy (Q R : ℝ) : ℝ :=
  -∑' n : ℕ, circleSincTerm Q R n

def circleSincSquareGapTerm (Q R : ℝ) (n : ℕ) : ℝ :=
  (Real.sinc (((n + 1 : ℕ) : ℝ) * Q) -
      Real.sinc (((n + 1 : ℕ) : ℝ) * R)) ^ 2 /
    ((n + 1 : ℕ) : ℝ)

def circleSincSquareGap (Q R : ℝ) : ℝ :=
  ∑' n : ℕ, circleSincSquareGapTerm Q R n

lemma abs_sinc_le_inv_of_pos {x : ℝ} (hx : 0 < x) :
    |Real.sinc x| ≤ x⁻¹ := by
  rw [Real.sinc_of_ne_zero hx.ne', abs_div, abs_of_pos hx]
  simpa only [one_div] using!
    (div_le_div_iff_of_pos_right hx).2 (Real.abs_sin_le_one x)

lemma summable_one_div_positiveFrequency_cube :
    Summable (fun n : ℕ ↦
      1 / (((n + 1 : ℕ) : ℝ) ^ 3)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using!
    (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))

lemma summable_circleSincTerm {Q R : ℝ} (hQ : 0 < Q) (hR : 0 < R) :
    Summable (circleSincTerm Q R) := by
  have hmajor : Summable (fun n : ℕ ↦
      (1 / (Q * R)) * (1 / (((n + 1 : ℕ) : ℝ) ^ 3))) :=
    summable_one_div_positiveFrequency_cube.mul_left (1 / (Q * R))
  refine Summable.of_norm_bounded hmajor ?_
  intro n
  have hm : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hmQ : 0 < ((n + 1 : ℕ) : ℝ) * Q := mul_pos hm hQ
  have hmR : 0 < ((n + 1 : ℕ) : ℝ) * R := mul_pos hm hR
  have hQbound := abs_sinc_le_inv_of_pos hmQ
  have hRbound := abs_sinc_le_inv_of_pos hmR
  rw [Real.norm_eq_abs]
  unfold circleSincTerm
  rw [abs_div, abs_mul, abs_of_pos hm]
  calc
    |Real.sinc (((n + 1 : ℕ) : ℝ) * Q)| *
          |Real.sinc (((n + 1 : ℕ) : ℝ) * R)| /
        ((n + 1 : ℕ) : ℝ) ≤
        ((((n + 1 : ℕ) : ℝ) * Q)⁻¹ *
          (((n + 1 : ℕ) : ℝ) * R)⁻¹) /
          ((n + 1 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hm.le
      exact mul_le_mul hQbound hRbound (abs_nonneg _)
        (inv_nonneg.mpr hmQ.le)
    _ = (1 / (Q * R)) *
        (1 / (((n + 1 : ℕ) : ℝ) ^ 3)) := by
      field_simp [hm.ne', hQ.ne', hR.ne']

lemma circleSincSquareGapTerm_eq (Q R : ℝ) (n : ℕ) :
    circleSincSquareGapTerm Q R n =
      circleSincTerm Q Q n + circleSincTerm R R n -
        2 * circleSincTerm Q R n := by
  unfold circleSincSquareGapTerm circleSincTerm
  ring

lemma summable_circleSincSquareGapTerm {Q R : ℝ}
    (hQ : 0 < Q) (hR : 0 < R) :
    Summable (circleSincSquareGapTerm Q R) := by
  have hQQ := summable_circleSincTerm hQ hQ
  have hRR := summable_circleSincTerm hR hR
  have hQR := summable_circleSincTerm hQ hR
  exact ((hQQ.add hRR).sub (hQR.mul_left 2)).congr fun n ↦
    (circleSincSquareGapTerm_eq Q R n).symm

theorem circleArcEnergy_square_completion {Q R : ℝ}
    (hQ : 0 < Q) (hR : 0 < R) :
    2 * circleArcEnergy Q R - circleArcEnergy Q Q -
        circleArcEnergy R R = circleSincSquareGap Q R := by
  have hQQ := summable_circleSincTerm hQ hQ
  have hRR := summable_circleSincTerm hR hR
  have hQR := summable_circleSincTerm hQ hR
  rw [circleSincSquareGap]
  calc
    2 * circleArcEnergy Q R - circleArcEnergy Q Q -
        circleArcEnergy R R =
        (∑' n, circleSincTerm Q Q n) +
          (∑' n, circleSincTerm R R n) -
            2 * (∑' n, circleSincTerm Q R n) := by
      simp only [circleArcEnergy]
      ring
    _ = ∑' n : ℕ, (circleSincTerm Q Q n + circleSincTerm R R n -
          2 * circleSincTerm Q R n) := by
      rw [(hQQ.add hRR).tsum_sub (hQR.mul_left 2),
        hQQ.tsum_add hRR, tsum_mul_left]
    _ = ∑' n, circleSincSquareGapTerm Q R n := by
      apply tsum_congr
      intro n
      rw [circleSincSquareGapTerm_eq]

theorem circleSincSquareGap_nonneg (Q R : ℝ) :
    0 ≤ circleSincSquareGap Q R := by
  unfold circleSincSquareGap circleSincSquareGapTerm
  exact tsum_nonneg fun n ↦ div_nonneg (sq_nonneg _) (by positivity)

theorem two_mul_circleArcEnergy_ge_self_sum {Q R : ℝ}
    (hQ : 0 < Q) (hR : 0 < R) :
    circleArcEnergy Q Q + circleArcEnergy R R ≤
      2 * circleArcEnergy Q R := by
  have hsquare := circleArcEnergy_square_completion hQ hR
  have hnonneg := circleSincSquareGap_nonneg Q R
  linarith

end

end Erdos1038
