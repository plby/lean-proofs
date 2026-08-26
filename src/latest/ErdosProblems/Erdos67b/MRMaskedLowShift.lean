import ErdosProblems.Erdos67b.MRTypicalLowHigh
import ErdosProblems.Erdos67b.MRGSA9SourceRadiusWide

/-!
# A horizontal low-factor shift without a square-root loss

The local Euler comparison retains the full masked L-series norm.  Its
constant is uniform over masks, so the summable deleted-prime cost can be
preserved when the high factor stays on the Halasz line.
-/

open scoped BigOperators Classical LSeries.notation
open Finset

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrLow_primeBandCoefficient_eq (f : ℕ → ℂ)
    (P : ℕ → Prop) [DecidablePred P] (y : ℕ) :
    gsA9Low (primeBandCoefficient f P) y =
      primeBandCoefficient f (fun p ↦ P p ∧ p ≤ y) := by
  exact primeBandCoefficient_nested f P (fun p ↦ p ≤ y)

theorem mrLSeries_low_primeBand_eq_finiteEulerProduct
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA9Low (primeBandCoefficient f P) y) s =
      ∏ p ∈ primesUpTo y with P p, gsA9LocalEulerFactor f s p := by
  rw [mrLow_primeBandCoefficient_eq,
    LSeries_primeBandCoefficient_eq_finiteEulerProduct_of_pos_re
      hmul hbound _ y (fun _ hp ↦ hp.2) hs]
  congr 1
  ext p
  simp only [mem_filter, mem_primesUpTo]
  tauto

/-- The low series at the left line costs one uniform radial-displacement
factor relative to the same low series at the right line. -/
theorem mrNorm_low_primeBand_shift_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] {y : ℕ} (hy : 2 ≤ y)
    (hlarge : ∀ p ∈ primesUpTo y, P p → 23 ≤ p)
    {sigmaLow sigmaHigh t : ℝ} (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    ‖LSeries (gsA9Low (primeBandCoefficient f P) y)
        ((sigmaLow : ℂ) + Complex.I * (t : ℂ))‖ ≤
      ‖LSeries (gsA9Low (primeBandCoefficient f P) y)
        ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖ *
      Real.exp (6 * gsA9WideSourceShiftConstant) := by
  let S := (primesUpTo y).filter P
  have hS : S ⊆ primesUpTo y := filter_subset _ _
  have hprime : ∀ p ∈ S, p.Prime := fun p hp ↦ (mem_primesUpTo.mp (hS hp)).1
  have hlow : 0 < ((sigmaLow : ℂ) + Complex.I * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith
  have hhigh : 0 < ((sigmaHigh : ℂ) + Complex.I * (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith
  rw [mrLSeries_low_primeBand_eq_finiteEulerProduct hmul hbound P y hlow,
    mrLSeries_low_primeBand_eq_finiteEulerProduct hmul hbound P y hhigh]
  have hshift := norm_prod_gsA9LocalEulerFactor_shift_le_exp_sum_norm_sub
    hmul hbound S hprime
    (sLow := (sigmaLow : ℂ) + Complex.I * (t : ℂ))
    (sHigh := (sigmaHigh : ℂ) + Complex.I * (t : ℂ))
    (fun p ↦ (p : ℝ) ^ (sigmaHigh - sigmaLow))
    (fun p hp ↦ Real.one_le_rpow (by exact_mod_cast (hprime p hp).one_le) (sub_nonneg.mpr hle))
    (fun p hp ↦ nat_cpow_neg_low_eq_rpow_gap_mul_neg_high (hprime p hp) hle)
    (fun p hp ↦ norm_prime_cpow_le_one_third_of_twenty_three_le
      (hprime p hp) (hlarge p (hS hp) (mem_filter.mp hp).2) hhalf)
  have hsum := sum_prime_radial_norm_sub_subset_wideSourceGap_le_constant
    hy S hS hle hsigma hgap (t := t)
  exact hshift.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))) (norm_nonneg _))

/-- Joining the shifted low factor to its common high factor retains the
full masked L-series, rather than its square root. -/
theorem mrNorm_maskedLow_mul_high_shift_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] {y : ℕ} (hy : 2 ≤ y)
    (hsmall : ∀ p, ¬ P p → p ≤ y)
    (hlarge : ∀ p ∈ primesUpTo y, P p → 23 ≤ p)
    {sigmaLow sigmaHigh t : ℝ} (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ))
    (hhigh : 1 < sigmaHigh) :
    ‖LSeries (gsA9Low (primeBandCoefficient f P) y)
          ((sigmaLow : ℂ) + Complex.I * (t : ℂ)) *
        LSeries (gsA9High f y) ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖ ≤
      Real.exp (6 * gsA9WideSourceShiftConstant) *
        ‖LSeries (primeBandCoefficient f P)
          ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖ := by
  have hshift := mrNorm_low_primeBand_shift_le hmul hbound P hy hlarge hhalf hle hsigma hgap (t := t)
  have hid := LSeries_gsA9Low_mul_gsA9High
    (primeBandCoefficient_isMultiplicativeOnPositiveNat hmul P)
    (fun n hn ↦ norm_primeBandCoefficient_le_one hbound P hn) y
    (s := ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))) (by simpa using hhigh)
  rw [mrHigh_primeBandCoefficient_eq f P y hsmall] at hid
  calc
    _ = ‖LSeries (gsA9Low (primeBandCoefficient f P) y)
        ((sigmaLow : ℂ) + Complex.I * (t : ℂ))‖ *
        ‖LSeries (gsA9High f y) ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖ := norm_mul _ _
    _ ≤ (‖LSeries (gsA9Low (primeBandCoefficient f P) y)
        ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖ *
        Real.exp (6 * gsA9WideSourceShiftConstant)) *
        ‖LSeries (gsA9High f y) ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖ :=
      mul_le_mul_of_nonneg_right hshift (norm_nonneg _)
    _ = _ := by rw [mul_right_comm, ← norm_mul, hid, mul_comm]

end

end Erdos67b
