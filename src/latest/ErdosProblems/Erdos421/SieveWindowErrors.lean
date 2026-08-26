import ErdosProblems.Erdos421.SmoothSieveWindows
import ErdosProblems.Erdos421.RoughEulerHarmonic

/-! # The actual rough-number window between the two sieve remainders -/

namespace Erdos421

noncomputable def sieveWindowError (M : ℕ) (a : ℕ → ℝ) (Y x : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, (a m : ℂ) *
    (additiveDivisorWindow oneSidedSchwartzWindow Y x m - (m : ℂ)⁻¹)

theorem sieveWindowError_re (M : ℕ) (a : ℕ → ℝ) (Y x : ℝ) :
    (sieveWindowError M a Y x).re =
      (∑ m ∈ Finset.Icc 1 M, a m * (additiveDivisorWindow oneSidedSchwartzWindow Y x m).re) -
        ∑ m ∈ Finset.Icc 1 M, a m / (m : ℝ) := by
  rw [sieveWindowError, Complex.re_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    zero_mul, sub_zero, div_eq_mul_inv]
  ring

theorem canonicalUpperMain_truncated (D z : ℕ) :
    canonicalUpperMain D z =
      ∑ m ∈ Finset.Icc 1 (D ^ 2), canonicalUpperSieve D z m / (m : ℝ) := by
  simpa only [canonicalUpperMain, div_eq_mul_inv] using
    canonicalUpper_sum_truncate D z (fun m ↦ (m : ℝ)⁻¹)

theorem additiveRoughWindow_le_main_error {D : ℕ} (hD : 1 ≤ D) (z : ℕ) {Y x : ℝ}
    (hY : 0 < Y) (hx : 0 ≤ x) {B : ℕ} (hB : x + Y ≤ B) :
    additiveRoughWindow B z Y x ≤ canonicalUpperMain D z +
      ‖sieveWindowError (D ^ 2) (canonicalUpperSieve D z) Y x‖ := by
  have hu := additiveRoughWindow_upper hD z hY hx hB
  have he := sieveWindowError_re (D ^ 2) (canonicalUpperSieve D z) Y x
  rw [← canonicalUpperMain_truncated] at he
  have hn := Complex.re_le_norm (sieveWindowError (D ^ 2) (canonicalUpperSieve D z) Y x)
  linarith

theorem additiveRoughWindow_ge_main_error {D z : ℕ} (hD : 1 ≤ D) (hz : 1 ≤ z) {Y x : ℝ}
    (hY : 0 < Y) (hx : 0 ≤ x) {B : ℕ} (hB : x + Y ≤ B) :
    canonicalLowerMain D z - ‖sieveWindowError (z * D ^ 2) (lowerSieveCoefficient D z) Y x‖ ≤
      additiveRoughWindow B z Y x := by
  have hl := additiveRoughWindow_lower hD hz hY hx hB
  have he := sieveWindowError_re (z * D ^ 2) (lowerSieveCoefficient D z) Y x
  rw [lowerSieveCoefficient_main_sum hD hz] at he
  have hn := (abs_le.mp (Complex.abs_re_le_norm
    (sieveWindowError (z * D ^ 2) (lowerSieveCoefficient D z) Y x))).1
  linarith

end Erdos421
