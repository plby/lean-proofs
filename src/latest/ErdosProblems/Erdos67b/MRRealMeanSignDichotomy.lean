import Mathlib.Analysis.Complex.Basic

/-!
# The real-sign step in Granville--Soundararajan mean stability

For real multiplicative functions, the source proof of slow variation first
compares a mean with a small Archimedean rotation of another mean.  If the
two real means have opposite signs, that comparison forces both means to be
small.  If they have the same sign, slow variation of their absolute values
is already slow variation of the means themselves.  This file records that
purely algebraic dichotomy.
-/

namespace Erdos67b

/-- A rough signed comparison together with slow variation of absolute
values gives slow variation of two real numbers.  The factor `2` is the
opposite-sign loss in the source proof. -/
theorem abs_sub_le_max_absNormDiff_two_mul
    {x y epsilon delta : ℝ}
    (hrough : |x - y| ≤ |y| / 2 + epsilon)
    (habs : abs (|x| - |y|) ≤ delta) :
    |x - y| ≤ max delta (2 * epsilon) := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hx, abs_of_nonneg hy] at habs
      exact habs.trans (le_max_left _ _)
    · have hy' : y ≤ 0 := le_of_not_ge hy
      have hxy : 0 ≤ x - y := by linarith
      rw [abs_of_nonpos hy', abs_of_nonneg hxy] at hrough
      rw [abs_of_nonneg hxy]
      have hyabs : -y / 2 ≤ epsilon := by linarith
      calc
        x - y ≤ -y / 2 + epsilon := hrough
        _ ≤ 2 * epsilon := by linarith
        _ ≤ max delta (2 * epsilon) := le_max_right _ _
  · have hx' : x ≤ 0 := le_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have hxy : x - y ≤ 0 := by linarith
      rw [abs_of_nonneg hy, abs_of_nonpos hxy] at hrough
      rw [abs_of_nonpos hxy]
      have hyabs : y / 2 ≤ epsilon := by linarith
      calc
        -(x - y) ≤ y / 2 + epsilon := hrough
        _ ≤ 2 * epsilon := by linarith
        _ ≤ max delta (2 * epsilon) := le_max_right _ _
    · have hy' : y ≤ 0 := le_of_not_ge hy
      rw [abs_of_nonpos hx', abs_of_nonpos hy'] at habs
      rw [show -x - -y = -(x - y) by ring, abs_neg] at habs
      exact habs.trans (le_max_left _ _)

/-- Complex wrapper for two quantities known to lie on the real axis. -/
theorem norm_sub_le_max_normDiff_two_mul_of_real
    {z w : ℂ} {epsilon delta : ℝ}
    (hz : z.im = 0) (hw : w.im = 0)
    (hrough : ‖z - w‖ ≤ ‖w‖ / 2 + epsilon)
    (habs : |‖z‖ - ‖w‖| ≤ delta) :
    ‖z - w‖ ≤ max delta (2 * epsilon) := by
  have hzEq : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hz
  have hwEq : w = (w.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hw
  have hrough' : |z.re - w.re| ≤ |w.re| / 2 + epsilon := by
    rw [hzEq, hwEq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at hrough
    exact hrough
  have habs' : abs (|z.re| - |w.re|) ≤ delta := by
    rw [hzEq, hwEq, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs] at habs
    exact habs
  have hresult := abs_sub_le_max_absNormDiff_two_mul hrough' habs'
  rw [hzEq, hwEq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hresult

end Erdos67b
