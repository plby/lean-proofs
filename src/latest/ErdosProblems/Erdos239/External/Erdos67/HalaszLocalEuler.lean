import ErdosProblems.Erdos239.External.Erdos67.EulerResidue

/-!
# The local Euler estimate in Halasz's argument

This file extracts the pointwise real-part estimate which turns the logarithm
of a local Euler factor into its first prime term.  Its only analytic input is
the quadratic Taylor remainder already proved in `EulerResidue`.
-/

open Complex

namespace Erdos67.HalaszLocalEuler

noncomputable section

open Erdos67.EulerResidue

/-- The real part of a local Euler logarithm is at most its linear term plus
the quadratic Taylor error. -/
theorem neg_log_one_sub_re_le_add_norm_sq {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    (-Complex.log (1 - z)).re ≤ z.re + ‖z‖ ^ 2 := by
  have hrem := norm_neg_log_one_sub_sub_self_le_sq hz
  have hre := Complex.re_le_norm (-Complex.log (1 - z) - z)
  simp only [Complex.sub_re] at hre
  linarith

/-- At a prime and to the right of the line `re s = 1`, a unit-valued
completely multiplicative coefficient has the expected local Halasz upper
bound.  The error is written using the bare zeta weight, since multiplication
by `h p` preserves its norm. -/
theorem neg_log_primeEulerFactor_re_le
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re)
    {p : ℕ} (hp : p.Prime) :
    (-Complex.log (1 - h p * (p : ℂ) ^ (-s))).re ≤
      (h p * (p : ℂ) ^ (-s)).re + ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
  let w : ℂ := (p : ℂ) ^ (-s)
  let z : ℂ := h p * w
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hwInv : ‖w‖ ≤ (p : ℝ)⁻¹ := by
    dsimp only [w]
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hpOne (by simp; linarith)
  have hwHalf : ‖w‖ ≤ 1 / 2 := by
    exact hwInv.trans (by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hpTwo)
  have hzNorm : ‖z‖ = ‖w‖ := by
    dsimp only [z]
    rw [norm_mul, hh hp.ne_zero, one_mul]
  have hzHalf : ‖z‖ ≤ 1 / 2 := hzNorm.le.trans hwHalf
  simpa only [z, w, hzNorm] using neg_log_one_sub_re_le_add_norm_sq hzHalf

/-- Direct comparison with the corresponding zeta local logarithm.  The
linear discrepancy is `‖h p - 1‖` times the zeta weight, and both local Taylor
remainders contribute one quadratic weight. -/
theorem neg_log_primeEulerFactor_re_le_zetaLocal
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re)
    {p : ℕ} (hp : p.Prime) :
    (-Complex.log (1 - h p * (p : ℂ) ^ (-s))).re ≤
      (-Complex.log (1 - (p : ℂ) ^ (-s))).re +
        ‖h p - 1‖ * ‖(p : ℂ) ^ (-s)‖ + 2 * ‖(p : ℂ) ^ (-s)‖ ^ 2 := by
  let w : ℂ := (p : ℂ) ^ (-s)
  let z : ℂ := h p * w
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hwInv : ‖w‖ ≤ (p : ℝ)⁻¹ := by
    dsimp only [w]
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hpOne (by simp; linarith)
  have hwHalf : ‖w‖ ≤ 1 / 2 := by
    exact hwInv.trans (by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hpTwo)
  have hzNorm : ‖z‖ = ‖w‖ := by
    dsimp only [z]
    rw [norm_mul, hh hp.ne_zero, one_mul]
  have hzHalf : ‖z‖ ≤ 1 / 2 := hzNorm.le.trans hwHalf
  have hcmp := norm_neg_log_one_sub_sub_neg_log_one_sub_le hzHalf hwHalf
  have hre := Complex.re_le_norm
    (-Complex.log (1 - z) - (-Complex.log (1 - w)))
  have hzw : ‖z - w‖ = ‖h p - 1‖ * ‖w‖ := by
    rw [show z - w = (h p - 1) * w by simp only [z]; ring, norm_mul]
  simp only [Complex.sub_re] at hre
  rw [hzw, hzNorm] at hcmp
  dsimp only [z, w] at hre ⊢
  linarith

end

end Erdos67.HalaszLocalEuler
