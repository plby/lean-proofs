import Util.Linnik.PowerScale

/-!
# Polynomially small errors on the Linnik scale

Both explicit-formula truncation and the far-left zero remainder are
smaller than `epsilon * x/n`.  The same holds for the finite conductor
correction and the higher-prime-power remainder.
-/

namespace Linnik

open Filter Erdos48 BoundedGaps.Maynard
open scoped Topology

theorem eventually_const_log_sq_div_sq_le_div (C : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      C * (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤ epsilon / n := by
  have hlim := tendsto_log_sq_div_nat.const_mul C
  simp only [mul_zero] at hlim
  have hsmall : ∀ᶠ n : ℕ in atTop, C * (Real.log (n : ℝ) ^ 2 / n) < epsilon := by
    simpa only [mul_zero] using hlim.eventually (gt_mem_nhds hepsilon)
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn₁
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := div_le_div_of_nonneg_right hn.le hnR.le
  have heq : C * (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) =
      (C * (Real.log (n : ℝ) ^ 2 / n)) / n := by field_simp
  rw [heq]
  exact h

theorem eventually_powerScale_analyticErrors_le
    (K A L : ℕ) (hL : 64 ≤ L) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 * ((K : ℝ) * dirichletExplicitFormulaErrorScale
        ((n ^ L : ℕ) : ℝ) n ((n ^ 4 : ℕ) : ℝ)) +
      (n : ℝ) ^ 2 * (96 * (A : ℝ) *
        (((n ^ L : ℕ) : ℝ) ^ (15 / 16 : ℝ)) * logScale n ^ 2) ≤
        epsilon * ((n ^ L : ℕ) : ℝ) / n := by
  let C : ℝ := (K : ℝ) * ((L : ℝ) + 1) ^ 2 + 3456 * A
  filter_upwards [eventually_const_log_sq_div_sq_le_div C hepsilon, eventually_ge_atTop 2]
    with n hn hn₂
  rw [powerScale_explicitError_eq (by omega : 0 < n)]
  have hfar := powerScale_farKernel_le (A := A) hn₂ hL
  have hsmall := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α := ℝ) (n ^ L))
  calc
    _ ≤ ((n ^ L : ℕ) : ℝ) * (C * (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) := by
      dsimp [C]
      nlinarith [hfar]
    _ ≤ ((n ^ L : ℕ) : ℝ) * (epsilon / n) := hsmall
    _ = _ := by ring

theorem eventually_powerScale_progressionCorrection_le
    (L : ℕ) (hL : 8 ≤ L) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (Real.log ((n * n ^ L : ℕ) : ℝ) ^ 2 +
        (Chebyshev.psi ((n ^ L : ℕ) : ℝ) - Chebyshev.theta ((n ^ L : ℕ) : ℝ))) ≤
        epsilon * ((n ^ L : ℕ) : ℝ) / n := by
  let C : ℝ := ((L : ℝ) + 1) ^ 2 + 2 * L
  have hlim := tendsto_log_sq_div_nat_sq.const_mul C
  simp only [mul_zero] at hlim
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C * (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) < epsilon := by
    simpa only [mul_zero] using hlim.eventually (gt_mem_nhds hepsilon)
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hsmall, hlogTop.eventually_ge_atTop 1, eventually_ge_atTop 2]
    with n hsmall hlog hn
  simp only [Function.comp_apply] at hlog
  let x : ℝ := ((n ^ L : ℕ) : ℝ)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn₀ : (0 : ℝ) < n := by linarith
  have hx₁ : 1 ≤ x := by dsimp [x]; exact_mod_cast Nat.one_le_pow L n (by omega)
  have hx₀ : 0 ≤ x := by linarith
  have hn4 : (n : ℝ) ^ 4 ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ n) (by omega : 4 ≤ L)
  have hn8 : (n : ℝ) ^ 8 ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ n) hL
  have hsqrt : (n : ℝ) ^ 4 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hn8
    rw [show (n : ℝ) ^ 8 = ((n : ℝ) ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)] at h
    exact h
  have hsqroot := Real.sq_sqrt hx₀
  have hnSq : 0 < (n : ℝ) ^ 2 := by positivity
  have hfirst : (n : ℝ) ^ 2 ≤ x / (n : ℝ) ^ 2 := by
    apply (le_div_iff₀ hnSq).mpr
    nlinarith
  have hsecond : (n : ℝ) ^ 2 * Real.sqrt x ≤ x / (n : ℝ) ^ 2 := by
    apply (le_div_iff₀ hnSq).mpr
    have := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg x)
    nlinarith
  have hlogx : Real.log x = (L : ℝ) * Real.log (n : ℝ) := log_natCast_pow n L
  have hlogprod : Real.log ((n * n ^ L : ℕ) : ℝ) =
      ((L : ℝ) + 1) * Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hn₀.ne' (by positivity), log_natCast_pow]
    ring
  have hpp := Chebyshev.psi_sub_theta_le hx₁
  rw [hlogx] at hpp
  have hlogSq : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  have hterm₁ := mul_le_mul_of_nonneg_right hfirst
    (show 0 ≤ ((L : ℝ) + 1) ^ 2 * Real.log (n : ℝ) ^ 2 by positivity)
  have hterm₂ := mul_le_mul_of_nonneg_right hsecond
    (show 0 ≤ 2 * (L : ℝ) * Real.log (n : ℝ) ^ 2 by positivity)
  have hpp' : Chebyshev.psi x - Chebyshev.theta x ≤
      2 * (L : ℝ) * Real.sqrt x * Real.log (n : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlogSq
      (show 0 ≤ 2 * (L : ℝ) * Real.sqrt x by positivity)
    nlinarith
  have hppn := mul_le_mul_of_nonneg_left hpp' (sq_nonneg (n : ℝ))
  have hbound : (n : ℝ) ^ 2 * (Real.log ((n * n ^ L : ℕ) : ℝ) ^ 2 +
      (Chebyshev.psi x - Chebyshev.theta x)) ≤
      x * (C * (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) := by
    rw [hlogprod]
    calc
      _ ≤ x / (n : ℝ) ^ 2 * (((L : ℝ) + 1) ^ 2 * Real.log (n : ℝ) ^ 2) +
          x / (n : ℝ) ^ 2 * (2 * (L : ℝ) * Real.log (n : ℝ) ^ 2) := by nlinarith
      _ = _ := by dsimp [C]; ring
  have hsmall' := mul_le_mul_of_nonneg_left hsmall.le hx₀
  apply (le_div_iff₀ hn₀).mpr
  change (n : ℝ) * (Real.log ((n * n ^ L : ℕ) : ℝ) ^ 2 +
    (Chebyshev.psi x - Chebyshev.theta x)) * n ≤ epsilon * x
  nlinarith

end Linnik
