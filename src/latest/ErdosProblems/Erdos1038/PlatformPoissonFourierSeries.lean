import ErdosProblems.Erdos1038.PlatformPoisson

/-!
# Fourier series of the platform Poisson kernel

This supplies the analytic-kernel form needed to identify Abel-regularized
cosine coefficients with ordinary Poisson convolution.
-/

set_option warningAsError false

namespace Erdos1038

noncomputable section

private lemma complex_geometric_term_re (rho theta : ℝ) (n : ℕ) :
    ((((rho : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)) ^ n).re) =
      rho ^ n * Real.cos ((n : ℝ) * theta) := by
  have hexp : (Complex.exp ((theta : ℂ) * Complex.I)) ^ n =
      Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow]
  have hrpowRe : (((rho : ℂ) ^ n).re) = rho ^ n := by
    norm_cast
  have hrpowIm : (((rho : ℂ) ^ n).im) = 0 := by
    have hrpow : ((rho : ℂ) ^ n) = ((rho ^ n : ℝ) : ℂ) := by
      norm_cast
    rw [hrpow]
    rfl
  rw [Complex.mul_re, hrpowRe, hrpowIm, zero_mul, sub_zero, hexp,
    Complex.exp_ofReal_mul_I_re]

private lemma complex_geometric_term_im (rho theta : ℝ) (n : ℕ) :
    ((((rho : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)) ^ n).im) =
      rho ^ n * Real.sin ((n : ℝ) * theta) := by
  have hexp : (Complex.exp ((theta : ℂ) * Complex.I)) ^ n =
      Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow]
  have hrpowRe : (((rho : ℂ) ^ n).re) = rho ^ n := by
    norm_cast
  have hrpowIm : (((rho : ℂ) ^ n).im) = 0 := by
    have hrpow : ((rho : ℂ) ^ n) = ((rho ^ n : ℝ) : ℂ) := by
      norm_cast
    rw [hrpow]
    rfl
  rw [Complex.mul_im, hrpowRe, hrpowIm, zero_mul, add_zero, hexp,
    Complex.exp_ofReal_mul_I_im]

/-- The real part of the complex geometric series. -/
theorem tsum_rho_pow_mul_cos
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    (∑' n : ℕ, rho ^ n * Real.cos ((n : ℝ) * theta)) =
      (1 - rho * Real.cos theta) /
        (1 - 2 * rho * Real.cos theta + rho ^ 2) := by
  let z : ℂ := (rho : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)
  have hnormExp : ‖Complex.exp ((theta : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.exp_mul_I]
    exact Complex.norm_cos_add_sin_mul_I theta
  have hnorm : ‖z‖ < 1 := by
    dsimp only [z]
    rw [norm_mul, Complex.norm_real, hnormExp, mul_one]
    exact hrho
  have hsum := Complex.hasSum_re (hasSum_geometric_of_norm_lt_one hnorm)
  have hterm : (fun n : ℕ ↦ (z ^ n).re) =
      fun n : ℕ ↦ rho ^ n * Real.cos ((n : ℝ) * theta) := by
    funext n
    exact complex_geometric_term_re rho theta n
  rw [hterm] at hsum
  have hre : z.re = rho * Real.cos theta := by
    dsimp only [z]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
  have him : z.im = rho * Real.sin theta := by
    dsimp only [z]
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      Complex.exp_ofReal_mul_I_im]
    ring
  have hnormSq : Complex.normSq (1 - z) =
      1 - 2 * rho * Real.cos theta + rho ^ 2 := by
    rw [Complex.normSq_apply]
    change (1 - z.re) * (1 - z.re) + (0 - z.im) * (0 - z.im) = _
    rw [hre, him]
    have htrig := Real.sin_sq_add_cos_sq theta
    nlinarith
  have hlimit : ((1 - z)⁻¹).re =
      (1 - rho * Real.cos theta) /
        (1 - 2 * rho * Real.cos theta + rho ^ 2) := by
    rw [Complex.inv_re, hnormSq]
    change (1 - z.re) / (1 - 2 * rho * Real.cos theta + rho ^ 2) = _
    rw [hre]
  rw [hlimit] at hsum
  exact hsum.tsum_eq

/-- The imaginary part of the complex geometric series. -/
theorem tsum_rho_pow_mul_sin
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    (∑' n : ℕ, rho ^ n * Real.sin ((n : ℝ) * theta)) =
      rho * Real.sin theta /
        (1 - 2 * rho * Real.cos theta + rho ^ 2) := by
  let z : ℂ := (rho : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)
  have hnormExp : ‖Complex.exp ((theta : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.exp_mul_I]
    exact Complex.norm_cos_add_sin_mul_I theta
  have hnorm : ‖z‖ < 1 := by
    dsimp only [z]
    rw [norm_mul, Complex.norm_real, hnormExp, mul_one]
    exact hrho
  have hsum := Complex.hasSum_im (hasSum_geometric_of_norm_lt_one hnorm)
  have hterm : (fun n : ℕ ↦ (z ^ n).im) =
      fun n : ℕ ↦ rho ^ n * Real.sin ((n : ℝ) * theta) := by
    funext n
    exact complex_geometric_term_im rho theta n
  rw [hterm] at hsum
  have hre : z.re = rho * Real.cos theta := by
    dsimp only [z]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
  have him : z.im = rho * Real.sin theta := by
    dsimp only [z]
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      Complex.exp_ofReal_mul_I_im]
    ring
  have hnormSq : Complex.normSq (1 - z) =
      1 - 2 * rho * Real.cos theta + rho ^ 2 := by
    rw [Complex.normSq_apply]
    change (1 - z.re) * (1 - z.re) + (0 - z.im) * (0 - z.im) = _
    rw [hre, him]
    have htrig := Real.sin_sq_add_cos_sq theta
    nlinarith
  have hlimit : ((1 - z)⁻¹).im =
      rho * Real.sin theta /
        (1 - 2 * rho * Real.cos theta + rho ^ 2) := by
    rw [Complex.inv_im, hnormSq]
    change -(0 - z.im) / (1 - 2 * rho * Real.cos theta + rho ^ 2) = _
    rw [him]
    ring
  rw [hlimit] at hsum
  exact hsum.tsum_eq

/-- The conjugate Poisson kernel on the circle. -/
def platformConjugatePoissonKernel (rho theta : ℝ) : ℝ :=
  2 * rho * Real.sin theta /
    (1 - 2 * rho * Real.cos theta + rho ^ 2)

/-- Fourier expansion of the conjugate Poisson kernel. -/
theorem platformConjugatePoissonKernel_eq_two_tsum
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    platformConjugatePoissonKernel rho theta =
      2 * ∑' n : ℕ,
        rho ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * theta) := by
  have hsum := tsum_rho_pow_mul_sin hrho theta
  have hsummable : Summable
      (fun n : ℕ ↦ rho ^ n * Real.sin ((n : ℝ) * theta)) := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one (abs_nonneg rho) hrho)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg rho) n)
      (Real.abs_sin_le_one ((n : ℝ) * theta))
  rw [hsummable.tsum_eq_zero_add] at hsum
  simp only [Nat.cast_zero, zero_mul, Real.sin_zero, pow_zero, mul_zero,
    zero_add] at hsum
  calc
    platformConjugatePoissonKernel rho theta =
        2 * (rho * Real.sin theta /
          (1 - 2 * rho * Real.cos theta + rho ^ 2)) := by
      unfold platformConjugatePoissonKernel
      ring
    _ = 2 * ∑' n : ℕ,
        rho ^ (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * theta) := by
      rw [← hsum]

/-- Product-to-sum form of the conjugate Poisson kernel.  This is the
kernel that acts on half-circle cosine coefficients. -/
theorem tsum_rho_pow_mul_sin_mul_cos
    {rho : ℝ} (hrho : |rho| < 1) (theta phi : ℝ) :
    (∑' n : ℕ,
        rho ^ (n + 1) *
          Real.sin (((n + 1 : ℕ) : ℝ) * theta) *
          Real.cos (((n + 1 : ℕ) : ℝ) * phi)) =
      (platformConjugatePoissonKernel rho (theta + phi) +
        platformConjugatePoissonKernel rho (theta - phi)) / 4 := by
  let plusTerm : ℕ → ℝ := fun n ↦
    rho ^ (n + 1) *
      Real.sin (((n + 1 : ℕ) : ℝ) * (theta + phi))
  let minusTerm : ℕ → ℝ := fun n ↦
    rho ^ (n + 1) *
      Real.sin (((n + 1 : ℕ) : ℝ) * (theta - phi))
  have hgeom : Summable (fun n : ℕ ↦ |rho| ^ (n + 1)) :=
    (summable_geometric_of_lt_one (abs_nonneg rho) hrho).comp_injective
      Nat.succ_injective
  have hplus : Summable plusTerm := by
    apply Summable.of_norm_bounded hgeom
    intro n
    rw [Real.norm_eq_abs]
    dsimp only [plusTerm]
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg rho) _)
      (Real.abs_sin_le_one _)
  have hminus : Summable minusTerm := by
    apply Summable.of_norm_bounded hgeom
    intro n
    rw [Real.norm_eq_abs]
    dsimp only [minusTerm]
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg rho) _)
      (Real.abs_sin_le_one _)
  have hterm (n : ℕ) :
      rho ^ (n + 1) *
          Real.sin (((n + 1 : ℕ) : ℝ) * theta) *
          Real.cos (((n + 1 : ℕ) : ℝ) * phi) =
        (plusTerm n + minusTerm n) / 2 := by
    have hplusAngle :
        (((n + 1 : ℕ) : ℝ) * (theta + phi)) =
          ((n + 1 : ℕ) : ℝ) * theta +
            ((n + 1 : ℕ) : ℝ) * phi := by ring
    have hminusAngle :
        (((n + 1 : ℕ) : ℝ) * (theta - phi)) =
          ((n + 1 : ℕ) : ℝ) * theta -
            ((n + 1 : ℕ) : ℝ) * phi := by ring
    dsimp only [plusTerm, minusTerm]
    rw [hplusAngle, hminusAngle, Real.sin_add, Real.sin_sub]
    ring
  have hsum :
      (∑' n : ℕ,
          rho ^ (n + 1) *
            Real.sin (((n + 1 : ℕ) : ℝ) * theta) *
            Real.cos (((n + 1 : ℕ) : ℝ) * phi)) =
        ((∑' n : ℕ, plusTerm n) + ∑' n : ℕ, minusTerm n) / 2 := by
    calc
      (∑' n : ℕ,
          rho ^ (n + 1) *
            Real.sin (((n + 1 : ℕ) : ℝ) * theta) *
            Real.cos (((n + 1 : ℕ) : ℝ) * phi)) =
          ∑' n : ℕ, (plusTerm n + minusTerm n) / 2 := by
        apply tsum_congr
        exact hterm
      _ = ((∑' n : ℕ, plusTerm n) + ∑' n : ℕ, minusTerm n) / 2 := by
        rw [show (fun n : ℕ ↦ (plusTerm n + minusTerm n) / 2) =
            fun n ↦ (1 / 2) * (plusTerm n + minusTerm n) by
          funext n
          ring,
          (hplus.add hminus).tsum_mul_left (1 / 2),
          hplus.tsum_add hminus]
        ring
  rw [hsum,
    platformConjugatePoissonKernel_eq_two_tsum hrho (theta + phi),
    platformConjugatePoissonKernel_eq_two_tsum hrho (theta - phi)]
  dsimp only [plusTerm, minusTerm]
  ring

/-- Fourier expansion of the real Poisson kernel. -/
theorem platformPoissonKernel_eq_one_add_two_tsum
    {rho : ℝ} (hrho : |rho| < 1) (theta : ℝ) :
    platformPoissonKernel rho theta =
      1 + 2 * ∑' n : ℕ,
        rho ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * theta) := by
  have hsum := tsum_rho_pow_mul_cos hrho theta
  have hsummable : Summable
      (fun n : ℕ ↦ rho ^ n * Real.cos ((n : ℝ) * theta)) := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one (abs_nonneg rho) hrho)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg rho) n)
      (Real.abs_cos_le_one ((n : ℝ) * theta))
  rw [hsummable.tsum_eq_zero_add] at hsum
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, pow_zero, one_mul] at hsum
  have hmulAbs : |rho * Real.cos theta| ≤ |rho| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg rho)
      (Real.abs_cos_le_one theta)
  have hmul : rho * Real.cos theta ≤ |rho| :=
    (le_abs_self (rho * Real.cos theta)).trans hmulAbs
  have hden : 0 < 1 - 2 * rho * Real.cos theta + rho ^ 2 := by
    have hsquare : 0 < (1 - |rho|) ^ 2 :=
      sq_pos_of_pos (sub_pos.mpr hrho)
    have habssq : |rho| ^ 2 = rho ^ 2 := sq_abs rho
    nlinarith
  unfold platformPoissonKernel
  let S := ∑' n : ℕ,
    rho ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * theta)
  have hS : S =
      (1 - rho * Real.cos theta) /
          (1 - 2 * rho * Real.cos theta + rho ^ 2) - 1 := by
    dsimp only [S]
    linarith [hsum]
  change (1 - rho ^ 2) /
      (1 - 2 * rho * Real.cos theta + rho ^ 2) = 1 + 2 * S
  rw [hS]
  rw [show 1 + 2 *
      ((1 - rho * Real.cos theta) /
          (1 - 2 * rho * Real.cos theta + rho ^ 2) - 1) =
      2 * ((1 - rho * Real.cos theta) /
          (1 - 2 * rho * Real.cos theta + rho ^ 2)) - 1 by ring]
  apply (div_eq_iff hden.ne').2
  calc
    1 - rho ^ 2 =
        2 * (1 - rho * Real.cos theta) -
          (1 - 2 * rho * Real.cos theta + rho ^ 2) := by ring
    _ = (2 * ((1 - rho * Real.cos theta) /
          (1 - 2 * rho * Real.cos theta + rho ^ 2)) - 1) *
          (1 - 2 * rho * Real.cos theta + rho ^ 2) := by
      rw [sub_mul]
      rw [show 2 * ((1 - rho * Real.cos theta) /
            (1 - 2 * rho * Real.cos theta + rho ^ 2)) *
            (1 - 2 * rho * Real.cos theta + rho ^ 2) =
          2 * (((1 - rho * Real.cos theta) /
            (1 - 2 * rho * Real.cos theta + rho ^ 2)) *
              (1 - 2 * rho * Real.cos theta + rho ^ 2)) by ring,
        div_mul_cancel₀ _ hden.ne']
      ring

end

end Erdos1038
