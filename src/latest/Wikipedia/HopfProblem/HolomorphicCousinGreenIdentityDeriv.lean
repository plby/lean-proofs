import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Differential identities for the compact-support Cauchy--Green formula

The two components below are the radial derivative and the angular derivative
divided by the radius.  Unlike the reciprocal complex kernel, both components
extend continuously across radius zero.
-/

noncomputable section

open Complex MeasureTheory Metric Set
open scoped Topology Interval

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The unit vector used by polar coordinates. -/
def greenUnit (θ : ℝ) : ℂ := circleMap 0 1 θ

theorem greenUnit_eq (θ : ℝ) :
    greenUnit θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  simp [greenUnit, circleMap, Complex.exp_mul_I]

@[simp] theorem norm_greenUnit (θ : ℝ) : ‖greenUnit θ‖ = 1 := by
  simp [greenUnit]

theorem greenUnit_ne_zero (θ : ℝ) : greenUnit θ ≠ 0 :=
  norm_ne_zero_iff.mp (by simp)

theorem continuous_greenUnit : Continuous greenUnit := by
  exact continuous_circleMap 0 1

theorem polarCoord_symm_eq_greenUnit (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * greenUnit p.2 := by
  simp [Complex.polarCoord_symm_apply, greenUnit_eq]

theorem realLinear_apply_complex (D : ℂ →L[ℝ] ℂ) (z : ℂ) :
    D z = (z.re : ℂ) * D 1 + (z.im : ℂ) * D Complex.I := by
  calc
    D z = D (z.re • (1 : ℂ) + z.im • Complex.I) := by
      congr 1
      simp [Complex.real_smul]
    _ = (z.re : ℂ) * D 1 + (z.im : ℂ) * D Complex.I := by
      rw [map_add, map_smul, map_smul]
      simp [Complex.real_smul]

/-- The real-linear form of the polar Wirtinger identity. -/
theorem polar_realLinear_identity (D : ℂ →L[ℝ] ℂ) (z : ℂ) :
    D z + Complex.I * D (Complex.I * z) =
      star z * (D 1 + Complex.I * D Complex.I) := by
  have hc : star z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [realLinear_apply_complex D z, realLinear_apply_complex D (Complex.I * z), hc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub, zero_add, Complex.ofReal_neg]
  ring_nf
  simp [Complex.I_sq]

/-- The radial derivative of the test function in polar coordinates. -/
def greenRadial (φ : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ φ ((p.1 : ℂ) * greenUnit p.2) (greenUnit p.2)

/-- The angular derivative divided by radius, extended to radius zero. -/
def greenAngular (φ : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ φ ((p.1 : ℂ) * greenUnit p.2) (Complex.I * greenUnit p.2)

theorem continuous_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (greenRadial φ) := by
  exact (hφ.continuous_fderiv_apply one_ne_zero).comp
    (((Complex.continuous_ofReal.comp continuous_fst).mul
      (continuous_greenUnit.comp continuous_snd)).prodMk
        (continuous_greenUnit.comp continuous_snd))

theorem continuous_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (greenAngular φ) := by
  exact (hφ.continuous_fderiv_apply one_ne_zero).comp
    (((Complex.continuous_ofReal.comp continuous_fst).mul
      (continuous_greenUnit.comp continuous_snd)).prodMk
        (continuous_const.mul (continuous_greenUnit.comp continuous_snd)))

theorem hasDerivAt_green_radial {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ)
    (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => φ ((t : ℂ) * greenUnit θ))
      (greenRadial φ (r, θ)) r := by
  apply (hφ _).hasFDerivAt.comp_hasDerivAt
  simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (greenUnit θ)

theorem hasDerivAt_green_angular {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ)
    (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => φ ((r : ℂ) * greenUnit t))
      ((r : ℂ) * greenAngular φ (r, θ)) θ := by
  have hu : HasDerivAt greenUnit (Complex.I * greenUnit θ) θ := by
    change HasDerivAt (circleMap 0 1) (Complex.I * circleMap 0 1 θ) θ
    simpa [mul_comm] using hasDerivAt_circleMap 0 1 θ
  have hd := (hφ _).hasFDerivAt.comp_hasDerivAt θ (hu.const_mul (r : ℂ))
  simpa only [Function.comp_def, ← Complex.real_smul, map_smul, greenAngular] using hd

/-- The radial term is evaluated by the one-dimensional fundamental theorem. -/
theorem integral_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (R θ : ℝ) :
    (∫ r in 0..R, greenRadial φ (r, θ)) =
      φ ((R : ℂ) * greenUnit θ) - φ 0 := by
  have hint : IntervalIntegrable (fun r => greenRadial φ (r, θ)) volume 0 R :=
    ((continuous_greenRadial hφ).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_green_radial (hφ.differentiable one_ne_zero) r θ) hint

/-- On every positive-radius circle, the angular term integrates to zero. -/
theorem integral_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {r : ℝ} (hr : r ≠ 0) :
    (∫ θ in (-Real.pi)..Real.pi, greenAngular φ (r, θ)) = 0 := by
  have hint : IntervalIntegrable (fun θ => (r : ℂ) * greenAngular φ (r, θ))
      volume (-Real.pi) Real.pi :=
    (continuous_const.mul ((continuous_greenAngular hφ).comp
      (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_green_angular (hφ.differentiable one_ne_zero) r θ) hint
  have hend : greenUnit Real.pi = greenUnit (-Real.pi) := by
    simp [greenUnit_eq]
  have hz : (r : ℂ) * (∫ θ in (-Real.pi)..Real.pi, greenAngular φ (r, θ)) = 0 := by
    simpa only [intervalIntegral.integral_const_mul, hend, sub_self] using heq
  exact (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr hr)

/-- Compact support supplies one radius at which both the function and all
its first derivatives vanish, and beyond which they remain zero. -/
theorem exists_green_support_radius {φ : ℂ → ℂ} (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → φ z = 0 ∧ fderiv ℝ φ z = 0 := by
  obtain ⟨R, hR, hs⟩ := hφ.isBounded.subset_ball_lt 0 (0 : ℂ)
  refine ⟨R, hR, ?_⟩
  intro z hz
  have hn : z ∉ tsupport φ := by
    intro hmem
    have hlt : ‖z‖ < R := by simpa using hs hmem
    exact not_lt_of_ge hz hlt
  exact ⟨image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn⟩

end Wikipedia.HopfProblem.HolomorphicCousin
