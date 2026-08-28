import Wikipedia.HopfProblem.HolomorphicCousinGreenIdentityDeriv
import Wikipedia.HopfProblem.HolomorphicCousinGreenIdentityPolar
import Wikipedia.HopfProblem.HolomorphicCousinWirtinger

/-!
# The fundamental compact-support Cauchy--Green identity

For a continuously real-differentiable compactly supported function on the
complex plane, the reciprocal kernel integrates its antiholomorphic derivative
to minus pi times its value at zero.  The proof uses the actual Lebesgue polar
change of variables and the one-dimensional fundamental theorem of calculus.
-/

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology Interval

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- Multiplication by the polar area factor removes the reciprocal singularity. -/
theorem green_polar_integrand (φ : ℂ → ℂ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    p.1 • ((Complex.polarCoord.symm p)⁻¹ * dbar φ (Complex.polarCoord.symm p)) =
      (greenRadial φ p + Complex.I * greenAngular φ p) / 2 := by
  have hr : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [polarCoord_symm_eq_greenUnit, Complex.real_smul, dbar]
  unfold greenRadial greenAngular
  rw [polar_realLinear_identity, Complex.star_def,
    ← Complex.inv_eq_conj (norm_greenUnit p.2)]
  field_simp

private theorem greenRadial_radius_vanish {φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hz : ∀ z : ℂ, R ≤ ‖z‖ → fderiv ℝ φ z = 0) :
    ∀ p : ℝ × ℝ, R < p.1 → greenRadial φ p = 0 := by
  intro p hp
  have hn : R ≤ ‖(p.1 : ℂ) * greenUnit p.2‖ := by
    simpa only [norm_mul, norm_greenUnit, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hR.trans hp)] using hp.le
  simp only [greenRadial, hz _ hn, zero_apply]

private theorem greenAngular_radius_vanish {φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hz : ∀ z : ℂ, R ≤ ‖z‖ → fderiv ℝ φ z = 0) :
    ∀ p : ℝ × ℝ, R < p.1 → greenAngular φ p = 0 := by
  intro p hp
  have hn : R ≤ ‖(p.1 : ℂ) * greenUnit p.2‖ := by
    simpa only [norm_mul, norm_greenUnit, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hR.trans hp)] using hp.le
  simp only [greenAngular, hz _ hn, zero_apply]

theorem integrableOn_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : IntegrableOn (greenRadial φ) polarCoord.target := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  exact integrableOn_polarTarget_of_radial_support
    (continuous_greenRadial hφ).continuousOn
    (greenRadial_radius_vanish hR (fun z h => (hz z h).2))

theorem integrableOn_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : IntegrableOn (greenAngular φ) polarCoord.target := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  exact integrableOn_polarTarget_of_radial_support
    (continuous_greenAngular hφ).continuousOn
    (greenAngular_radius_vanish hR (fun z h => (hz z h).2))

/-- The radial part gives the evaluation functional at the origin. -/
theorem integral_greenRadial_polarTarget {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    (∫ p in polarCoord.target, greenRadial φ p) = -(2 * (Real.pi : ℂ)) * φ 0 := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  rw [integral_polarTarget_eq_angle_radius hR.le
    (continuous_greenRadial hφ).continuousOn
    (greenRadial_radius_vanish hR (fun z h => (hz z h).2))]
  have hend (θ : ℝ) : φ ((R : ℂ) * greenUnit θ) = 0 := by
    apply (hz _ _).1
    simp [abs_of_pos hR]
  simp_rw [integral_greenRadial hφ, hend, zero_sub]
  simp only [intervalIntegral.integral_const, Complex.real_smul,
    sub_neg_eq_add, Complex.ofReal_add]
  ring

/-- The angular part vanishes by periodicity, with the radius-zero endpoint
irrelevant to the Lebesgue integral. -/
theorem integral_greenAngular_polarTarget {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    (∫ p in polarCoord.target, greenAngular φ p) = 0 := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  rw [integral_polarTarget_eq_radius_angle hR.le
    (continuous_greenAngular hφ).continuousOn
    (greenAngular_radius_vanish hR (fun z h => (hz z h).2))]
  apply intervalIntegral.integral_zero_ae
  filter_upwards with r hr
  have hr' : r ∈ Ioc 0 R := by simpa only [uIoc_of_le hR.le] using hr
  exact integral_greenAngular hφ hr'.1.ne'

/-- **Fundamental Cauchy--Green identity.** The normalization here is
`∂̄ = (∂ₓ + i∂ᵧ)/2` and Lebesgue area measure on the complex plane. -/
theorem integral_inv_mul_dbar {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    (∫ w : ℂ, w⁻¹ * dbar φ w) = -(Real.pi : ℂ) * φ 0 := by
  rw [← Complex.integral_comp_polarCoord_symm]
  calc
    (∫ p in polarCoord.target,
        p.1 • ((Complex.polarCoord.symm p)⁻¹ * dbar φ (Complex.polarCoord.symm p))) =
        ∫ p in polarCoord.target, (greenRadial φ p + Complex.I * greenAngular φ p) / 2 := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      exact green_polar_integrand φ p hp.1
    _ = ((∫ p in polarCoord.target, greenRadial φ p) +
        Complex.I * (∫ p in polarCoord.target, greenAngular φ p)) / 2 := by
      rw [integral_div, integral_add (integrableOn_greenRadial hφ hc)
        ((integrableOn_greenAngular hφ hc).const_mul Complex.I), integral_const_mul]
    _ = -(Real.pi : ℂ) * φ 0 := by
      rw [integral_greenRadial_polarTarget hφ hc, integral_greenAngular_polarTarget hφ hc]
      ring

end Wikipedia.HopfProblem.HolomorphicCousin
