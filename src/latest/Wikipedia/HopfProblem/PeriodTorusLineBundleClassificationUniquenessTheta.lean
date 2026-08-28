import Wikipedia.HopfProblem.PeriodTorusThetaPositivity
import Wikipedia.HopfProblem.PeriodTorusThetaZero
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Uniqueness of unitary Appell--Humbert data from an actual entire gauge

The quotient of two unitary Appell--Humbert factors is itself the theta
transformation law for the difference of the Hermitian forms.  A nowhere-zero
entire gauge and its reciprocal force that difference to be both nonnegative
and nonpositive.  Polarization then makes the difference zero, and the
zero-form theta theorem makes the gauge constant and the multipliers equal.

This is an intermediate analytic uniqueness theorem.  It assumes the actual
scalar gauge equation, not the existence of an Appell--Humbert presentation
for an arbitrary line bundle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness

open PeriodTorusTheta

theorem isHermitian_sub (H₁ H₂ : HermitianForm)
    (h₁ : IsHermitian H₁) (h₂ : IsHermitian H₂) : IsHermitian (H₁ - H₂) := by
  intro x y
  simp only [LinearMap.sub_apply, h₁ x y, h₂ x y, star_sub]

theorem isHermitian_neg (H : HermitianForm) (hH : IsHermitian H) :
    IsHermitian (-H) := by
  intro x y
  simp only [LinearMap.neg_apply, hH x y, star_neg]

/-- Polarization in the linear-first convention: the real diagonal determines
an actual Hermitian form. -/
theorem hermitian_eq_zero_of_real_diagonal_eq_zero (H : HermitianForm)
    (hH : IsHermitian H) (hdiag : ∀ z, (H z z).re = 0) : H = 0 := by
  have hre (x y : ComplexPlane₂) : (H x y).re = 0 := by
    have h := IsHermitian.diagonal_add_re H hH x y
    rw [hdiag, hdiag, hdiag] at h
    linarith
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply Complex.ext
  · simpa only [LinearMap.zero_apply, Complex.zero_re] using hre x y
  · have h := hre (Complex.I • x) y
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h
    simp only [LinearMap.zero_apply, Complex.zero_im]
    linarith

/-- Dividing the actual factors gives the theta law for the difference form. -/
theorem ratio_automorphy (p : PeriodDomain) (H₁ H₂ : HermitianForm)
    (α₁ α₂ : p.lattice → ℂ) (g : ComplexPlane₂ → ℂ)
    (hGauge : ∀ (l : p.lattice) z, g (z + l) =
      (α₂ l * Complex.exp ((Real.pi : ℂ) * H₂ z l + ((Real.pi : ℂ) / 2) * H₂ l l)) /
        (α₁ l * Complex.exp ((Real.pi : ℂ) * H₁ z l + ((Real.pi : ℂ) / 2) * H₁ l l)) *
          g z) :
    AppellHumbertAutomorphy p (H₂ - H₁) (fun l => α₂ l / α₁ l) g := by
  intro l z
  have he :
      ((Real.pi : ℂ) * H₂ z l + ((Real.pi : ℂ) / 2) * H₂ l l) -
          ((Real.pi : ℂ) * H₁ z l + ((Real.pi : ℂ) / 2) * H₁ l l) =
        (Real.pi : ℂ) * (H₂ - H₁) z l + ((Real.pi : ℂ) / 2) * (H₂ - H₁) l l := by
    simp only [LinearMap.sub_apply]
    ring
  rw [hGauge, mul_div_mul_comm, ← Complex.exp_sub, he]

/-- The reciprocal theta function transforms with the negative Hermitian form. -/
theorem inverse_automorphy (p : PeriodDomain) (H : HermitianForm)
    (α : p.lattice → ℂ) (g : ComplexPlane₂ → ℂ)
    (hAuto : AppellHumbertAutomorphy p H α g) :
    AppellHumbertAutomorphy p (-H) (fun l => (α l)⁻¹) (fun z => (g z)⁻¹) := by
  intro l z
  have he : (Real.pi : ℂ) * (-H) z l + ((Real.pi : ℂ) / 2) * (-H) l l =
      -((Real.pi : ℂ) * H z l + ((Real.pi : ℂ) / 2) * H l l) := by
    simp only [LinearMap.neg_apply]
    ring
  dsimp only
  rw [hAuto, he, Complex.exp_neg]
  simp only [mul_inv]

/-- An actual nowhere-zero entire scalar gauge between two unitary
Appell--Humbert factors forces equality of their data and is constant. -/
theorem hermitian_data_eq_of_nonvanishing_gauge (p : PeriodDomain)
    (H₁ H₂ : HermitianForm) (h₁ : IsHermitian H₁) (h₂ : IsHermitian H₂)
    (α₁ α₂ : p.lattice → ℂ) (hα₁ : ∀ l, ‖α₁ l‖ = 1) (hα₂ : ∀ l, ‖α₂ l‖ = 1)
    (g : ComplexPlane₂ → ℂ) (hg : Differentiable ℂ g) (hgne : ∀ z, g z ≠ 0)
    (hGauge : ∀ (l : p.lattice) z, g (z + l) =
      (α₂ l * Complex.exp ((Real.pi : ℂ) * H₂ z l + ((Real.pi : ℂ) / 2) * H₂ l l)) /
        (α₁ l * Complex.exp ((Real.pi : ℂ) * H₁ z l + ((Real.pi : ℂ) / 2) * H₁ l l)) *
          g z) :
    H₁ = H₂ ∧ α₁ = α₂ ∧ ∀ z, g z = g 0 := by
  let H : HermitianForm := H₂ - H₁
  let α : p.lattice → ℂ := fun l => α₂ l / α₁ l
  have hH : IsHermitian H := isHermitian_sub H₂ H₁ h₂ h₁
  have hα : ∀ l, ‖α l‖ = 1 := by
    intro l
    simp only [α, norm_div, hα₂, hα₁, div_self (one_ne_zero : (1 : ℝ) ≠ 0)]
  have hAuto : AppellHumbertAutomorphy p H α g :=
    ratio_automorphy p H₁ H₂ α₁ α₂ g hGauge
  have hInvAuto := inverse_automorphy p H α g hAuto
  have hInvα : ∀ l, ‖(α l)⁻¹‖ = 1 := by
    intro l
    simp only [norm_inv, hα, inv_one]
  have hNonzero : ∃ z, g z ≠ 0 := ⟨0, hgne 0⟩
  have hInvNonzero : ∃ z, (g z)⁻¹ ≠ 0 := ⟨0, inv_ne_zero (hgne 0)⟩
  have hHzero : H = 0 := by
    apply hermitian_eq_zero_of_real_diagonal_eq_zero H hH
    intro v
    have hp := hermitian_nonnegative_of_nonzero_theta p H hH α hα g hg
      hAuto hNonzero v
    have hn := hermitian_nonnegative_of_nonzero_theta p (-H) (isHermitian_neg H hH)
      (fun l => (α l)⁻¹) hInvα (fun z => (g z)⁻¹) (hg.inv hgne)
      hInvAuto hInvNonzero v
    simp only [LinearMap.neg_apply, Complex.neg_re] at hn
    linarith
  have hAutoZero : AppellHumbertAutomorphy p 0 α g := by
    simpa only [hHzero] using hAuto
  refine ⟨(sub_eq_zero.mp hHzero).symm, ?_,
    theta_eq_at_zero_of_zero_form p α hα g hg hAutoZero⟩
  funext l
  have he := multiplier_eq_one_of_zero_form p α hα g hg hAutoZero hNonzero l
  have hne : α₁ l ≠ 0 := by
    intro hzero
    have hn := hα₁ l
    simp only [hzero, norm_zero] at hn
    exact zero_ne_one hn
  exact ((div_eq_one_iff_eq hne).mp he).symm

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness
