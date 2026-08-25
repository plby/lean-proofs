import Util.Bernays.HalfPlaneSquareIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Fourier estimates for compactly truncated vertical lines
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform

namespace Bernays

noncomputable def verticalProduct (f : ℂ → ℂ) (ψ : ℝ → ℂ) (σ : ℝ) (t : ℝ) : ℂ :=
  f ((σ : ℂ) + t * Complex.I) * ψ t

theorem vertical_hasDerivAt {f : ℂ → ℂ} {σ t : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * Complex.I)) :
    HasDerivAt (fun t : ℝ => f ((σ : ℂ) + t * Complex.I))
      (deriv f ((σ : ℂ) + t * Complex.I) * Complex.I) t := by
  have hin : HasDerivAt (fun z : ℂ => (σ : ℂ) + z * Complex.I) Complex.I (t : ℂ) := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (σ : ℂ)
  exact (hf.hasDerivAt.comp (t : ℂ) hin).comp_ofReal

theorem verticalProduct_hasDerivAt {f : ℂ → ℂ} {ψ : ℝ → ℂ} {σ t : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * Complex.I)) (hψ : DifferentiableAt ℝ ψ t) :
    HasDerivAt (verticalProduct f ψ σ)
      (deriv f ((σ : ℂ) + t * Complex.I) * Complex.I * ψ t +
        f ((σ : ℂ) + t * Complex.I) * deriv ψ t) t :=
  (vertical_hasDerivAt hf).mul hψ.hasDerivAt

theorem verticalProduct_deriv_norm_le {f : ℂ → ℂ} {ψ : ℝ → ℂ} {σ t C : ℝ}
    (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * Complex.I)) (hψ : DifferentiableAt ℝ ψ t)
    (hψ₀ : ‖ψ t‖ ≤ C) (hψ₁ : ‖deriv ψ t‖ ≤ C) :
    ‖deriv (verticalProduct f ψ σ) t‖ ≤
      C * (‖deriv f ((σ : ℂ) + t * Complex.I)‖ + ‖f ((σ : ℂ) + t * Complex.I)‖) := by
  rw [(verticalProduct_hasDerivAt hf hψ).deriv]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_I, mul_one]
  have h₀ := mul_le_mul_of_nonneg_left hψ₀ (norm_nonneg (deriv f ((σ : ℂ) + t * Complex.I)))
  have h₁ := mul_le_mul_of_nonneg_left hψ₁ (norm_nonneg (f ((σ : ℂ) + t * Complex.I)))
  nlinarith

theorem verticalProduct_deriv_continuous {f : ℂ → ℂ} {ψ : ℝ → ℂ} {σ : ℝ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hσ : 1 < σ) (hψ : ContDiff ℝ 1 ψ) : Continuous (deriv (verticalProduct f ψ σ)) := by
  have heq : deriv (verticalProduct f ψ σ) = fun t : ℝ =>
      deriv f ((σ : ℂ) + t * Complex.I) * Complex.I * ψ t +
        f ((σ : ℂ) + t * Complex.I) * deriv ψ t := by
    funext t
    exact (verticalProduct_hasDerivAt (hf _ (by simpa using hσ))
      ((hψ.differentiable (by norm_num)) t)).deriv
  rw [heq]
  exact (((halfPlane_vertical_continuous (halfPlane_deriv_continuousOn hf) hσ).mul_const _).mul
    hψ.continuous).add (((halfPlane_vertical_continuous (halfPlane_differentiableOn hf).continuousOn
      hσ)).mul hψ.continuous_deriv_one)

theorem verticalProduct_integrable {f : ℂ → ℂ} {ψ : ℝ → ℂ} {σ : ℝ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hσ : 1 < σ) (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    Integrable (verticalProduct f ψ σ) ∧ Integrable (deriv (verticalProduct f ψ σ)) := by
  have hs : HasCompactSupport (verticalProduct f ψ σ) := hsupp.mul_left
  have hc : Continuous (verticalProduct f ψ σ) :=
    (halfPlane_vertical_continuous (halfPlane_differentiableOn hf).continuousOn hσ).mul hψ.continuous
  exact ⟨hc.integrable_of_hasCompactSupport hs,
    (verticalProduct_deriv_continuous hf hσ hψ).integrable_of_hasCompactSupport hs.deriv⟩

theorem fourier_norm_le_integral_norm (g : ℝ → ℂ) (u : ℝ) :
    ‖𝓕 g u‖ ≤ ∫ t : ℝ, ‖g t‖ := by
  rw [Real.fourier_eq]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

theorem fourier_deriv_norm_bound {g : ℝ → ℂ} (hg : Integrable g)
    (hgd : Differentiable ℝ g) (hg' : Integrable (deriv g)) (u : ℝ) :
    (2 * Real.pi * |u|) * ‖𝓕 g u‖ ≤ ∫ t : ℝ, ‖deriv g t‖ := by
  have heq := congrArg (fun k : ℝ → ℂ => ‖k u‖) (Real.fourier_deriv hg hgd hg')
  simp only [Pi.smul_apply, norm_smul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at heq
  exact heq ▸ fourier_norm_le_integral_norm (deriv g) u

end Bernays
