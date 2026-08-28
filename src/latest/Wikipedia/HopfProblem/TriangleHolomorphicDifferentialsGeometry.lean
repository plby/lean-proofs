import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Scalar derivatives in the upper-half-plane coordinate

The scalar derivative is the ordinary complex derivative in the actual
upper-half-plane chart.  Chart inversion is used only on its open target.
Holomorphicity of this derivative and its chain rule are proved for the
genuine holomorphic functions and maps on the upper half-plane.
-/

noncomputable section

open Filter Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

/-- The complex derivative in the literal upper-half-plane coordinate. -/
def scalarDeriv (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  deriv (f ∘ UpperHalfPlane.ofComplex) (z : ℂ)

/-- Holomorphicity supplies the ordinary derivative in the actual chart. -/
theorem scalarHasDerivAt {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (z : ℍ) :
    HasDerivAt (f ∘ UpperHalfPlane.ofComplex) (scalarDeriv f z) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiableAt_iff.mp
    ((hf z).mdifferentiableAt (by simp))).hasDerivAt

/-- Differentiation preserves holomorphicity on the upper half-plane. -/
theorem scalarDeriv_holomorphic {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (scalarDeriv f) := by
  have hd : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex)
      UpperHalfPlane.upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp (hf.mdifferentiable (by simp))
  intro z
  apply UpperHalfPlane.contMDiffAt_iff.mpr
  apply (((hd.deriv UpperHalfPlane.isOpen_upperHalfPlaneSet).analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet) (z : ℂ) z.im_pos).contDiffAt.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.im_pos] with w hw
  exact congrArg (deriv (f ∘ UpperHalfPlane.ofComplex)) hw

/-- The scalar chain rule for a holomorphic upper-half-plane map. -/
theorem scalarDeriv_comp {f : ℍ → ℂ} {h : ℍ → ℍ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hh : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω h) (z : ℍ) :
    scalarDeriv (f ∘ h) z =
      scalarDeriv f (h z) * scalarDeriv (fun w : ℍ => (h w : ℂ)) z := by
  have hh' := scalarHasDerivAt (UpperHalfPlane.contMDiff_coe.comp hh) z
  have hf' : HasDerivAt (f ∘ UpperHalfPlane.ofComplex) (scalarDeriv f (h z))
      (((fun w : ℍ => (h w : ℂ)) ∘ UpperHalfPlane.ofComplex) (z : ℂ)) := by
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      scalarHasDerivAt hf (h z)
  have hc := hf'.comp (z : ℂ) hh'
  have hc' : HasDerivAt ((f ∘ h) ∘ UpperHalfPlane.ofComplex)
      (scalarDeriv f (h z) * scalarDeriv (fun w : ℍ => (h w : ℂ)) z) (z : ℂ) := by
    simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using hc
  exact hc'.deriv

@[simp] theorem scalarDeriv_coe (z : ℍ) :
    scalarDeriv (fun w : ℍ => (w : ℂ)) z = 1 :=
  ((hasDerivAt_id (z : ℂ)).congr_of_eventuallyEq
    (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.im_pos)).deriv

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
