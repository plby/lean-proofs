import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Wikipedia.NoExoticSixSphere.Definitions
import Wikipedia.SmoothSixDPoincare.SphereBoundaryKernel

/-!
# The original tangent-kernel condition on a positively scaled sphere

Precomposition by the actual invertible scalar map transports the native
unit-sphere tangent-kernel theorem to radius `r`. The original sphere map
and its derivative are retained. The conclusion applies to a smooth
ambient extension fixing that map on the scaled sphere.
-/

noncomputable section

open Function
open scoped Manifold ContDiff RealInnerProductSpace

namespace NoExoticSixSphere

open GLOrthonormalization
open Wikipedia.SmoothSixDPoincare.SphereBoundary

theorem common_kernel_of_scaled_sphere_extension {p : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : Vector (p + 1) → F) (hG : ContDiff ℝ ∞ G)
    (r : ℝ) (hr : 0 < r) (f : Sphere p → F)
    (hext : ∀ q : Sphere p, G (r • q.val) = f q)
    (hi : ∀ q, Injective (mfderiv (𝓡 p) 𝓘(ℝ, F) f q))
    (q : Sphere p) (v : Vector (p + 1))
    (hgv : fderiv ℝ G (r • q.val) v = 0)
    (hnv : fderiv ℝ (definingFunction (E := Vector (p + 1))) (r • q.val) v = 0) : v = 0 := by
  let : Fact (Module.finrank ℝ (Vector (p + 1)) = p + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let L : Vector (p + 1) →L[ℝ] Vector (p + 1) :=
    r • ContinuousLinearMap.id ℝ (Vector (p + 1))
  let w := r⁻¹ • v
  have hwv : r • w = v := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hs : ContDiff ℝ ∞ (G ∘ L) := hG.comp L.contDiff
  have hk := common_kernel_of_immersive_sphere_extension hs.contMDiff hext hi
  have hc : fderiv ℝ (G ∘ L) q.val = (fderiv ℝ G (r • q.val)).comp L :=
    ((hG.differentiable (by simp) (r • q.val)).hasFDerivAt.comp q.val L.hasFDerivAt).fderiv
  have hinner : inner ℝ q.val v = 0 := by
    have h := (fderiv_definingFunction_eq_zero_iff (r • q.val) v).mp hnv
    rw [real_inner_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left hr.ne'
  have hnw : fderiv ℝ (definingFunction (E := Vector (p + 1))) q.val w = 0 := by
    apply (fderiv_definingFunction_eq_zero_iff q.val w).mpr
    change inner ℝ q.val (r⁻¹ • v) = 0
    rw [inner_smul_right, hinner, mul_zero]
  have hgw : mfderiv (𝓡 (p + 1)) 𝓘(ℝ, F) (G ∘ L) q.val w = 0 := by
    rw [mfderiv_eq_fderiv, hc]
    change fderiv ℝ G (r • q.val) (r • w) = 0
    rw [hwv]
    exact hgv
  have hw := hk q.val ((definingFunction_eq_zero_iff q.val).mpr q.property) w hgw hnw
  rw [hw, smul_zero] at hwv
  exact hwv.symm

end NoExoticSixSphere
