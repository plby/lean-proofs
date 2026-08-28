import Wikipedia.NoExoticSixSphere.TubularRetractionDifferential
import Wikipedia.NoExoticSixSphere.NormalFrameOfEquations

/-!
# The intrinsic ambient gradient of a smooth time on an embedded manifold

Extend the time through an actual tubular retraction and project its
ambient gradient onto the original tangent image. The resulting vector
field is smooth, represents the native time differential, and is independent
of the chosen retraction. It is nonzero at every regular point.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] (e : EuclideanEmbedding n M)
  (r : e.TubularRetraction) (t : M → ℝ)

def embeddingDerivative (x : M) : Vector n →L[ℝ] Vector e.ambientDimension :=
  mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x

def timeDerivative (x : M) : Vector n →L[ℝ] ℝ := mfderiv (𝓡 n) 𝓘(ℝ, ℝ) t x

def extension : Vector e.ambientDimension → ℝ := t ∘ r.toFun

theorem extension_embedding (x : M) : extension e r t (e.toFun x) = t x := by
  change t (r.toFun (e.toFun x)) = t x
  rw [r.fixes]

theorem contDiffAt_extension (ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t) (x : M) :
    ContDiffAt ℝ ∞ (extension e r t) (e.toFun x) := by
  have hr := r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds (r.contains ⟨x, rfl⟩))
  exact ((ht (r.toFun (e.toFun x))).comp (e.toFun x) hr).contDiffAt

theorem extension_differential_tangent (ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t)
    (x : M) (v : Vector n) :
    fderiv ℝ (extension e r t) (e.toFun x)
        (embeddingDerivative e x v) = timeDerivative (n := n) t x v := by
  have he : extension e r t ∘ e.toFun = t := funext (extension_embedding e r t)
  have hc := mfderiv_comp x
    ((contDiffAt_extension e r t ht x).differentiableAt (by simp)).mdifferentiableAt
    (e.smooth.mdifferentiableAt (by simp))
  rw [he, mfderiv_eq_fderiv] at hc
  exact congrArg (fun L : Vector n →L[ℝ] ℝ ↦ L v) hc.symm

def gradient (x : M) : Vector e.ambientDimension :=
  e.tangentProjection x ((fderiv ℝ (extension e r t) (e.toFun x)).adjoint 1)

theorem gradient_mem_tangent (x : M) : gradient e r t x ∈ e.tangentImage x :=
  (e.tangentImage x).starProjection_apply_mem _

theorem inner_gradient_tangent (x : M) (v : Vector e.ambientDimension)
    (hv : v ∈ e.tangentImage x) :
    inner ℝ (gradient e r t x) v = fderiv ℝ (extension e r t) (e.toFun x) v := by
  have h := (e.tangentImage x).starProjection_inner_eq_zero
    ((fderiv ℝ (extension e r t) (e.toFun x)).adjoint 1) v hv
  rw [inner_sub_left] at h
  simpa only [gradient, EuclideanEmbedding.tangentProjection,
    ContinuousLinearMap.adjoint_inner_left, Real.inner_apply, mul_one, one_mul]
    using (sub_eq_zero.mp h).symm

theorem inner_gradient_native (ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t)
    (x : M) (v : Vector n) :
    inner ℝ (gradient e r t x) (embeddingDerivative e x v) =
      timeDerivative (n := n) t x v :=
  (inner_gradient_tangent e r t x _ ⟨v, rfl⟩).trans
    (extension_differential_tangent e r t ht x v)

theorem gradient_ne_zero (ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t) (x : M)
    (hreg : Surjective (timeDerivative (n := n) t x)) : gradient e r t x ≠ 0 := by
  obtain ⟨v, hv⟩ := hreg 1
  intro hz
  have h := inner_gradient_native e r t ht x v
  rw [hz, inner_zero_left, hv] at h
  exact zero_ne_one h

theorem contMDiff_gradient (ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t) :
    ContMDiff (𝓡 n) (𝓡 e.ambientDimension) ∞ (gradient e r t) := by
  have hd : ContMDiff (𝓡 n) 𝓘(ℝ, Vector e.ambientDimension →L[ℝ] ℝ) ∞
      (fun x ↦ fderiv ℝ (extension e r t) (e.toFun x)) :=
    NormalFrameOfEquations.contMDiff_equationDifferential e.smooth
      (contDiffAt_extension e r t ht)
  have ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ →L[ℝ] Vector e.ambientDimension) ∞
      (fun x ↦ (fderiv ℝ (extension e r t) (e.toFun x)).adjoint) :=
    realAdjoint.contDiff.contMDiff.comp hd
  exact e.contMDiff_tangentProjection.clm_apply (ha.clm_apply contMDiff_const)

theorem gradient_unique (ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t) (x : M)
    (g : Vector e.ambientDimension) (hg : g ∈ e.tangentImage x)
    (hpair : ∀ v : Vector n,
      inner ℝ g (embeddingDerivative e x v) = timeDerivative (n := n) t x v) :
    g = gradient e r t x := by
  have hm : g - gradient e r t x ∈ (embeddingDerivative e x).range :=
    (e.tangentImage x).sub_mem hg (gradient_mem_tangent e r t x)
  obtain ⟨v, hv⟩ := hm
  have hz : inner ℝ (g - gradient e r t x) (g - gradient e r t x) = 0 := by
    calc
      _ = inner ℝ (g - gradient e r t x) (embeddingDerivative e x v) :=
        congrArg (inner ℝ (g - gradient e r t x)) hv.symm
      _ = 0 := by rw [inner_sub_left, hpair, inner_gradient_native e r t ht, sub_self]
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hz)

theorem gradient_retraction_independent (r' : e.TubularRetraction)
    (ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t) (x : M) :
    gradient e r' t x = gradient e r t x :=
  gradient_unique e r t ht x (gradient e r' t x) (gradient_mem_tangent e r' t x)
    (inner_gradient_native e r' t ht x)

end NoExoticSixSphere.EmbeddedTime
