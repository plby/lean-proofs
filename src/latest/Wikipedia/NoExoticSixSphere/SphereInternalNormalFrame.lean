import Wikipedia.NoExoticSixSphere.SphereThreeProjectionFrame
import Wikipedia.NoExoticSixSphere.SphereInternalNormalSpace
import Wikipedia.NoExoticSixSphere.SmoothRangeOrthonormalization

/-!
# Internal normal three-frames without a parity assumption

For an actual smooth immersed three-sphere in a normally framed smooth
six-manifold, the internal normal projection is smooth and has rank three.
The proved sphere projection-frame theorem gives its global smooth frame.
Gram--Schmidt makes that frame orthonormal with exactly the original range.
Neither global injectivity nor a spanning disk is required.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (f : Sphere 3 → M)

def internalSphereNormalProjection (s : Sphere 3) :
    Vector e.ambientDimension →L[ℝ] Vector e.ambientDimension :=
  (e.sphereNormalSpace f s).starProjection

theorem range_internalSphereNormalProjection (s : Sphere 3) :
    (e.internalSphereNormalProjection f s).range = e.sphereNormalSpace f s :=
  (e.sphereNormalSpace f s).range_starProjection

theorem idempotent_internalSphereNormalProjection (s : Sphere 3) :
    IsIdempotentElem (e.internalSphereNormalProjection f s) :=
  (e.sphereNormalSpace f s).isIdempotentElem_starProjection

variable (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

include hf hd in
theorem internalSphereNormalProjection_eq_gramComplement (s : Sphere 3) :
    e.internalSphereNormalProjection f s = 1 - gramProjection (e.sphereFrameOperator a f s) := by
  simp only [internalSphereNormalProjection, e.sphereNormalSpace_eq_frameComplement f a hf s,
    gramProjection_eq_starProjection _ (e.injective_sphereFrameOperator a f hf hd s),
    Submodule.starProjection_orthogonal']

include a hf hd in
theorem contMDiff_internalSphereNormalProjection :
    ContMDiff (𝓡 3)
      𝓘(ℝ, Vector e.ambientDimension →L[ℝ] Vector e.ambientDimension) ∞
      (e.internalSphereNormalProjection f) := by
  have he : e.internalSphereNormalProjection f =
      fun s ↦ 1 - gramProjection (e.sphereFrameOperator a f s) :=
    funext (e.internalSphereNormalProjection_eq_gramComplement f a hf hd)
  rw [he]
  intro s
  exact contMDiffAt_const.sub (contMDiffAt_gramProjection
    (e.contMDiff_sphereFrameOperator a f hf).contMDiffAt
    (e.injective_sphereFrameOperator a f hf hd s))

include a hf hd in
theorem exists_smooth_internalNormalFrame :
    ∃ C : Sphere 3 → Vector 3 →L[ℝ] Vector e.ambientDimension,
      ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ C ∧
      (∀ s w, ‖C s w‖ = ‖w‖) ∧ ∀ s, (C s).range = e.sphereNormalSpace f s := by
  obtain ⟨b⟩ := SphereThreeProjection.nonempty_smoothFrame
    (e.internalSphereNormalProjection f) (e.idempotent_internalSphereNormalProjection f)
    (e.contMDiff_internalSphereNormalProjection f a hf hd) (fun s ↦ by
      rw [e.range_internalSphereNormalProjection]
      exact e.finrank_sphereNormalSpace f a hf hd s)
  refine ⟨fun s ↦ (b.orthonormal s).val, b.contMDiff_orthonormal, fun s ↦ ?_, fun s ↦ ?_⟩
  · exact (b.orthonormal s).property
  · exact (b.orthonormal_range s).trans (e.range_internalSphereNormalProjection f s)

end NoExoticSixSphere.EuclideanEmbedding
