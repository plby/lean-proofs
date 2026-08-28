import Wikipedia.NoExoticSixSphere.SmoothTubularRetraction
import Wikipedia.NoExoticSixSphere.PartialFrames

/-!
# The actual tubular retraction is inverse to the embedding on tangent images

Differentiate the exact retraction identity in the original manifold atlas.
Its differential is a left inverse of the embedding differential, and the
reverse composition fixes every vector in the original tangent image.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.TubularRetraction

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M} (r : TubularRetraction e)

theorem mfderiv_comp_embedding (x : M) :
    (mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun x)).comp
      (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x) = ContinuousLinearMap.id ℝ (Vector n) := by
  have he : r.toFun ∘ e.toFun = id := funext r.fixes
  have hr := r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds (r.contains ⟨x, rfl⟩))
  have h := mfderiv_comp x (hr.mdifferentiableAt (by simp))
    (e.smooth.mdifferentiableAt (by simp))
  rw [he, mfderiv_id] at h
  exact h.symm

theorem mfderiv_embedding_retract_tangent (x : M) (v : Vector e.ambientDimension)
    (hv : v ∈ e.tangentImage x) :
    mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x
      (mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun x) v) = v := by
  obtain ⟨w, rfl⟩ := hv
  have h := congrArg (fun L : Vector n →L[ℝ] Vector n ↦ L w) (r.mfderiv_comp_embedding x)
  change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun x)
    (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x w) = w at h
  exact congrArg (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x) h

theorem injective_mfderiv_on_tangent (x : M) :
    InjOn (fun v : Vector e.ambientDimension ↦
      mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun x) v)
      (e.tangentImage x : Set (Vector e.ambientDimension)) := by
  intro v hv w hw he
  have h := congrArg (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x) he
  rw [r.mfderiv_embedding_retract_tangent x v hv,
    r.mfderiv_embedding_retract_tangent x w hw] at h
  exact h

end NoExoticSixSphere.EuclideanEmbedding.TubularRetraction
