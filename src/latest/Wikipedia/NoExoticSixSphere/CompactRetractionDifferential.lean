import Wikipedia.NoExoticSixSphere.CompactTubularRetraction
import Wikipedia.NoExoticSixSphere.PartialFrames

/-!
# Differential identities for a retraction near a compact subset

The retraction fixes an actual open base neighborhood. Differentiating that
local identity gives the tangent inverse identities at every point of the
base. Compactness of the entire ambient manifold is not needed.
-/

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.RetractionNear

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M} {K : Set M} (r : e.RetractionNear K)

theorem mfderiv_comp_embedding (x : M) (hx : x ∈ r.base) :
    (mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun x)).comp
      (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x) =
        ContinuousLinearMap.id ℝ (Vector n) := by
  have he : r.toFun ∘ e.toFun =ᶠ[𝓝 x] id :=
    Filter.mem_of_superset (r.base.isOpen.mem_nhds hx) (fun y hy ↦ r.fixes y hy)
  have hr := r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds (r.contains ⟨x, hx, rfl⟩))
  have h := mfderiv_comp x (hr.mdifferentiableAt (by simp))
    (e.smooth.mdifferentiableAt (by simp))
  rw [he.mfderiv_eq, mfderiv_id] at h
  exact h.symm

theorem mfderiv_embedding_retract_tangent (x : M) (hx : x ∈ r.base)
    (v : Vector e.ambientDimension) (hv : v ∈ e.tangentImage x) :
    mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x
      (mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun x) v) = v := by
  obtain ⟨w, rfl⟩ := hv
  have h := congrArg (fun L : Vector n →L[ℝ] Vector n ↦ L w) (r.mfderiv_comp_embedding x hx)
  change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun x)
    (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x w) = w at h
  exact congrArg (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x) h

theorem injective_mfderiv_on_tangent (x : M) (hx : x ∈ r.base) :
    InjOn (fun v : Vector e.ambientDimension ↦
      mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun x) v)
      (e.tangentImage x : Set (Vector e.ambientDimension)) := by
  intro v hv w hw he
  have h := congrArg (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x) he
  rw [r.mfderiv_embedding_retract_tangent x hx v hv,
    r.mfderiv_embedding_retract_tangent x hx w hw] at h
  exact h

end NoExoticSixSphere.EuclideanEmbedding.RetractionNear
