import Wikipedia.NoExoticSixSphere.SphereInternalNormalSpace
import Wikipedia.NoExoticSixSphere.SpanningDiskBoundaryComplement
import Wikipedia.NoExoticSixSphere.BoundaryTransverseOperator

/-!
# The constructed transverse frame lies in the original manifold

The boundary transverse space is exactly the stabilized internal normal space
of the original sphere in the original six-manifold. The proof retains the
actual collar derivative and boundary normal columns, then uses the proved
three-dimensional ranks. Projection to the old ambient coordinates therefore
loses no vector or norm and gives a smooth full internal normal frame.
-/

noncomputable section

open Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val)

include hf hd hTb in
theorem transverse_range_boundary (s : Sphere 3) :
    (A.transverse s.val).range = (e.sphereNormalSpace f s).map
      (appendZeroMap e.ambientDimension 6).toLinearMap := by
  have hW : e.sphereNormalSpace f s = (e.normalFrameOnSphere a f s).val.rangeᗮ ⊓
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
    rw [e.normalFrameOnSphere_range a f s]
    change e.sphereNormalSpace f s = (e.tangentImage (f s))ᗮᗮ ⊓ _
    rw [Submodule.orthogonal_orthogonal]
    rfl
  have hle : (e.sphereNormalSpace f s).map
      (appendZeroMap e.ambientDimension 6).toLinearMap ≤ (A.transverse s.val).range := by
    rw [A.range_transverse s.val (sphere_subset_closedBall s.property), hTb s, hW]
    exact D.map_normal_le_combined_orthogonal (e.smooth.comp hf) s
      (e.normalFrameOnSphere a f s).val
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← (Submodule.equivMapOfInjective (appendZeroMap e.ambientDimension 6).toLinearMap
    (appendZeroMap_injective e.ambientDimension 6) (e.sphereNormalSpace f s)).finrank_eq,
    e.finrank_sphereNormalSpace f a hf hd s,
    LinearMap.finrank_range_of_inj (Stiefel.injective
      ⟨A.transverse s.val, A.norm_transverse s.val (sphere_subset_closedBall s.property)⟩),
    finrank_euclideanSpace_fin]

include hf hd hTb in
theorem append_boundaryTransverse (s : Sphere 3) (v : Vector 3) :
    appendZeroMap e.ambientDimension 6 (A.boundaryTransverse s v) = A.transverse s.val v := by
  apply appendZeroMap_oldProjection
  have h : A.transverse s.val v ∈ (e.sphereNormalSpace f s).map
      (appendZeroMap e.ambientDimension 6).toLinearMap := by
    rw [← e.transverse_range_boundary a f hf hd D A hTb s]
    exact ⟨v, rfl⟩
  obtain ⟨w, _, hw⟩ := h
  exact ⟨w, hw⟩

include hf hd hTb in
theorem norm_boundaryTransverse (s : Sphere 3) (v : Vector 3) :
    ‖A.boundaryTransverse s v‖ = ‖v‖ := by
  calc
    ‖A.boundaryTransverse s v‖ =
        ‖appendZeroMap e.ambientDimension 6 (A.boundaryTransverse s v)‖ :=
      (norm_appendZeroMap e.ambientDimension 6 _).symm
    _ = ‖A.transverse s.val v‖ := congrArg norm (e.append_boundaryTransverse a f hf hd D A hTb s v)
    _ = ‖v‖ := A.norm_transverse s.val (sphere_subset_closedBall s.property) v

include hf hd hTb in
theorem range_boundaryTransverse (s : Sphere 3) :
    (A.boundaryTransverse s).range = e.sphereNormalSpace f s := by
  change LinearMap.range ((oldProjection e.ambientDimension 6).toLinearMap.comp
    (A.transverse s.val).toLinearMap) = _
  rw [LinearMap.range_comp, e.transverse_range_boundary a f hf hd D A hTb s,
    ← Submodule.map_comp]
  have he : (oldProjection e.ambientDimension 6).toLinearMap.comp
      (appendZeroMap e.ambientDimension 6).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact oldProjection_appendZeroMap e.ambientDimension 6 v
  rw [he, Submodule.map_id]

end NoExoticSixSphere.EuclideanEmbedding
