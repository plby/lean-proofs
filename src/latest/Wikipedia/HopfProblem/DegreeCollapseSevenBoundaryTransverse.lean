import Wikipedia.HopfProblem.DegreeCollapseSevenSphereNormalSpace
import Wikipedia.NoExoticSixSphere.SpanningDiskBoundaryComplement
import Wikipedia.NoExoticSixSphere.EuclideanBlockProjection

/-!
# The four transverse columns are the original internal normal frame

The actual retained disk collar identifies the boundary complement. Equality
of the computed dimensions proves that every transverse vector lies in the
old ambient coordinates and in the seven-manifold tangent image. Projection
loses no norm and gives the full four-dimensional internal normal frame.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalFramedProduct.FramedProduct

open NoExoticSixSphere GLOrthonormalization

variable {N k : ℕ} {D : Vector 4 → Vector (N + 6)}
  {T : Vector 4 → Vector k →L[ℝ] Vector (N + 6)} (A : FramedProduct D T)

def boundaryTransverse (s : Sphere 3) : Vector 4 →L[ℝ] Vector N :=
  (oldProjection N 6).comp (A.transverse s.val)

theorem contMDiff_transverse_boundary :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector (N + 6)) ∞
      (fun s : Sphere 3 ↦ A.transverse s.val) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  intro s
  exact (A.smooth_transverse s.val (Metric.sphere_subset_closedBall s.property)).contMDiffAt.comp
    s hs.contMDiffAt

theorem contMDiff_boundaryTransverse :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector N) ∞ A.boundaryTransverse := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  intro s
  exact contMDiffAt_const.clm_comp
    ((A.smooth_transverse s.val (Metric.sphere_subset_closedBall s.property)).contMDiffAt.comp
      s hs.contMDiffAt)

end Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalFramedProduct.FramedProduct

noncomputable section

open Function Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3,
    T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include hf hd hTb in
theorem transverse_range_boundary (s : Sphere 3) :
    (A.transverse s.val).range = (SevenSurgery.sphereNormalSpace e f s).map
      (appendZeroMap e.ambientDimension 6).toLinearMap := by
  have hW : SevenSurgery.sphereNormalSpace e f s = (SevenSurgery.normalFrameOnSphere e a f s).val.rangeᗮ ⊓
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
    rw [SevenSurgery.normalFrameOnSphere_range e a f s]
    change SevenSurgery.sphereNormalSpace e f s = (e.tangentImage (f s))ᗮᗮ ⊓ _
    rw [Submodule.orthogonal_orthogonal]
    rfl
  have hle : (SevenSurgery.sphereNormalSpace e f s).map
      (appendZeroMap e.ambientDimension 6).toLinearMap ≤ (A.transverse s.val).range := by
    rw [A.range_transverse s.val (sphere_subset_closedBall s.property), hTb s, hW]
    exact D.map_normal_le_combined_orthogonal (e.smooth.comp hf) s
      (SevenSurgery.normalFrameOnSphere e a f s).val
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← (Submodule.equivMapOfInjective (appendZeroMap e.ambientDimension 6).toLinearMap
    (appendZeroMap_injective e.ambientDimension 6) (SevenSurgery.sphereNormalSpace e f s)).finrank_eq,
    SevenSurgery.finrank_sphereNormalSpace e f hf hd s,
    LinearMap.finrank_range_of_inj (Stiefel.injective
      ⟨A.transverse s.val, A.norm_transverse s.val (sphere_subset_closedBall s.property)⟩),
    finrank_euclideanSpace_fin]

include hf hd hTb in
theorem append_boundaryTransverse (s : Sphere 3) (v : Vector 4) :
    appendZeroMap e.ambientDimension 6 (A.boundaryTransverse s v) = A.transverse s.val v := by
  apply appendZeroMap_oldProjection
  have h : A.transverse s.val v ∈ (SevenSurgery.sphereNormalSpace e f s).map
      (appendZeroMap e.ambientDimension 6).toLinearMap := by
    rw [← SevenSurgery.transverse_range_boundary e a f hf hd D A hTb s]
    exact ⟨v, rfl⟩
  obtain ⟨w, _, hw⟩ := h
  exact ⟨w, hw⟩

include hf hd hTb in
theorem norm_boundaryTransverse (s : Sphere 3) (v : Vector 4) :
    ‖A.boundaryTransverse s v‖ = ‖v‖ := by
  calc
    ‖A.boundaryTransverse s v‖ =
        ‖appendZeroMap e.ambientDimension 6 (A.boundaryTransverse s v)‖ :=
      (norm_appendZeroMap e.ambientDimension 6 _).symm
    _ = ‖A.transverse s.val v‖ :=
      congrArg norm (SevenSurgery.append_boundaryTransverse e a f hf hd D A hTb s v)
    _ = ‖v‖ := A.norm_transverse s.val (sphere_subset_closedBall s.property) v

include hf hd hTb in
theorem range_boundaryTransverse (s : Sphere 3) :
    (A.boundaryTransverse s).range = SevenSurgery.sphereNormalSpace e f s := by
  change LinearMap.range ((oldProjection e.ambientDimension 6).toLinearMap.comp
    (A.transverse s.val).toLinearMap) = _
  rw [LinearMap.range_comp, SevenSurgery.transverse_range_boundary e a f hf hd D A hTb s,
    ← Submodule.map_comp]
  have he : (oldProjection e.ambientDimension 6).toLinearMap.comp
      (appendZeroMap e.ambientDimension 6).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact oldProjection_appendZeroMap e.ambientDimension 6 v
  rw [he, Submodule.map_id]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
