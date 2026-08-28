import Wikipedia.HopfProblem.DegreeCollapseLowSphereNormalSpace
import Wikipedia.HopfProblem.DegreeCollapseLowSpanningDiskComplement
import Wikipedia.HopfProblem.DegreeCollapseLowTransverseCollar
import Wikipedia.NoExoticSixSphere.EuclideanBlockProjection

/-!

# Boundary transverse columns are the original internal normal directions

The actual low-dimensional disk collar identifies the whole boundary
complement. Its rank is 7-d. Every transverse column lies in the original
ambient coordinates, and projection gives a full isometric frame for the
internal normal space in the original seven-manifold tangent image.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowFramedProduct.FramedProduct

open NoExoticSixSphere GLOrthonormalization

variable {d N k q : ℕ} {D : Vector (d + 1) → Vector (N + (1 + (1 + (d + 1))))}
  {T : Vector (d + 1) → Vector k →L[ℝ] Vector (N + (1 + (1 + (d + 1))))}
  (A : FramedProduct (q := q) D T)

def boundaryTransverse (s : NoExoticSixSphere.Sphere d) : Vector q →L[ℝ] Vector N :=
  (oldProjection N (1 + (1 + (d + 1)))).comp (A.transverse s.val)

theorem contMDiff_boundaryTransverse :
    ContMDiff (𝓡 d) 𝓘(ℝ, Vector q →L[ℝ] Vector N) ∞ A.boundaryTransverse :=
  contMDiff_const.clm_comp A.contMDiff_transverse_boundary

end Wikipedia.HopfProblem.DegreeCollapse.LowFramedProduct.FramedProduct

open Function Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere d → M) (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  {b : NoExoticSixSphere.Sphere d}
  (D : FramedDisk b (e.toFun ∘ f) (fun s => a.orthonormal (f s)))
  (A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame)

include hf hd in
theorem transverse_range_boundary (s : NoExoticSixSphere.Sphere d) :
    (A.transverse s.val).range = (sphereNormalSpace e f s).map
      (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))).toLinearMap := by
  have hW : sphereNormalSpace e f s = (a.orthonormal (f s)).val.rangeᗮ ⊓
      (mfderiv (𝓡 d) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
    rw [a.orthonormal_range, e.range_normalProjection]
    change sphereNormalSpace e f s = (e.tangentImage (f s))ᗮᗮ ⊓ _
    rw [Submodule.orthogonal_orthogonal]
    rfl
  have hle : (sphereNormalSpace e f s).map
      (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))).toLinearMap ≤
        (A.transverse s.val).range := by
    rw [A.range_transverse s.val (sphere_subset_closedBall s.property),
      D.frame_boundary s, hW]
    exact D.map_normal_le_combined_orthogonal (e.smooth.comp hf) s
      (a.orthonormal (f s)).val
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← (Submodule.equivMapOfInjective
    (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))).toLinearMap
    (appendZeroMap_injective e.ambientDimension (1 + (1 + (d + 1))))
    (sphereNormalSpace e f s)).finrank_eq,
    finrank_sphereNormalSpace e f hf hd s,
    LinearMap.finrank_range_of_inj (Stiefel.injective
      ⟨A.transverse s.val, A.norm_transverse s.val (sphere_subset_closedBall s.property)⟩),
    finrank_euclideanSpace_fin]

include hf hd in
theorem append_boundaryTransverse (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d)) :
    appendZeroMap e.ambientDimension (1 + (1 + (d + 1))) (A.boundaryTransverse s v) =
      A.transverse s.val v := by
  apply appendZeroMap_oldProjection
  have h : A.transverse s.val v ∈ (sphereNormalSpace e f s).map
      (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))).toLinearMap := by
    rw [← transverse_range_boundary e a f hf hd D A s]
    exact ⟨v, rfl⟩
  obtain ⟨w, _, hw⟩ := h
  exact ⟨w, hw⟩

include hf hd in
theorem norm_boundaryTransverse (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d)) :
    ‖A.boundaryTransverse s v‖ = ‖v‖ := by
  calc
    ‖A.boundaryTransverse s v‖ =
        ‖appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
          (A.boundaryTransverse s v)‖ :=
      (norm_appendZeroMap e.ambientDimension (1 + (1 + (d + 1))) _).symm
    _ = ‖A.transverse s.val v‖ :=
      congrArg norm (append_boundaryTransverse e a f hf hd D A s v)
    _ = ‖v‖ := A.norm_transverse s.val (sphere_subset_closedBall s.property) v

include hf hd in
theorem range_boundaryTransverse (s : NoExoticSixSphere.Sphere d) :
    (A.boundaryTransverse s).range = sphereNormalSpace e f s := by
  change LinearMap.range
    ((oldProjection e.ambientDimension (1 + (1 + (d + 1)))).toLinearMap.comp
      (A.transverse s.val).toLinearMap) = _
  rw [LinearMap.range_comp, transverse_range_boundary e a f hf hd D A s,
    ← Submodule.map_comp]
  have he : (oldProjection e.ambientDimension (1 + (1 + (d + 1)))).toLinearMap.comp
      (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact oldProjection_appendZeroMap e.ambientDimension (1 + (1 + (d + 1))) v
  rw [he, Submodule.map_id]

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
