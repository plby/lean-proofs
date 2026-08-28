import Wikipedia.NoExoticSixSphere.RoundedTraceBordismTimeDifferential

/-!
# Native boundary tangent spaces are the kernels of the end time differential

The native boundary atlas is retained. Differentiating the identically zero
boundary equation gives one inclusion, and injectivity and rank-nullity give
equality. The actual time differential has exactly the same kernel.
-/

noncomputable section

open Function Set Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryTraceDifferential (p : Boundary A) : Vector 6 →L[ℝ] (ℝ × Vector 6) :=
  letI := traceChartedSpace A
  letI := boundaryChartedSpace A
  mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
    (Subtype.val : Boundary A → ambientSet A) p

theorem injective_boundaryTraceDifferential (p : Boundary A) :
    Injective (boundaryTraceDifferential A p) :=
  injective_mfderiv_boundaryInclusion A p

theorem boundaryDefiningDifferential_comp_boundary (p : Boundary A) :
    (boundaryDefiningDifferential A p.val).comp (boundaryTraceDifferential A p) = 0 := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  have hd := mvfderiv_comp p
    ((contMDiff_boundaryDefiningFunction A).mdifferentiableAt (by simp))
    ((contMDiff_boundaryInclusion A).mdifferentiableAt (by simp))
  have he : boundaryDefiningFunction A ∘ (Subtype.val : Boundary A → ambientSet A) =
      (fun _ ↦ (0 : ℝ)) := by
    funext q
    exact (boundaryDefiningFunction_zero_iff A q.val).mpr q.property
  rw [he, mvfderiv_const] at hd
  exact hd.symm

theorem range_boundaryTraceDifferential (p : Boundary A) :
    (boundaryTraceDifferential A p).range = (boundaryDefiningDifferential A p.val).ker := by
  have hle : (boundaryTraceDifferential A p).range ≤
      (boundaryDefiningDifferential A p.val).ker := by
    rintro v ⟨w, rfl⟩
    exact congrArg (fun D : Vector 6 →L[ℝ] ℝ ↦ D w)
      (boundaryDefiningDifferential_comp_boundary A p)
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (injective_boundaryTraceDifferential A p)]
  exact (finrank_kernel_of_surjective (boundaryDefiningDifferential A p.val)
    (boundaryDefiningDifferential_surjective A p) (finrank ℝ (Vector 6))
    (by simp [finrank_prod])).symm

theorem range_boundaryTraceDifferential_time (p : Boundary A) :
    (boundaryTraceDifferential A p).range = (bordismTimeDifferential A p.val).ker := by
  rw [range_boundaryTraceDifferential]
  rcases (boundary_iff_mem_ends A p.val).mp p.property with hp | hp
  · rw [bordismTimeDifferential_otherEnd A p hp]
  · rw [bordismTimeDifferential_topEnd A p hp]
    ext v
    change boundaryDefiningDifferential A p.val v = 0 ↔
      -(boundaryDefiningDifferential A p.val v) = 0
    exact neg_eq_zero.symm

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
