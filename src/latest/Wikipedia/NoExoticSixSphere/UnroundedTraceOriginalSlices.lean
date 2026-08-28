import Wikipedia.NoExoticSixSphere.UnroundedTraceFrame

/-!
# Original slices retained in the actual unrounded attachment

Every height slice of the original cylinder is closed embedded in the
actual ambient union. Positive-height slices miss the handle. The descended
trace columns on each slice are exactly the original normal frame and five
graph axes. These are trace columns, not yet the full induced boundary frame.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnroundedTrace

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def cylinderSlice (t : Icc (0 : ℝ) (height A)) : C(M, ambientSet A) where
  toFun := fun m ↦ ⟨e.heightCylinder (m, t.val), Or.inl ⟨(m, t), rfl⟩⟩
  continuous_toFun := (e.isClosedEmbedding_heightSlice t.val).continuous.subtype_mk _

theorem closedEmbedding_cylinderSlice (t : Icc (0 : ℝ) (height A)) :
    IsClosedEmbedding (cylinderSlice A t) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (cylinderSlice A t).continuous ?_ ?_
  · intro x y he
    exact (e.isClosedEmbedding_heightSlice t.val).injective (congrArg Subtype.val he)
  · exact (e.isClosedEmbedding_heightSlice t.val).isClosedMap.subtype_mk _

theorem cylinderSlice_not_mem_handle (t : Icc (0 : ℝ) (height A)) (ht : 0 < t.val) (m : M) :
    (cylinderSlice A t m).val ∉ range (handleMap A) := by
  rintro ⟨p, he⟩
  obtain ⟨s, _, _, ht0⟩ :=
    (intersection_iff A p.1.property (handle_vector_mem A p) m t.property).mp he
  exact (ne_of_gt ht) ht0

theorem columns_cylinderSlice (t : Icc (0 : ℝ) (height A)) (m : M) :
    columns A (cylinderSlice A t m) = boundaryFrameOperator (a.orthonormal m).val :=
  columns_cylinder A (m, t)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnroundedTrace
