import Wikipedia.NoExoticSixSphere.RoundedTraceGraphTimeTangent

/-!
# A smooth cutoff supported in the time-regular neighborhood

It equals one near the whole native boundary and vanishes on a neighborhood
of the complement of the regular set. The latter neighborhood condition is
needed to divide by the time speed without asserting interior regularity.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem exists_verticalFrameCutoff : letI := traceChartedSpace A;
    ∃ ρ : C^∞⟮ProductHalfSpace.model (Vector 6), ambientSet A; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ᶠ p in 𝓝ˢ (timeRegularNeighborhood A)ᶜ, ρ p = 0) ∧
      (∀ᶠ p in 𝓝ˢ (range (Subtype.val : Boundary A → ambientSet A)), ρ p = 1) ∧
      ∀ p, ρ p ∈ Icc 0 1 := by
  let := traceChartedSpace A
  let := trace_isManifold A
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  apply exists_contMDiffMap_zero_one_nhds_of_isClosed (ProductHalfSpace.model (Vector 6))
    (isOpen_timeRegularNeighborhood A).isClosed_compl
    (isClosed_nativeBoundary A).isClosedEmbedding_subtypeVal.isClosed_range
  rw [disjoint_left]
  rintro p hp ⟨q, rfl⟩
  exact hp (boundary_mem_timeRegularNeighborhood A q)

def verticalFrameCutoff : letI := traceChartedSpace A;
    C^∞⟮ProductHalfSpace.model (Vector 6), ambientSet A; 𝓘(ℝ, ℝ), ℝ⟯ :=
  Classical.choose (exists_verticalFrameCutoff A)

theorem verticalFrameCutoff_eventually_zero : letI := traceChartedSpace A;
    ∀ᶠ p in 𝓝ˢ (timeRegularNeighborhood A)ᶜ, verticalFrameCutoff A p = 0 :=
  (Classical.choose_spec (exists_verticalFrameCutoff A)).1

theorem verticalFrameCutoff_eventually_one : letI := traceChartedSpace A;
    ∀ᶠ p in 𝓝ˢ (range (Subtype.val : Boundary A → ambientSet A)), verticalFrameCutoff A p = 1 :=
  (Classical.choose_spec (exists_verticalFrameCutoff A)).2.1

theorem verticalFrameCutoff_mem_Icc (p : ambientSet A) : letI := traceChartedSpace A;
    verticalFrameCutoff A p ∈ Icc 0 1 :=
  (Classical.choose_spec (exists_verticalFrameCutoff A)).2.2 p

theorem verticalFrameCutoff_zero {p : ambientSet A} (hp : p ∉ timeRegularNeighborhood A) :
    letI := traceChartedSpace A; verticalFrameCutoff A p = 0 :=
  (verticalFrameCutoff_eventually_zero A).self_of_nhdsSet p hp

theorem verticalFrameCutoff_one_boundary (p : Boundary A) : letI := traceChartedSpace A;
    verticalFrameCutoff A p.val = 1 :=
  (verticalFrameCutoff_eventually_one A).self_of_nhdsSet p.val (mem_range_self p)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
