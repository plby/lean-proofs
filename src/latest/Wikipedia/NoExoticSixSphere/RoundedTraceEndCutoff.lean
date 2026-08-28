import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryDefiningDifferential

/-!
# A smooth cutoff separating the actual two ends of the rounded trace

The complementary end is closed in the trace itself, not merely in its
boundary. Smooth separation supplies a function in `[0, 1]` that is locally
constant at both ends. It is not required to be a submersion in the interior.
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

def otherEnd : Set (ambientSet A) :=
  Subtype.val '' (otherBoundaryPart A : Set (Boundary A))

theorem mem_otherEnd_iff (p : ambientSet A) : letI := traceChartedSpace A;
    p ∈ otherEnd A ↔ (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p ∧
      p ∉ topEnd A := by
  let := traceChartedSpace A
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.property, (mem_otherBoundaryPart_iff A q).mp hq⟩
  · rintro ⟨hb, ht⟩
    exact ⟨⟨p, hb⟩, (mem_otherBoundaryPart_iff A ⟨p, hb⟩).mpr ht, rfl⟩

theorem isClosed_otherEnd : IsClosed (otherEnd A) :=
  (isClosed_nativeBoundary A).isClosedEmbedding_subtypeVal.isClosedMap _
    (isClosed_otherBoundaryPart A)

theorem disjoint_otherEnd_topEnd : Disjoint (otherEnd A) (topEnd A) := by
  rw [disjoint_left]
  intro p hp ht
  exact ((mem_otherEnd_iff A p).mp hp).2 ht

theorem boundary_iff_mem_ends (p : ambientSet A) : letI := traceChartedSpace A;
    (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p ↔
      p ∈ otherEnd A ∨ p ∈ topEnd A := by
  let := traceChartedSpace A
  rw [mem_otherEnd_iff, mem_topEnd_iff]
  tauto

theorem exists_endCutoff : letI := traceChartedSpace A;
    ∃ χ : C^∞⟮ProductHalfSpace.model (Vector 6), ambientSet A; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ᶠ p in 𝓝ˢ (otherEnd A), χ p = 0) ∧
      (∀ᶠ p in 𝓝ˢ (topEnd A), χ p = 1) ∧ ∀ p, χ p ∈ Icc 0 1 := by
  let := traceChartedSpace A
  let := trace_isManifold A
  let := isCompact_iff_compactSpace.mp (isCompact_ambientSet A)
  exact exists_contMDiffMap_zero_one_nhds_of_isClosed (ProductHalfSpace.model (Vector 6))
    (isClosed_otherEnd A) (isClosed_topEnd A) (disjoint_otherEnd_topEnd A)

def endCutoff : letI := traceChartedSpace A;
    C^∞⟮ProductHalfSpace.model (Vector 6), ambientSet A; 𝓘(ℝ, ℝ), ℝ⟯ :=
  Classical.choose (exists_endCutoff A)

theorem endCutoff_eventually_zero : letI := traceChartedSpace A;
    ∀ᶠ p in 𝓝ˢ (otherEnd A), endCutoff A p = 0 :=
  (Classical.choose_spec (exists_endCutoff A)).1

theorem endCutoff_eventually_one : letI := traceChartedSpace A;
    ∀ᶠ p in 𝓝ˢ (topEnd A), endCutoff A p = 1 :=
  (Classical.choose_spec (exists_endCutoff A)).2.1

theorem endCutoff_mem_Icc (p : ambientSet A) : letI := traceChartedSpace A;
    endCutoff A p ∈ Icc 0 1 :=
  (Classical.choose_spec (exists_endCutoff A)).2.2 p

theorem endCutoff_zero {p : ambientSet A} (hp : p ∈ otherEnd A) :
    letI := traceChartedSpace A; endCutoff A p = 0 :=
  (endCutoff_eventually_zero A).self_of_nhdsSet p hp

theorem endCutoff_one {p : ambientSet A} (hp : p ∈ topEnd A) :
    letI := traceChartedSpace A; endCutoff A p = 1 :=
  (endCutoff_eventually_one A).self_of_nhdsSet p hp

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
