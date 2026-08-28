import Wikipedia.NoExoticSixSphere.RoundedTraceNormalFrame

/-!
# The unchanged original end of the rounded attachment

Positive-time cylinder points meet neither the handle nor the added rounding
region. In particular, the top endpoint is a closed embedded copy of the
original manifold in the unchanged cylinder piece, with exact coordinates.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem positive_height_avoids_handle (m : M) {t : ℝ} (ht : 0 < t)
    (hT : t ≤ UnroundedTrace.height A) :
    e.heightCylinder (m, t) ∉ range (UnroundedTrace.handleMap A) := by
  rintro ⟨p, hp⟩
  obtain ⟨_, _, _, hz⟩ := (UnroundedTrace.intersection_iff A p.1.property
    (UnroundedTrace.handle_vector_mem A p) m ⟨ht.le, hT⟩).mp hp
  exact (ne_of_gt ht) hz

theorem positive_height_avoids_added (m : M) {t : ℝ} (ht : 0 < t) :
    e.heightCylinder (m, t) ∉ A.collarSheet '' addedParameters A := by
  rintro ⟨p, hp, he⟩
  have h := congrArg (Prod.snd : M × ℝ → ℝ) (e.injective_heightCylinder he)
  change p.2 = t at h
  have hn : p.2 ≤ 0 := hp.2.1.2
  rw [h] at hn
  exact (not_lt_of_ge hn) ht

def topMap : C(M, ambientSet A) :=
  ⟨fun m ↦ ⟨e.heightCylinder (m, UnroundedTrace.height A),
      unrounded_subset A (Or.inl
        ⟨(m, ⟨UnroundedTrace.height A, (UnroundedTrace.height_pos A).le, le_rfl⟩), rfl⟩)⟩,
    (e.continuous_heightCylinder.comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩

theorem topMap_ambient (m : M) : (topMap A m).val =
    e.heightCylinder (m, UnroundedTrace.height A) := rfl

theorem topMap_mem_cylinderOnly (m : M) : topMap A m ∈ cylinderOnlyPart A := by
  intro h
  exact h.elim (positive_height_avoids_handle A m (UnroundedTrace.height_pos A) le_rfl)
    (positive_height_avoids_added A m (UnroundedTrace.height_pos A))

def topLift (m : M) : cylinderOnlyPart A := ⟨topMap A m, topMap_mem_cylinderOnly A m⟩

theorem topLift_coordinates (m : M) :
    (unchangedCylinderHomeomorph A (topLift A m)).val.val = (m, UnroundedTrace.height A) := by
  apply e.injective_heightCylinder
  exact unchangedCylinderHomeomorph_ambient A (topLift A m)

theorem isEmbedding_topMap : IsEmbedding (topMap A) := by
  have he : IsEmbedding (fun m : M ↦ e.heightCylinder (m, UnroundedTrace.height A)) :=
    e.isEmbedding_heightCylinder.comp (isEmbedding_prodMkLeft _)
  exact he.codRestrict (ambientSet A) (fun m ↦ (topMap A m).property)

theorem isClosedEmbedding_topMap : IsClosedEmbedding (topMap A) :=
  (topMap A).continuous.isClosedEmbedding (isEmbedding_topMap A).injective

def topEnd : Set (ambientSet A) := range (topMap A)

theorem isClosed_topEnd : IsClosed (topEnd A) := (isClosedEmbedding_topMap A).isClosed_range

def topEndHomeomorph : M ≃ₜ topEnd A := (isEmbedding_topMap A).toHomeomorph

theorem topEndHomeomorph_val (m : M) : (topEndHomeomorph A m).val = topMap A m := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
