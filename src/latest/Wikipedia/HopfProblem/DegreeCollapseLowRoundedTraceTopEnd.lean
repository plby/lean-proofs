import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceNormalFrame

/-!

# The unchanged original end of the rounded attachment

Positive-time cylinder points meet neither the handle nor the added rounding
region. In particular, the top endpoint is a closed embedded copy of the
original manifold in the unchanged cylinder piece, with exact coordinates.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem positive_height_avoids_handle (m : M) {t : ℝ} (ht : 0 < t)
    (hT : t ≤ UnroundedTrace.height A) :
    (LowHeightCylinder.heightCylinder d e) (m, t) ∉ range (UnroundedTrace.handleMap A) := by
  rintro ⟨p, hp⟩
  obtain ⟨_, _, _, hz⟩ := (UnroundedTrace.intersection_iff A p.1.property
    (UnroundedTrace.handle_vector_mem A p) m ⟨ht.le, hT⟩).mp hp
  exact (ne_of_gt ht) hz

theorem positive_height_avoids_added (m : M) {t : ℝ} (ht : 0 < t) :
    (LowHeightCylinder.heightCylinder d e) (m, t) ∉ A.collarSheet '' addedParameters A := by
  rintro ⟨p, hp, he⟩
  have h := congrArg (Prod.snd : M × ℝ → ℝ) ((LowHeightCylinder.injective_heightCylinder d e) he)
  change p.2 = t at h
  have hn : p.2 ≤ 0 := hp.2.1.2
  rw [h] at hn
  exact (not_lt_of_ge hn) ht

def topMap : C(M, ambientSet A) :=
  ⟨fun m ↦ ⟨(LowHeightCylinder.heightCylinder d e) (m, UnroundedTrace.height A),
      unrounded_subset A (Or.inl
        ⟨(m, ⟨UnroundedTrace.height A, (UnroundedTrace.height_pos A).le, le_rfl⟩), rfl⟩)⟩,
    ((LowHeightCylinder.continuous_heightCylinder d e).comp
      (continuous_id.prodMk continuous_const)).subtype_mk _⟩

theorem topMap_ambient (m : M) : (topMap A m).val =
    (LowHeightCylinder.heightCylinder d e) (m, UnroundedTrace.height A) := rfl

theorem topMap_mem_cylinderOnly (m : M) : topMap A m ∈ cylinderOnlyPart A := by
  intro h
  exact h.elim (positive_height_avoids_handle A m (UnroundedTrace.height_pos A) le_rfl)
    (positive_height_avoids_added A m (UnroundedTrace.height_pos A))

def topLift (m : M) : cylinderOnlyPart A := ⟨topMap A m, topMap_mem_cylinderOnly A m⟩

theorem topLift_coordinates (m : M) :
    (unchangedCylinderHomeomorph A (topLift A m)).val.val = (m, UnroundedTrace.height A) := by
  apply (LowHeightCylinder.injective_heightCylinder d e)
  exact unchangedCylinderHomeomorph_ambient A (topLift A m)

theorem isEmbedding_topMap : IsEmbedding (topMap A) := by
  have he : IsEmbedding (fun m : M ↦
      LowHeightCylinder.heightCylinder d e (m, UnroundedTrace.height A)) :=
    (LowHeightCylinder.isEmbedding_heightCylinder d e).comp (isEmbedding_prodMkLeft _)
  exact he.codRestrict (ambientSet A) (fun m ↦ (topMap A m).property)

theorem isClosedEmbedding_topMap : IsClosedEmbedding (topMap A) :=
  (topMap A).continuous.isClosedEmbedding (isEmbedding_topMap A).injective

def topEnd : Set (ambientSet A) := range (topMap A)

theorem isClosed_topEnd : IsClosed (topEnd A) := (isClosedEmbedding_topMap A).isClosed_range

def topEndHomeomorph : M ≃ₜ topEnd A := (isEmbedding_topMap A).toHomeomorph

theorem topEndHomeomorph_val (m : M) : (topEndHomeomorph A m).val = topMap A m := rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
