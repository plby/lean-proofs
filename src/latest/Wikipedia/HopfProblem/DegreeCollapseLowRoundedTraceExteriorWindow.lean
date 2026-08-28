import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceOtherEndPieces

/-!

# The retained cylinder end is the original manifold outside a closed tube

At height zero, the compact rounding image is precisely the image of the
outer closed tube. The old handle contributes a smaller subset of that
same image. Their complement is an actual open subset of the original
manifold, with its original inherited smooth structure.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def outerTubeImage : Set M :=
  A.tube '' ((univ : Set (NoExoticSixSphere.Sphere d)) ×ˢ
    closedBall (0 : Vector (7 - d)) (outerRadius A))

theorem isCompact_outerTubeImage : IsCompact (outerTubeImage A) := by
  apply (isCompact_univ.prod (isCompact_closedBall _ _)).image_of_continuousOn
  intro p hp
  have hc := (A.tube_localDiffeomorph p.1 p.2
    ((closedBall_subset_closedBall (outerRadius_lt A).le) hp.2)).contMDiffAt.continuousAt
  exact hc.continuousWithinAt

theorem isClosed_outerTubeImage : IsClosed (outerTubeImage A) := by
  let := e.closedEmbedding.isEmbedding.t2Space
  exact (isCompact_outerTubeImage A).isClosed

def retainedExterior : Opens M := ⟨(outerTubeImage A)ᶜ, (isClosed_outerTubeImage A).isOpen_compl⟩

theorem zero_cylinder_mem_added_iff (m : M) :
    (LowHeightCylinder.heightCylinder d e) (m, 0) ∈ A.collarSheet '' addedParameters A ↔
      m ∈ outerTubeImage A := by
  constructor
  · rintro ⟨q, hq, he⟩
    have hm := congrArg Prod.fst ((LowHeightCylinder.injective_heightCylinder d e) he)
    exact ⟨q.1, ⟨mem_univ _, hq.1⟩, hm⟩
  · rintro ⟨⟨s, v⟩, hp, hm⟩
    refine ⟨((s, v), 0), ⟨hp.2, ⟨?_, le_rfl⟩, ?_⟩, ?_⟩
    · linarith [(bump A).rOut_pos]
    · exact GeneralRoundedHandleCorner.nonneg_of_corner (bump A)
        (UnroundedTrace.handleRadius_pos A).le (Or.inl le_rfl)
    · change LowHeightCylinder.heightCylinder d e (A.tube (s, v), 0) =
        LowHeightCylinder.heightCylinder d e (m, 0)
      rw [hm]

theorem zero_cylinder_mem_handle_imp_outer (m : M)
    (hp : (LowHeightCylinder.heightCylinder d e) (m, 0) ∈ range (UnroundedTrace.handleMap A)) :
    m ∈ outerTubeImage A := by
  obtain ⟨q, hq⟩ := hp
  obtain ⟨s, _, hm, _⟩ := (UnroundedTrace.intersection_iff A q.1.property
    (UnroundedTrace.handle_vector_mem A q) m ⟨le_rfl, (UnroundedTrace.height_pos A).le⟩).mp hq
  exact ⟨(s, q.2.val), ⟨mem_univ _,
    (closedBall_subset_closedBall (outerRadius_gt_handle A).le) q.2.property⟩, hm⟩

theorem mem_retainedExterior_iff (m : M) : m ∈ retainedExterior A ↔
    (LowHeightCylinder.heightCylinder d e) (m, 0) ∉ range (UnroundedTrace.handleMap A) ∪
      A.collarSheet '' addedParameters A := by
  constructor
  · intro hm hp
    rcases hp with hp | hp
    · exact hm (zero_cylinder_mem_handle_imp_outer A m hp)
    · exact hm ((zero_cylinder_mem_added_iff A m).mp hp)
  · intro hp hm
    exact hp (Or.inr ((zero_cylinder_mem_added_iff A m).mpr hm))

def bottomTraceMap (m : M) : ambientSet A :=
  ⟨(LowHeightCylinder.heightCylinder d e) (m, 0), unrounded_subset A
    (Or.inl ⟨(m, ⟨0, le_rfl, (UnroundedTrace.height_pos A).le⟩), rfl⟩)⟩

theorem continuous_bottomTraceMap : Continuous (bottomTraceMap A) :=
  ((LowHeightCylinder.continuous_heightCylinder d e).comp
    (continuous_id.prodMk continuous_const)).subtype_mk _

def exteriorCylinderLift (m : retainedExterior A) : cylinderOnlyPart A :=
  ⟨bottomTraceMap A m.val, (mem_retainedExterior_iff A m.val).mp m.property⟩

theorem exteriorCylinderLift_coordinates (m : retainedExterior A) :
    (unchangedCylinderHomeomorph A (exteriorCylinderLift A m)).val.val = (m.val, 0) :=
  LowHeightCylinder.injective_heightCylinder d e
    (unchangedCylinderHomeomorph_ambient A (exteriorCylinderLift A m))

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
