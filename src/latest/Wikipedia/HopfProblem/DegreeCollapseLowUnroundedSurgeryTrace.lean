import Wikipedia.HopfProblem.DegreeCollapseLowAttachingCylinderIntersection
import Wikipedia.SmoothSixDPoincare.ClosedAttachment

/-!

# The actual compact ambient attachment for low-dimensional surgery

The short original-manifold cylinder meets the handle exactly on its attaching
face. Half the available transverse radius retains a smooth margin. The
ambient union is compact and is homeomorphic to the actual closed-attachment
quotient. No rounded smooth trace or boundary atlas is inferred here.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.UnroundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel
open Wikipedia.SmoothSixDPoincare

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def handleRadius : ℝ := A.radius / 2

theorem handleRadius_pos : 0 < handleRadius A := half_pos A.radius_pos

theorem handleRadius_lt : handleRadius A < A.radius := half_lt_self A.radius_pos

abbrev Handle :=
  closedBall (0 : Vector (d + 1)) 1 × closedBall (0 : Vector (7 - d)) (handleRadius A)

theorem handle_vector_mem (p : Handle A) : p.2.val ∈ closedBall (0 : Vector (7 - d)) A.radius :=
  (closedBall_subset_closedBall (handleRadius_lt A).le) p.2.property

theorem closedEmbedding_handle :
    IsClosedEmbedding (fun p : Handle A ↦ A.map (p.1.val, p.2.val)) :=
  LowDiskThickening.restrict_closedProduct_embedding
    (fun p : closedBall (0 : Vector (d + 1)) 1 × Vector (7 - d) ↦ A.map (p.1.val, p.2))
    (handleRadius_lt A).le A.embedded

def handleMap : C(Handle A, Vector (e.ambientDimension + (1 + (1 + (d + 1))))) :=
  ⟨fun p ↦ A.map (p.1.val, p.2.val), (closedEmbedding_handle A).continuous⟩

def attachingFace : Set (Handle A) := {p | p.1.val ∈ sphere (0 : Vector (d + 1)) 1}

variable [CompactSpace M]

def height : ℝ := Classical.choose A.exists_heightCylinder_intersection

theorem height_pos : 0 < height A :=
  (Classical.choose_spec A.exists_heightCylinder_intersection).1

theorem intersection_iff {x : Vector (d + 1)} (hx : x ∈ closedBall 0 1)
    {v : Vector (7 - d)} (hv : v ∈ closedBall 0 A.radius) (m : M)
    {t : ℝ} (ht : t ∈ Icc 0 (height A)) :
    A.map (x, v) = (LowHeightCylinder.heightCylinder d e) (m, t) ↔
      ∃ s : NoExoticSixSphere.Sphere d, s.val = x ∧ A.tube (s, v) = m ∧ t = 0 :=
  (Classical.choose_spec A.exists_heightCylinder_intersection).2 x hx v hv m t ht

abbrev Cylinder := M × Icc (0 : ℝ) (height A)

def cylinderMap : C(Cylinder A, Vector (e.ambientDimension + (1 + (1 + (d + 1))))) :=
  ⟨fun p ↦ (LowHeightCylinder.heightCylinder d e) (p.1, p.2.val),
    ((LowHeightCylinder.closedEmbedding_heightCylinder_slab d e) 0 (height A)).continuous⟩

theorem closedEmbedding_cylinder : IsClosedEmbedding (cylinderMap A) :=
  (LowHeightCylinder.closedEmbedding_heightCylinder_slab d e) 0 (height A)

theorem handle_mem_cylinder_iff (p : Handle A) :
    handleMap A p ∈ range (cylinderMap A) ↔ p ∈ attachingFace A := by
  constructor
  · rintro ⟨⟨m, t⟩, he⟩
    have h := (intersection_iff A p.1.property (handle_vector_mem A p) m t.property).mp
      he.symm
    obtain ⟨s, hs, _, _⟩ := h
    change p.1.val ∈ sphere (0 : Vector (d + 1)) 1
    exact hs ▸ s.property
  · intro hp
    let s : NoExoticSixSphere.Sphere d := ⟨p.1.val, hp⟩
    refine ⟨(A.tube (s, p.2.val), ⟨0, le_rfl, (height_pos A).le⟩), ?_⟩
    exact ((LowHeightCylinder.heightCylinder_zero d e) (A.tube (s, p.2.val))).trans
      (A.map_boundary s p.2.val (handle_vector_mem A p)).symm

def ambientSet : Set (Vector (e.ambientDimension + (1 + (1 + (d + 1))))) :=
  range (cylinderMap A) ∪ range (handleMap A)

theorem isCompact_ambientSet : IsCompact (ambientSet A) :=
  (isCompact_range (cylinderMap A).continuous).union
    (isCompact_range (handleMap A).continuous)

theorem isClosed_ambientSet : IsClosed (ambientSet A) := (isCompact_ambientSet A).isClosed

/-- The unrounded ambient union has exactly the specified closed-attachment topology. -/
def attachmentHomeomorph :
    ClosedAttachment.Space (range (cylinderMap A)) (attachingFace A) (handleMap A) ≃ₜ
      ambientSet A :=
  ClosedAttachment.unionHomeomorph (range (cylinderMap A)) (attachingFace A) (handleMap A)
    (isCompact_range (cylinderMap A).continuous) (closedEmbedding_handle A).injective
    (handle_mem_cylinder_iff A)

theorem map_intersection_eq : range (cylinderMap A) ∩ range (handleMap A) =
    range (fun p : NoExoticSixSphere.Sphere d × closedBall (0 : Vector (7 - d)) (handleRadius A) ↦
      (LowHeightCylinder.heightCylinder d e) (A.tube (p.1, p.2.val), 0)) := by
  ext y
  constructor
  · rintro ⟨hc, p, rfl⟩
    have hp := (handle_mem_cylinder_iff A p).mp hc
    let s : NoExoticSixSphere.Sphere d := ⟨p.1.val, hp⟩
    refine ⟨(s, p.2), ?_⟩
    exact ((LowHeightCylinder.heightCylinder_zero d e) (A.tube (s, p.2.val))).trans
      (A.map_boundary s p.2.val (handle_vector_mem A p)).symm
  · rintro ⟨⟨s, v⟩, rfl⟩
    have hv : v.val ∈ closedBall (0 : Vector (7 - d)) A.radius :=
      (closedBall_subset_closedBall (handleRadius_lt A).le) v.property
    refine ⟨⟨(A.tube (s, v.val), ⟨0, le_rfl, (height_pos A).le⟩), rfl⟩,
      (⟨s.val, sphere_subset_closedBall s.property⟩, v), ?_⟩
    exact (A.map_boundary s v.val hv).trans
      ((LowHeightCylinder.heightCylinder_zero d e) (A.tube (s, v.val))).symm

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.UnroundedTrace
