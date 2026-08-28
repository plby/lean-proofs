import Wikipedia.NoExoticSixSphere.AttachingCylinderIntersection
import Wikipedia.NoExoticSixSphere.ClosedProductRestriction
import Wikipedia.NoExoticSixSphere.ClosedNoncompactAttachment

/-!
# The closed ambient attachment before corner rounding

Choose a short cylinder whose intersection with the handle is exactly the
attaching face. Use half the available transverse radius to retain a smooth
margin. The actual ambient union is closed and is homeomorphic to its
closed-attachment quotient in every manifold dimension, without global
compactness. It is compact when the original manifold is compact. No smooth
boundary atlas or rounded trace is asserted by this topological construction.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnroundedTrace

open GLOrthonormalization Stiefel
open Wikipedia.SmoothSixDPoincare

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def handleRadius : ℝ := A.radius / 2

theorem handleRadius_pos : 0 < handleRadius A := half_pos A.radius_pos

theorem handleRadius_lt : handleRadius A < A.radius := half_lt_self A.radius_pos

abbrev Handle := closedBall (0 : Vector 4) 1 × closedBall (0 : Vector (n - 3)) (handleRadius A)

theorem handle_vector_mem (p : Handle A) : p.2.val ∈ closedBall (0 : Vector (n - 3)) A.radius :=
  (closedBall_subset_closedBall (handleRadius_lt A).le) p.2.property

theorem closedEmbedding_handle :
    IsClosedEmbedding (fun p : Handle A ↦ A.map (p.1.val, p.2.val)) :=
  restrict_closedProduct_embedding
    (fun p : closedBall (0 : Vector 4) 1 × Vector (n - 3) ↦ A.map (p.1.val, p.2))
    (handleRadius_lt A).le A.embedded

def handleMap : C(Handle A, Vector (e.ambientDimension + 6)) :=
  ⟨fun p ↦ A.map (p.1.val, p.2.val), (closedEmbedding_handle A).continuous⟩

def attachingFace : Set (Handle A) := {p | p.1.val ∈ sphere (0 : Vector 4) 1}

def height : ℝ := Classical.choose A.exists_heightCylinder_intersection

theorem height_pos : 0 < height A :=
  (Classical.choose_spec A.exists_heightCylinder_intersection).1

theorem intersection_iff {x : Vector 4} (hx : x ∈ closedBall 0 1)
    {v : Vector (n - 3)} (hv : v ∈ closedBall 0 A.radius) (m : M)
    {t : ℝ} (ht : t ∈ Icc 0 (height A)) :
    A.map (x, v) = e.heightCylinder (m, t) ↔
      ∃ s : Sphere 3, s.val = x ∧ A.tube (s, v) = m ∧ t = 0 :=
  (Classical.choose_spec A.exists_heightCylinder_intersection).2 x hx v hv m t ht

abbrev Cylinder := M × Icc (0 : ℝ) (height A)

def cylinderMap : C(Cylinder A, Vector (e.ambientDimension + 6)) :=
  ⟨fun p ↦ e.heightCylinder (p.1, p.2.val),
    (e.closedEmbedding_heightCylinder_slab 0 (height A)).continuous⟩

theorem closedEmbedding_cylinder : IsClosedEmbedding (cylinderMap A) :=
  e.closedEmbedding_heightCylinder_slab 0 (height A)

theorem handle_mem_cylinder_iff (p : Handle A) :
    handleMap A p ∈ range (cylinderMap A) ↔ p ∈ attachingFace A := by
  constructor
  · rintro ⟨⟨m, t⟩, he⟩
    have h := (intersection_iff A p.1.property (handle_vector_mem A p) m t.property).mp
      he.symm
    obtain ⟨s, hs, _, _⟩ := h
    change p.1.val ∈ sphere (0 : Vector 4) 1
    exact hs ▸ s.property
  · intro hp
    let s : Sphere 3 := ⟨p.1.val, hp⟩
    refine ⟨(A.tube (s, p.2.val), ⟨0, le_rfl, (height_pos A).le⟩), ?_⟩
    exact (e.heightCylinder_zero (A.tube (s, p.2.val))).trans
      (A.map_boundary s p.2.val (handle_vector_mem A p)).symm

def ambientSet : Set (Vector (e.ambientDimension + 6)) :=
  range (cylinderMap A) ∪ range (handleMap A)

theorem isCompact_ambientSet [CompactSpace M] : IsCompact (ambientSet A) :=
  (isCompact_range (cylinderMap A).continuous).union
    (isCompact_range (handleMap A).continuous)

theorem isClosed_ambientSet : IsClosed (ambientSet A) :=
  (closedEmbedding_cylinder A).isClosed_range.union (closedEmbedding_handle A).isClosed_range

/-- The unrounded ambient union has exactly the specified closed-attachment topology. -/
def attachmentHomeomorph :
    ClosedAttachment.Space (range (cylinderMap A)) (attachingFace A) (handleMap A) ≃ₜ
      ambientSet A :=
  ClosedAttachment.unionHomeomorphOfIsClosed
    (range (cylinderMap A)) (attachingFace A) (handleMap A)
    (closedEmbedding_cylinder A).isClosed_range (closedEmbedding_handle A).isClosedMap
    (closedEmbedding_handle A).injective (handle_mem_cylinder_iff A)

theorem map_intersection_eq : range (cylinderMap A) ∩ range (handleMap A) =
    range (fun p : Sphere 3 × closedBall (0 : Vector (n - 3)) (handleRadius A) ↦
      e.heightCylinder (A.tube (p.1, p.2.val), 0)) := by
  ext y
  constructor
  · rintro ⟨hc, p, rfl⟩
    have hp := (handle_mem_cylinder_iff A p).mp hc
    let s : Sphere 3 := ⟨p.1.val, hp⟩
    refine ⟨(s, p.2), ?_⟩
    exact (e.heightCylinder_zero (A.tube (s, p.2.val))).trans
      (A.map_boundary s p.2.val (handle_vector_mem A p)).symm
  · rintro ⟨⟨s, v⟩, rfl⟩
    have hv : v.val ∈ closedBall (0 : Vector (n - 3)) A.radius :=
      (closedBall_subset_closedBall (handleRadius_lt A).le) v.property
    refine ⟨⟨(A.tube (s, v.val), ⟨0, le_rfl, (height_pos A).le⟩), rfl⟩,
      (⟨s.val, sphere_subset_closedBall s.property⟩, v), ?_⟩
    exact (A.map_boundary s v.val hv).trans
      (e.heightCylinder_zero (A.tube (s, v.val))).symm

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnroundedTrace
