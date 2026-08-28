import Wikipedia.HopfProblem.DegreeCollapseSurgeryCylinderCollapse
import Wikipedia.NoExoticSixSphere.UnitSurgeryCoordinates
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyBoundary

/-!
# The actual canonical surgery boundary in the flattened trace body

The closed exterior stays at height zero and the new face is the original
embedded product D4 × S2. Their exact intersection is the common corner.
Closed-cover comparison therefore identifies the canonical surgery target
with this actual ambient union, retaining both full piece maps.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem closedEmbedding_bottomMap : IsClosedEmbedding (bottomMap A) := by
  apply (bottomMap A).continuous.isClosedEmbedding
  intro x y h
  exact congrArg Prod.fst (e.injective_heightCylinder h)

def flatExteriorMap : C(FramedSurgery.Exterior (E := Vector 4) (UnitSurgery.face A hR),
    Vector (e.ambientDimension + 6)) :=
  (bottomMap A).comp (FramedSurgery.exteriorOldMap (E := Vector 4) (UnitSurgery.face A hR))

def flatNewFaceMap : C(FramedSurgery.ClosedNewFace (Vector 4) (Vector 3),
    Vector (e.ambientDimension + 6)) :=
  (TraceCoreAttachment.unitHandleMap A hR).comp (FramedSurgery.wholeNewFace (Vector 4) (Vector 3))

theorem flatNewFaceMap_apply (p : FramedSurgery.ClosedNewFace (Vector 4) (Vector 3)) :
    flatNewFaceMap A hR p = A.map (p.1.val, p.2.val) := rfl

theorem closedEmbedding_flatExteriorMap : IsClosedEmbedding (flatExteriorMap A hR) :=
  (closedEmbedding_bottomMap A).comp
    (FramedSurgery.exteriorOldMap_isClosedEmbedding (E := Vector 4) (UnitSurgery.face A hR))

theorem closedEmbedding_flatNewFaceMap : IsClosedEmbedding (flatNewFaceMap A hR) :=
  (flatNewFaceMap A hR).continuous.isClosedEmbedding
    ((TraceCoreAttachment.injective_unitHandleMap A hR).comp
      (FramedSurgery.wholeNewFace_injective (Vector 4) (Vector 3)))

def flatBoundarySet : Set (Vector (e.ambientDimension + 6)) :=
  range (flatExteriorMap A hR) ∪ range (flatNewFaceMap A hR)

theorem isClosed_flatBoundarySet : IsClosed (flatBoundarySet A hR) :=
  (closedEmbedding_flatExteriorMap A hR).isClosed_range.union
    (closedEmbedding_flatNewFaceMap A hR).isClosed_range

theorem flatBoundary_subset_body : flatBoundarySet A hR ⊆ bodySet A := by
  rintro x (⟨r, rfl⟩ | ⟨p, rfl⟩)
  · exact Or.inl ⟨r.val, rfl⟩
  · right
    exact ⟨TraceCoreAttachment.unitHandleCoordinates A hR
      (FramedSurgery.wholeNewFace (Vector 4) (Vector 3) p), rfl⟩

theorem isCompact_flatBoundarySet : IsCompact (flatBoundarySet A hR) :=
  (isCompact_bodySet A).of_isClosed_subset (isClosed_flatBoundarySet A hR)
    (flatBoundary_subset_body A hR)

theorem flatBoundary_overlap (r : FramedSurgery.Exterior (E := Vector 4) (UnitSurgery.face A hR))
    (p : FramedSurgery.ClosedNewFace (Vector 4) (Vector 3)) :
    flatExteriorMap A hR r = flatNewFaceMap A hR p ↔
      ∃ q : Sphere 3 × Sphere 2, r = FramedSurgery.exteriorCorner (E := Vector 4) (UnitSurgery.face A hR) q ∧
        p = (⟨q.1.val, sphere_subset_closedBall q.1.property⟩, q.2) := by
  have hv : p.2.val ∈ closedBall (0 : Vector 3) A.radius :=
    (closedBall_subset_closedBall (by rw [hR]; norm_num : (1 : ℝ) ≤ A.radius))
      (sphere_subset_closedBall p.2.property)
  constructor
  · intro h
    have he : A.map (p.1.val, p.2.val) = e.heightCylinder (r.val, 0) := h.symm
    obtain ⟨s, hs, hm, ht⟩ := (UnroundedTrace.intersection_iff A p.1.property hv r.val
      ⟨le_rfl, (UnroundedTrace.height_pos A).le⟩).mp he
    refine ⟨(s, p.2), Subtype.ext hm.symm, ?_⟩
    exact Prod.ext (Subtype.ext hs.symm) rfl
  · rintro ⟨q, rfl, rfl⟩
    change e.heightCylinder (A.tube (q.1, q.2.val), 0) = A.map (q.1.val, q.2.val)
    exact (e.heightCylinder_zero _).trans (A.map_boundary q.1 q.2.val hv).symm

def flatExterior : C(FramedSurgery.Exterior (E := Vector 4) (UnitSurgery.face A hR), flatBoundarySet A hR) :=
  ⟨fun r ↦ ⟨flatExteriorMap A hR r, Or.inl ⟨r, rfl⟩⟩,
    (flatExteriorMap A hR).continuous.subtype_mk _⟩

def flatNewFace : C(FramedSurgery.ClosedNewFace (Vector 4) (Vector 3), flatBoundarySet A hR) :=
  ⟨fun p ↦ ⟨flatNewFaceMap A hR p, Or.inr ⟨p, rfl⟩⟩,
    (flatNewFaceMap A hR).continuous.subtype_mk _⟩

theorem closedEmbedding_flatExterior : IsClosedEmbedding (flatExterior A hR) :=
  ClosedCover.isClosedEmbedding_codRestrict (closedEmbedding_flatExteriorMap A hR)
    (fun r ↦ Or.inl ⟨r, rfl⟩)

theorem closedEmbedding_flatNewFace : IsClosedEmbedding (flatNewFace A hR) :=
  ClosedCover.isClosedEmbedding_codRestrict (closedEmbedding_flatNewFaceMap A hR)
    (fun p ↦ Or.inr ⟨p, rfl⟩)

theorem flatBoundary_cover : range (flatExterior A hR) ∪ range (flatNewFace A hR) = univ := by
  apply eq_univ_of_forall
  rintro ⟨x, ⟨r, rfl⟩ | ⟨p, rfl⟩⟩
  · exact Or.inl ⟨r, rfl⟩
  · exact Or.inr ⟨p, rfl⟩

theorem flatBoundary_incidence (r : FramedSurgery.Exterior (E := Vector 4) (UnitSurgery.face A hR))
    (p : FramedSurgery.ClosedNewFace (Vector 4) (Vector 3)) :
    FramedSurgery.exteriorNewMap (E := Vector 4) (UnitSurgery.face A hR) 2 r =
      FramedSurgery.closedNewMap (E := Vector 4) (UnitSurgery.face A hR) 2 p ↔
        flatExterior A hR r = flatNewFace A hR p := by
  rw [Subtype.ext_iff]
  exact (FramedSurgery.exterior_new_face_overlap (E := Vector 4) (UnitSurgery.face A hR) 2 r p).trans
    (flatBoundary_overlap A hR r p).symm

def flatBoundaryHomeomorph : UnitSurgery.Target A hR ≃ₜ flatBoundarySet A hR :=
  ClosedCover.homeomorphOfClosedPieces
    (FramedSurgery.exteriorNewMap (E := Vector 4) (UnitSurgery.face A hR) 2) (flatExterior A hR)
    (FramedSurgery.closedNewMap (E := Vector 4) (UnitSurgery.face A hR) 2) (flatNewFace A hR)
    (FramedSurgery.exteriorNewMap_isClosedEmbedding (E := Vector 4) (UnitSurgery.face A hR) 2)
    (closedEmbedding_flatExterior A hR)
    (FramedSurgery.closedNewMap_isClosedEmbedding (E := Vector 4) (UnitSurgery.face A hR) 2)
    (closedEmbedding_flatNewFace A hR)
    (FramedSurgery.exterior_new_face_cover (E := Vector 4) (UnitSurgery.face A hR) 2)
    (flatBoundary_cover A hR) (Homeomorph.refl _) (flatBoundary_incidence A hR)

theorem flatBoundaryHomeomorph_exterior (r : FramedSurgery.Exterior (E := Vector 4) (UnitSurgery.face A hR)) :
    flatBoundaryHomeomorph A hR (FramedSurgery.exteriorNewMap (E := Vector 4) (UnitSurgery.face A hR) 2 r) =
      flatExterior A hR r :=
  ClosedCover.homeomorphOfClosedPieces_left _ _ _ _ _ _ _ _ _ _ _ _ r

theorem flatBoundaryHomeomorph_newFace (p : FramedSurgery.ClosedNewFace (Vector 4) (Vector 3)) :
    flatBoundaryHomeomorph A hR (FramedSurgery.closedNewMap (E := Vector 4) (UnitSurgery.face A hR) 2 p) =
      flatNewFace A hR p :=
  ClosedCover.homeomorphOfClosedPieces_right _ _ _ _ _ _ _ _ _ _ _ _ p

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
