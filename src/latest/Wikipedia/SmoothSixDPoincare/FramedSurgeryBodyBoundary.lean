import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyAttachment
import Wikipedia.SmoothSixDPoincare.ClosedPieceComparison
import Wikipedia.SmoothSixDPoincare.SurgeryComplementPieces

/-!
# Identify the constructed surgery boundary inside the whole-body quotient

The designated boundary is exactly the union of the old closed exterior and
the new closed handle face. Its subspace topology agrees with the already
constructed surgery boundary, with both closed-piece maps fixed pointwise.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  (i : C(X, Y))

def bodyBoundarySet : Set (AttachedBody A i) :=
  range (bodyExteriorMap A i) ∪ range (bodyNewFaceMap A i)

omit [T2Space X] [CompactSpace X] in
theorem isClosed_bodyBoundarySet (hi : IsClosedEmbedding i) : IsClosed (bodyBoundarySet A i) :=
  (bodyExteriorMap_isClosedEmbedding A i hi).isClosed_range.union
    (bodyNewFaceMap_isClosedEmbedding A i hi.injective).isClosed_range

abbrev BodyBoundary := bodyBoundarySet A i

def bodyBoundaryExterior : C(Exterior A, BodyBoundary A i) :=
  ⟨fun r => ⟨bodyExteriorMap A i r, Or.inl (mem_range_self r)⟩,
    (bodyExteriorMap A i).continuous.subtype_mk _⟩

def bodyBoundaryNewFace : C(ClosedNewFace E F, BodyBoundary A i) :=
  ⟨fun p => ⟨bodyNewFaceMap A i p, Or.inr (mem_range_self p)⟩,
    (bodyNewFaceMap A i).continuous.subtype_mk _⟩

omit [T2Space X] [CompactSpace X] in
theorem bodyBoundaryExterior_isClosedEmbedding (hi : IsClosedEmbedding i) :
    IsClosedEmbedding (bodyBoundaryExterior A i) :=
  ClosedCover.isClosedEmbedding_codRestrict (s := bodyBoundarySet A i)
    (bodyExteriorMap_isClosedEmbedding A i hi) (fun r => Or.inl (mem_range_self r))

omit [T2Space X] [CompactSpace X] in
theorem bodyBoundaryNewFace_isClosedEmbedding (hi : Injective i) :
    IsClosedEmbedding (bodyBoundaryNewFace A i) :=
  ClosedCover.isClosedEmbedding_codRestrict (s := bodyBoundarySet A i)
    (bodyNewFaceMap_isClosedEmbedding A i hi) (fun p => Or.inr (mem_range_self p))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X] [CompactSpace X]
    [T2Space Y] [CompactSpace Y] in
theorem bodyBoundary_cover :
    range (bodyBoundaryExterior A i) ∪ range (bodyBoundaryNewFace A i) = univ := by
  apply eq_univ_of_forall
  intro z
  rcases z.property with ⟨r, hr⟩ | ⟨p, hp⟩
  · exact Or.inl ⟨r, Subtype.ext hr⟩
  · exact Or.inr ⟨p, Subtype.ext hp⟩

variable (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

omit [FiniteDimensional ℝ F] [CompactSpace X] [T2Space Y] [CompactSpace Y] in
theorem bodyBoundary_incidence (hi : Injective i) (r : Exterior A) (p : ClosedNewFace E F) :
    exteriorNewMap A n r = closedNewMap A n p ↔
      bodyBoundaryExterior A i r = bodyBoundaryNewFace A i p := by
  rw [Subtype.ext_iff]
  exact (exterior_new_face_overlap A n r p).trans
    (bodyExteriorMap_eq_newFace A i hi r p).symm

def bodyBoundaryHomeomorph (hi : IsClosedEmbedding i) : Boundary A n ≃ₜ BodyBoundary A i :=
  ClosedCover.homeomorphOfClosedPieces
    (exteriorNewMap A n) (bodyBoundaryExterior A i)
    (closedNewMap A n) (bodyBoundaryNewFace A i)
    (exteriorNewMap_isClosedEmbedding A n) (bodyBoundaryExterior_isClosedEmbedding A i hi)
    (closedNewMap_isClosedEmbedding A n) (bodyBoundaryNewFace_isClosedEmbedding A i hi.injective)
    (exterior_new_face_cover A n) (bodyBoundary_cover A i)
    (Homeomorph.refl _) (bodyBoundary_incidence A i n hi.injective)

theorem bodyBoundaryHomeomorph_exterior (hi : IsClosedEmbedding i) (r : Exterior A) :
    bodyBoundaryHomeomorph A i n hi (exteriorNewMap A n r) = bodyBoundaryExterior A i r :=
  ClosedCover.homeomorphOfClosedPieces_left _ _ _ _ _ _ _ _ _ _ _ _ r

theorem bodyBoundaryHomeomorph_newFace (hi : IsClosedEmbedding i) (p : ClosedNewFace E F) :
    bodyBoundaryHomeomorph A i n hi (closedNewMap A n p) = bodyBoundaryNewFace A i p :=
  ClosedCover.homeomorphOfClosedPieces_right _ _ _ _ _ _ _ _ _ _ _ _ p

def boundaryBodyMap (hi : IsClosedEmbedding i) : C(Boundary A n, AttachedBody A i) :=
  ⟨fun x => (bodyBoundaryHomeomorph A i n hi x).val,
    continuous_subtype_val.comp (bodyBoundaryHomeomorph A i n hi).continuous⟩

theorem boundaryBodyMap_isClosedEmbedding (hi : IsClosedEmbedding i) :
    IsClosedEmbedding (boundaryBodyMap A i n hi) :=
  (isClosed_bodyBoundarySet A i hi).isClosedEmbedding_subtypeVal.comp
    (bodyBoundaryHomeomorph A i n hi).isClosedEmbedding

theorem boundaryBodyMap_range (hi : IsClosedEmbedding i) :
    range (boundaryBodyMap A i n hi) = bodyBoundarySet A i := by
  change range (Subtype.val ∘ bodyBoundaryHomeomorph A i n hi) = _
  rw [(bodyBoundaryHomeomorph A i n hi).surjective.range_comp]
  exact Subtype.range_coe

theorem boundaryBodyMap_exterior (hi : IsClosedEmbedding i) (r : Exterior A) :
    boundaryBodyMap A i n hi (exteriorNewMap A n r) =
      FaceAttachment.oldMap (bodyFaceMap A i) (i r.val) :=
  congrArg (fun z : BodyBoundary A i => z.val) (bodyBoundaryHomeomorph_exterior A i n hi r)

theorem boundaryBodyMap_newFace (hi : IsClosedEmbedding i) (p : ClosedNewFace E F) :
    boundaryBodyMap A i n hi (closedNewMap A n p) =
      FaceAttachment.handleMap (bodyFaceMap A i) (wholeNewFace E F p) :=
  congrArg (fun z : BodyBoundary A i => z.val) (bodyBoundaryHomeomorph_newFace A i n hi p)

theorem boundaryBodyMap_old_exterior (hi : IsClosedEmbedding i)
    (x : oldPatch A) (hx : x.val ∉ faceInterior A) :
    boundaryBodyMap A i n hi (oldMap A n x) =
      FaceAttachment.oldMap (bodyFaceMap A i) (i x.val) :=
  boundaryBodyMap_exterior A i n hi ⟨x.val, hx⟩

end Wikipedia.SmoothSixDPoincare.FramedSurgery
