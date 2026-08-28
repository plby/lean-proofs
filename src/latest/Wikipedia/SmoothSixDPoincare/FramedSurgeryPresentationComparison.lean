import Wikipedia.SmoothSixDPoincare.FramedSurgeryBoundaryPair
import Wikipedia.SmoothSixDPoincare.FramedSurgeryRetainedBodyFace

/-!
# Compare the constructed boundary with an original surgery presentation

Matching the original attaching face determines the same common exterior.
The exact closed-piece incidences then identify the constructed boundary
with the original new boundary, retaining both entire piece maps.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X R Z : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  [TopologicalSpace R] [TopologicalSpace Z] (d : SurgeryBoundaryPair E F R X Z)
  (hface : ∀ p, d.oldPiece p = A.map (oldFaceCoordinates E F p))

include hface in
theorem presentationExterior_range : range d.oldExterior = (faceInterior A)ᶜ := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩ hx
    obtain ⟨p, hp⟩ := faceInterior_subset_range hx
    let p' := (oldFaceCoordinates E F).symm p
    have hold : d.oldPiece p' = d.oldExterior r := by
      rw [hface]
      exact (congrArg A.map ((oldFaceCoordinates E F).apply_symm_apply p)).trans hp
    obtain ⟨q, -, hpq⟩ := (d.old_overlap r p').mp hold.symm
    have he : p.2.val = q.2.val :=
      congrArg (fun z : UnitSphere E × UnitBall F => z.2.val) hpq
    have hn : ‖p.2.val‖ = 1 := (congrArg norm he).trans (mem_sphere_zero_iff_norm.mp q.2.property)
    have hlt := (face_mem_interior_iff A p.1 p.2).mp (hp.symm ▸ hx)
    rw [hn] at hlt
    exact lt_irrefl _ hlt
  · intro hx
    have hc : x ∈ range d.oldExterior ∪ range d.oldPiece := by rw [d.old_cover]; trivial
    rcases hc with hr | ⟨p, rfl⟩
    · exact hr
    · have hn : ‖p.2.val‖ = 1 := le_antisymm p.2.property (not_lt.mp (by
        intro hlt
        apply hx
        rw [hface]
        exact (face_mem_interior_iff A _ _).mpr hlt))
      let q : UnitSphere E × UnitSphere F := (p.1, ⟨p.2.val, mem_sphere_zero_iff_norm.mpr hn⟩)
      exact ⟨d.boundary q, (d.old_overlap _ _).mpr ⟨q, rfl, rfl⟩⟩

def presentationExteriorCoordinates : Exterior A ≃ₜ R :=
  (Homeomorph.setCongr (presentationExterior_range A d hface).symm).trans
    d.oldExterior_closed.isEmbedding.toHomeomorph.symm

theorem presentationExteriorCoordinates_point (r : Exterior A) :
    d.oldExterior (presentationExteriorCoordinates A d hface r) = r.val := by
  change d.oldExterior (d.oldExterior_closed.isEmbedding.toHomeomorph.symm ⟨r.val, _⟩) = r.val
  exact congrArg Subtype.val (d.oldExterior_closed.isEmbedding.toHomeomorph.apply_symm_apply _)

theorem presentationExteriorCoordinates_corner (q : UnitSphere E × UnitSphere F) :
    presentationExteriorCoordinates A d hface (exteriorCorner A q) = d.boundary q := by
  apply d.oldExterior_closed.injective
  rw [presentationExteriorCoordinates_point]
  have hd := (d.old_overlap (d.boundary q) (oldBoundary q)).mpr ⟨q, rfl, rfl⟩
  exact ((hface (oldBoundary q)).symm).trans hd.symm

def presentationNewExterior : Exterior A → Z :=
  d.newExterior ∘ presentationExteriorCoordinates A d hface

def presentationNewPiece : ClosedNewFace E F → Z :=
  d.newPiece ∘ (newFaceCoordinates E F).symm

theorem presentationNewExterior_isClosedEmbedding :
    IsClosedEmbedding (presentationNewExterior A d hface) :=
  d.newExterior_closed.comp (presentationExteriorCoordinates A d hface).isClosedEmbedding

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
theorem presentationNewPiece_isClosedEmbedding : IsClosedEmbedding (presentationNewPiece d) :=
  d.newPiece_closed.comp (newFaceCoordinates E F).symm.isClosedEmbedding

theorem presentationNew_cover :
    range (presentationNewExterior A d hface) ∪ range (presentationNewPiece d) = univ := by
  change range (d.newExterior ∘ presentationExteriorCoordinates A d hface) ∪
    range (d.newPiece ∘ (newFaceCoordinates E F).symm) = univ
  rw [(presentationExteriorCoordinates A d hface).surjective.range_comp,
    (newFaceCoordinates E F).symm.surjective.range_comp]
  exact d.new_cover

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X] [CompactSpace X]
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

omit [FiniteDimensional ℝ F] [CompactSpace X] in
theorem presentationNew_incidence (r : Exterior A) (p : ClosedNewFace E F) :
    exteriorNewMap A n r = closedNewMap A n p ↔
      presentationNewExterior A d hface r = presentationNewPiece d p := by
  rw [exterior_new_face_overlap]
  change _ ↔ d.newExterior (presentationExteriorCoordinates A d hface r) =
    d.newPiece ((newFaceCoordinates E F).symm p)
  rw [d.new_overlap]
  constructor
  · rintro ⟨q, rfl, rfl⟩
    exact ⟨q, presentationExteriorCoordinates_corner A d hface q, rfl⟩
  · rintro ⟨q, hr, hp⟩
    refine ⟨q, (presentationExteriorCoordinates A d hface).injective
      (hr.trans (presentationExteriorCoordinates_corner A d hface q).symm), ?_⟩
    exact (newFaceCoordinates E F).symm.injective hp

def presentationBoundaryHomeomorph : Boundary A n ≃ₜ Z :=
  ClosedCover.homeomorphOfClosedPieces
    (exteriorNewMap A n) (presentationNewExterior A d hface)
    (closedNewMap A n) (presentationNewPiece d)
    (exteriorNewMap_isClosedEmbedding A n) (presentationNewExterior_isClosedEmbedding A d hface)
    (closedNewMap_isClosedEmbedding A n) (presentationNewPiece_isClosedEmbedding d)
    (exterior_new_face_cover A n) (presentationNew_cover A d hface)
    (Homeomorph.refl _) (presentationNew_incidence A d hface n)

theorem presentationBoundaryHomeomorph_exterior (r : Exterior A) :
    presentationBoundaryHomeomorph A d hface n (exteriorNewMap A n r) =
      d.newExterior (presentationExteriorCoordinates A d hface r) :=
  ClosedCover.homeomorphOfClosedPieces_left _ _ _ _ _ _ _ _ _ _ _ _ r

theorem presentationBoundaryHomeomorph_newFace (p : ClosedNewFace E F) :
    presentationBoundaryHomeomorph A d hface n (closedNewMap A n p) =
      d.newPiece ((newFaceCoordinates E F).symm p) :=
  ClosedCover.homeomorphOfClosedPieces_right _ _ _ _ _ _ _ _ _ _ _ _ p

end Wikipedia.SmoothSixDPoincare.FramedSurgery
