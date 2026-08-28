import Wikipedia.SmoothSixDPoincare.FramedSurgeryClosedPresentation
import Wikipedia.SmoothSixDPoincare.NativeMorseBoundaryPair

/-!
# The constructed smooth surgery boundary has the original closed-piece presentation

The full closed embeddings, exhaustive covers, and exact common-corner
incidences are the proved maps of the actual boundary quotient. This record
is constructed from the original framed face and compact boundary.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

def oldFaceCoordinates (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :
    (UnitSphere E × UnitBall F) ≃ₜ (UnitSphere E × MorseHandle.UnitDisk F) :=
  (Homeomorph.refl (UnitSphere E)).prodCongr (MorseHandle.unitBallHomeomorph F)

def newFaceCoordinates (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :
    (UnitBall E × UnitSphere F) ≃ₜ ClosedNewFace E F :=
  (MorseHandle.unitBallHomeomorph E).prodCongr (Homeomorph.refl (UnitSphere F))

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

def boundaryPair : SurgeryBoundaryPair E F (Exterior A) X (Boundary A n) where
  oldExterior := exteriorOldMap A
  newExterior := exteriorNewMap A n
  oldPiece := A.map ∘ oldFaceCoordinates E F
  newPiece := closedNewMap A n ∘ newFaceCoordinates E F
  oldExterior_closed := exteriorOldMap_isClosedEmbedding A
  newExterior_closed := exteriorNewMap_isClosedEmbedding A n
  oldPiece_closed := A.closedEmbedding.comp (oldFaceCoordinates E F).isClosedEmbedding
  newPiece_closed := (closedNewMap_isClosedEmbedding A n).comp
    (newFaceCoordinates E F).isClosedEmbedding
  old_cover := by
    rw [(oldFaceCoordinates E F).surjective.range_comp]
    exact exterior_old_face_cover A
  new_cover := by
    rw [(newFaceCoordinates E F).surjective.range_comp]
    exact exterior_new_face_cover A n
  boundary := exteriorCorner A
  old_overlap := by
    intro r p
    constructor
    · intro h
      obtain ⟨q, hr, hp⟩ := (exterior_old_face_overlap A r (oldFaceCoordinates E F p)).mp h
      exact ⟨q, hr, (oldFaceCoordinates E F).injective hp⟩
    · rintro ⟨q, rfl, rfl⟩
      rfl
  new_overlap := by
    intro r p
    constructor
    · intro h
      obtain ⟨q, hr, hp⟩ := (exterior_new_face_overlap A n r (newFaceCoordinates E F p)).mp h
      exact ⟨q, hr, (newFaceCoordinates E F).injective hp⟩
    · rintro ⟨q, rfl, rfl⟩
      exact exteriorNewMap_corner A n q

theorem boundaryPair_oldPiece (p : UnitSphere E × UnitBall F) :
    (boundaryPair A n).oldPiece p = A.map (oldFaceCoordinates E F p) := rfl

theorem boundaryPair_newPiece (p : UnitBall E × UnitSphere F) :
    (boundaryPair A n).newPiece p = closedNewMap A n (newFaceCoordinates E F p) := rfl

end Wikipedia.SmoothSixDPoincare.FramedSurgery
