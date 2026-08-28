import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyBoundary

/-!
# Change positive-face disk coordinates, fixed at the attaching corner

A homeomorphism of the negative disk fixed on its sphere changes the
closed positive face and extends to the entire constructed boundary,
leaving its common exterior pointwise fixed.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

section Coordinates

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  (a : MorseHandle.UnitDisk E ≃ₜ MorseHandle.UnitDisk E)
  (ha : ∀ u : MorseHandle.UnitDisk E, ‖u.val‖ = 1 → a u = u)

def newFaceDiskChange : ClosedNewFace E F ≃ₜ ClosedNewFace E F :=
  a.prodCongr (Homeomorph.refl (UnitSphere F))

include ha in
theorem newFaceDiskChange_corner (u : UnitSphere E) (v : UnitSphere F) :
    newFaceDiskChange (F := F) a (⟨u.val, sphere_subset_closedBall u.property⟩, v) =
      (⟨u.val, sphere_subset_closedBall u.property⟩, v) :=
  Prod.ext (ha _ (mem_sphere_zero_iff_norm.mp u.property)) rfl

def wholeHandleDiskChange : WholeHandle E F ≃ₜ WholeHandle E F :=
  a.prodCongr (Homeomorph.refl (MorseHandle.UnitDisk F))

include ha in
theorem wholeHandleDiskChange_face (p : WholeHandle E F) (hp : p ∈ wholeAttachingFace E F) :
    wholeHandleDiskChange a p = p := Prod.ext (ha p.1 hp) rfl

theorem wholeHandleDiskChange_newFace (p : ClosedNewFace E F) :
    wholeHandleDiskChange a (wholeNewFace E F p) = wholeNewFace E F (newFaceDiskChange a p) := rfl

end Coordinates

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace H X] {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]
  (a : MorseHandle.UnitDisk E ≃ₜ MorseHandle.UnitDisk E)
  (ha : ∀ u : MorseHandle.UnitDisk E, ‖u.val‖ = 1 → a u = u)

include ha in
omit [FiniteDimensional ℝ F] [CompactSpace X] in
theorem diskChange_incidence (r : Exterior A) (p : ClosedNewFace E F) :
    exteriorNewMap A n r = closedNewMap A n p ↔
      exteriorNewMap A n r = closedNewMap A n (newFaceDiskChange a p) := by
  rw [exterior_new_face_overlap, exterior_new_face_overlap]
  constructor
  · rintro ⟨q, rfl, rfl⟩
    exact ⟨q, rfl, newFaceDiskChange_corner a ha q.1 q.2⟩
  · rintro ⟨q, hr, hp⟩
    exact ⟨q, hr, (newFaceDiskChange a).injective
      (hp.trans (newFaceDiskChange_corner a ha q.1 q.2).symm)⟩

def boundaryDiskChange : Boundary A n ≃ₜ Boundary A n :=
  ClosedCover.homeomorphOfClosedPieces
    (exteriorNewMap A n) (exteriorNewMap A n) (closedNewMap A n) (closedNewMap A n)
    (exteriorNewMap_isClosedEmbedding A n) (exteriorNewMap_isClosedEmbedding A n)
    (closedNewMap_isClosedEmbedding A n) (closedNewMap_isClosedEmbedding A n)
    (exterior_new_face_cover A n) (exterior_new_face_cover A n)
    (newFaceDiskChange a) (diskChange_incidence A n a ha)

theorem boundaryDiskChange_exterior (r : Exterior A) :
    boundaryDiskChange A n a ha (exteriorNewMap A n r) = exteriorNewMap A n r :=
  ClosedCover.homeomorphOfClosedPieces_left _ _ _ _ _ _ _ _ _ _ _ _ r

theorem boundaryDiskChange_newFace (p : ClosedNewFace E F) :
    boundaryDiskChange A n a ha (closedNewMap A n p) =
      closedNewMap A n (newFaceDiskChange a p) :=
  ClosedCover.homeomorphOfClosedPieces_right _ _ _ _ _ _ _ _ _ _ _ _ p

end Wikipedia.SmoothSixDPoincare.FramedSurgery
