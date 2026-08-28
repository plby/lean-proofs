import Wikipedia.SmoothSixDPoincare.FramedSurgeryDiskChange
import Wikipedia.SmoothSixDPoincare.FaceAttachmentHandleChange

/-!
# The positive-face disk correction is the restriction of a whole-body correction

The whole handle changes only its negative disk coordinate and fixes its
attaching face pointwise. The designated boundary and the exact common
exterior are retained, with the prescribed positive-face reparametrization.
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
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (i : C(X, Y))
  (a : MorseHandle.UnitDisk E ≃ₜ MorseHandle.UnitDisk E)
  (ha : ∀ u : MorseHandle.UnitDisk E, ‖u.val‖ = 1 → a u = u)

def bodyDiskChange : AttachedBody A i ≃ₜ AttachedBody A i :=
  FaceAttachment.handleChange (bodyFaceMap A i) (wholeHandleDiskChange a)
    (wholeHandleDiskChange_face a ha)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X] [CompactSpace X]
    [T2Space Y] [CompactSpace Y] in
theorem bodyDiskChange_old (y : Y) :
    bodyDiskChange A i a ha (FaceAttachment.oldMap (bodyFaceMap A i) y) =
      FaceAttachment.oldMap (bodyFaceMap A i) y := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X] [CompactSpace X]
    [T2Space Y] [CompactSpace Y] in
theorem bodyDiskChange_handle (k : WholeHandle E F) :
    bodyDiskChange A i a ha (FaceAttachment.handleMap (bodyFaceMap A i) k) =
      FaceAttachment.handleMap (bodyFaceMap A i) (wholeHandleDiskChange a k) := rfl

variable (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)] (hi : IsClosedEmbedding i)

theorem bodyDiskChange_boundaryMap (z : Boundary A n) :
    boundaryBodyMap A i n hi (boundaryDiskChange A n a ha z) =
      bodyDiskChange A i a ha (boundaryBodyMap A i n hi z) := by
  have hc : z ∈ range (exteriorNewMap A n) ∪ range (closedNewMap A n) :=
    (exterior_new_face_cover A n).symm ▸ mem_univ z
  rcases hc with ⟨r, rfl⟩ | ⟨p, rfl⟩
  · exact (congrArg (boundaryBodyMap A i n hi) (boundaryDiskChange_exterior A n a ha r)).trans
      ((boundaryBodyMap_exterior A i n hi r).trans
        ((bodyDiskChange_old A i a ha (i r.val)).symm.trans
          (congrArg (bodyDiskChange A i a ha) (boundaryBodyMap_exterior A i n hi r)).symm))
  · exact (congrArg (boundaryBodyMap A i n hi) (boundaryDiskChange_newFace A n a ha p)).trans
      ((boundaryBodyMap_newFace A i n hi (newFaceDiskChange a p)).trans
        ((bodyDiskChange_handle A i a ha (wholeNewFace E F p)).symm.trans
          (congrArg (bodyDiskChange A i a ha) (boundaryBodyMap_newFace A i n hi p)).symm))

include n hi in
theorem bodyDiskChange_boundary :
    bodyDiskChange A i a ha '' bodyBoundarySet A i = bodyBoundarySet A i := by
  rw [← boundaryBodyMap_range A i n hi]
  calc
    _ = range (fun z => bodyDiskChange A i a ha (boundaryBodyMap A i n hi z)) :=
      (range_comp _ _).symm
    _ = range (fun z => boundaryBodyMap A i n hi (boundaryDiskChange A n a ha z)) :=
      congrArg range (funext (fun z => (bodyDiskChange_boundaryMap A i a ha n hi z).symm))
    _ = range (boundaryBodyMap A i n hi) :=
      (boundaryDiskChange A n a ha).surjective.range_comp _

end Wikipedia.SmoothSixDPoincare.FramedSurgery
