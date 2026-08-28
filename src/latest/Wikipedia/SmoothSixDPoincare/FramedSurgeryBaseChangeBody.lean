import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothBaseChange
import Wikipedia.SmoothSixDPoincare.CommonBaseAttachmentRealization

/-!
# Smooth boundary changes extend by the original whole-handle coordinates

A commuting change of the old body and boundary induces the literal
whole-attachment homeomorphism. Its boundary restriction is exactly the
native surgery-boundary diffeomorphism already constructed, not merely
another homeomorphism of the same boundary spaces.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X X' Y Y' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}
  [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  [TopologicalSpace X'] [T2Space X'] [ChartedSpace H X']
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (A' : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X')
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y']
  (i : C(X, Y)) (i' : C(X', Y'))
  (e : X ≃ₜ X') (hface : ∀ z, e (A.map z) = A'.map z)
  (b : Y ≃ₜ Y') (hbody : ∀ x, b (i x) = i' (e x))

include hface hbody in
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X] [T2Space X']
    [T2Space Y] [CompactSpace Y] [T2Space Y'] [CompactSpace Y'] in
theorem baseChange_bodyFaceMap :
    b.toHomotopyEquiv.toFun.comp (bodyFaceMap A i) = bodyFaceMap A' i' := by
  ext z
  exact (hbody (A.map (wholeFaceCoordinates E F z))).trans
    (congrArg i' (hface (wholeFaceCoordinates E F z)))

def baseChangeBody : AttachedBody A i ≃ₜ AttachedBody A' i' :=
  (FaceAttachment.baseCongr (bodyFaceMap A i) b).trans
    (FaceAttachment.congrFaceMap (baseChange_bodyFaceMap A A' i i' e hface b hbody))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X] [T2Space X']
    [T2Space Y] [CompactSpace Y] [T2Space Y'] [CompactSpace Y'] in
theorem baseChangeBody_old (y : Y) :
    baseChangeBody A A' i i' e hface b hbody (FaceAttachment.oldMap (bodyFaceMap A i) y) =
      FaceAttachment.oldMap (bodyFaceMap A' i') (b y) :=
  FaceAttachment.congrFaceMap_old (baseChange_bodyFaceMap A A' i i' e hface b hbody) (b y)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space X] [T2Space X']
    [T2Space Y] [CompactSpace Y] [T2Space Y'] [CompactSpace Y'] in
theorem baseChangeBody_handle (k : WholeHandle E F) :
    baseChangeBody A A' i i' e hface b hbody (FaceAttachment.handleMap (bodyFaceMap A i) k) =
      FaceAttachment.handleMap (bodyFaceMap A' i') k :=
  FaceAttachment.congrFaceMap_handle (baseChange_bodyFaceMap A A' i i' e hface b hbody) k

variable [CompactSpace X] [CompactSpace X']
  (hi : IsClosedEmbedding i) (hi' : IsClosedEmbedding i')
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

theorem baseChangeBoundary_bodyMap (z : Boundary A n) :
    boundaryBodyMap A' i' n hi' (baseChangeBoundary A A' n e hface z) =
      baseChangeBody A A' i i' e hface b hbody (boundaryBodyMap A i n hi z) := by
  have hz := exterior_new_face_cover A n
  have hc : z ∈ range (exteriorNewMap A n) ∪ range (closedNewMap A n) :=
    hz.symm ▸ mem_univ z
  rcases hc with ⟨r, rfl⟩ | ⟨p, rfl⟩
  · let x := exteriorToOldPatch A r
    have hx : (baseChangeOldHomeomorph A A' e hface x).val ∉ faceInterior A' :=
      fun h => r.property ((baseChange_mem_faceInterior_iff A A' e hface r.val).mp h)
    exact (congrArg (boundaryBodyMap A' i' n hi')
      (baseChangeBoundary_old A A' n e hface x)).trans
        ((boundaryBodyMap_old_exterior A' i' n hi' (baseChangeOldHomeomorph A A' e hface x)
          hx).trans
          ((congrArg (FaceAttachment.oldMap (bodyFaceMap A' i')) (hbody r.val).symm).trans
            ((baseChangeBody_old A A' i i' e hface b hbody (i r.val)).symm.trans
              (congrArg (baseChangeBody A A' i i' e hface b hbody)
                (boundaryBodyMap_exterior A i n hi r)).symm)))
  · exact (congrArg (boundaryBodyMap A' i' n hi')
      (baseChangeBoundary_closedNewMap A A' n e hface p)).trans
        ((boundaryBodyMap_newFace A' i' n hi' p).trans
          ((baseChangeBody_handle A A' i i' e hface b hbody (wholeNewFace E F p)).symm.trans
            (congrArg (baseChangeBody A A' i i' e hface b hbody)
              (boundaryBodyMap_newFace A i n hi p)).symm))

include hi hi' n in
theorem baseChangeBody_boundary :
    baseChangeBody A A' i i' e hface b hbody '' bodyBoundarySet A i = bodyBoundarySet A' i' := by
  rw [← boundaryBodyMap_range A i n hi]
  calc
    _ = range (fun z => baseChangeBody A A' i i' e hface b hbody (boundaryBodyMap A i n hi z)) :=
      (range_comp _ _).symm
    _ = range (fun z => boundaryBodyMap A' i' n hi' (baseChangeBoundary A A' n e hface z)) :=
      congrArg range (funext (fun z =>
        (baseChangeBoundary_bodyMap A A' i i' e hface b hbody hi hi' n z).symm))
    _ = range (boundaryBodyMap A' i' n hi') :=
      (baseChangeBoundary A A' n e hface).surjective.range_comp _
    _ = bodyBoundarySet A' i' := boundaryBodyMap_range A' i' n hi'

variable (D : Diffeomorph J J X X' ∞) (hD : ∀ z, D (A.map z) = A'.map z)
  (hbodyD : ∀ x, b (i x) = i' (D x))
  (P : SmoothBoundaryData A n) (Q : SmoothBoundaryData A' n)

theorem baseChangeDiffeomorph_bodyMap :
    letI := P.charted
    letI := Q.charted
    ∀ z, boundaryBodyMap A' i' n hi' (baseChangeDiffeomorph A A' n D hD P Q z) =
      baseChangeBody A A' i i' D.toHomeomorph hD b hbodyD (boundaryBodyMap A i n hi z) := by
  let _ := P.charted
  let _ := Q.charted
  exact baseChangeBoundary_bodyMap A A' i i' D.toHomeomorph hD b hbodyD hi hi' n

end Wikipedia.SmoothSixDPoincare.FramedSurgery
