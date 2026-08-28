import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyEquiv
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBaseChangeBody

/-!
# Extend an exact smooth boundary/body equivalence by a matching whole handle

The extension retains the old body map, every whole-handle coordinate,
and the exact commuting boundary map. Both new native smooth atlases can
be constructed from the original smooth boundary manifolds.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyEquiv

open PuncturedHandle FramedSurgery

variable {E F G H X X' Y Y' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace H X]
  [TopologicalSpace X'] [T2Space X'] [CompactSpace X'] [ChartedSpace H X']
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y']
  {i : C(X, Y)} {i' : C(X', Y')}
  (e : SmoothBoundaryBodyEquiv (J := J) i i')
  (hi : IsClosedEmbedding i) (hi' : IsClosedEmbedding i')
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (A' : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X')
  (hface : ∀ z, e.boundary (A.map z) = A'.map z)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]
  (P : SmoothBoundaryData A n) (Q : SmoothBoundaryData A' n)

def attach :
    letI := P.charted
    letI := Q.charted
    SmoothBoundaryBodyEquiv (J := J) (boundaryBodyMap A i n hi) (boundaryBodyMap A' i' n hi') := by
  let _ := P.charted
  let _ := Q.charted
  exact {
    body := baseChangeBody A A' i i' e.boundary.toHomeomorph hface e.body e.boundary_point
    boundary := baseChangeDiffeomorph A A' n e.boundary hface P Q
    boundary_point := fun z =>
      (baseChangeDiffeomorph_bodyMap A A' i i' e.body hi hi' n
        e.boundary hface e.boundary_point P Q z).symm }

theorem attach_body :
    letI := P.charted
    letI := Q.charted
    (e.attach hi hi' A A' hface n P Q).body =
      baseChangeBody A A' i i' e.boundary.toHomeomorph hface e.body e.boundary_point := rfl

theorem attach_old (y : Y) :
    letI := P.charted
    letI := Q.charted
    (e.attach hi hi' A A' hface n P Q).body (FaceAttachment.oldMap (bodyFaceMap A i) y) =
      FaceAttachment.oldMap (bodyFaceMap A' i') (e.body y) := by
  let _ := P.charted
  let _ := Q.charted
  exact baseChangeBody_old A A' i i' e.boundary.toHomeomorph hface e.body e.boundary_point y

theorem attach_handle (k : WholeHandle E F) :
    letI := P.charted
    letI := Q.charted
    (e.attach hi hi' A A' hface n P Q).body (FaceAttachment.handleMap (bodyFaceMap A i) k) =
      FaceAttachment.handleMap (bodyFaceMap A' i') k := by
  let _ := P.charted
  let _ := Q.charted
  exact baseChangeBody_handle A A' i i' e.boundary.toHomeomorph hface e.body e.boundary_point k

theorem attach_boundary_toHomeomorph :
    letI := P.charted
    letI := Q.charted
    (e.attach hi hi' A A' hface n P Q).boundary.toHomeomorph =
      baseChangeBoundary A A' n e.boundary.toHomeomorph hface := rfl

theorem exists_attach [FiniteDimensional ℝ G] [J.Boundaryless]
    [IsManifold J ∞ X] [IsManifold J ∞ X'] :
    ∃ (P : SmoothBoundaryData A n) (Q : SmoothBoundaryData A' n),
      letI := P.charted
      letI := Q.charted
      ∃ f : SmoothBoundaryBodyEquiv (J := J)
          (boundaryBodyMap A i n hi) (boundaryBodyMap A' i' n hi'),
        f.body =
          baseChangeBody A A' i i' e.boundary.toHomeomorph hface e.body e.boundary_point := by
  obtain ⟨P⟩ := nonempty_smoothBoundaryData A n
  obtain ⟨Q⟩ := nonempty_smoothBoundaryData A' n
  exact ⟨P, Q, e.attach hi hi' A A' hface n P Q, rfl⟩

theorem exists_attach_postcompose [FiniteDimensional ℝ G] [J.Boundaryless]
    [IsManifold J ∞ X] [IsManifold J ∞ X'] :
    ∃ (P : SmoothBoundaryData A n) (Q : SmoothBoundaryData (A.postcompose e.boundary) n),
      letI := P.charted
      letI := Q.charted
      ∃ f : SmoothBoundaryBodyEquiv (J := J) (boundaryBodyMap A i n hi)
          (boundaryBodyMap (A.postcompose e.boundary) i' n hi'),
        (∀ y, f.body (FaceAttachment.oldMap (bodyFaceMap A i) y) =
          FaceAttachment.oldMap (bodyFaceMap (A.postcompose e.boundary) i') (e.body y)) ∧
        (∀ k, f.body (FaceAttachment.handleMap (bodyFaceMap A i) k) =
          FaceAttachment.handleMap (bodyFaceMap (A.postcompose e.boundary) i') k) ∧
        f.boundary.toHomeomorph = baseChangeBoundary A (A.postcompose e.boundary) n
          e.boundary.toHomeomorph (fun _ => rfl) := by
  obtain ⟨P⟩ := nonempty_smoothBoundaryData A n
  obtain ⟨Q⟩ := nonempty_smoothBoundaryData (A.postcompose e.boundary) n
  refine ⟨P, Q, e.attach hi hi' A (A.postcompose e.boundary) (fun _ => rfl) n P Q, ?_⟩
  exact ⟨e.attach_old hi hi' A (A.postcompose e.boundary) (fun _ => rfl) n P Q,
    e.attach_handle hi hi' A (A.postcompose e.boundary) (fun _ => rfl) n P Q, rfl⟩

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyEquiv
