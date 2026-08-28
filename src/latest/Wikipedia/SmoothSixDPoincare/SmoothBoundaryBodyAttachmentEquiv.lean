import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

/-!
# Exact extension of a bundled smooth boundary/body equivalence

The original one-handle extension supplies an equivalence between the
bundled attachments. It changes only old-body coordinates and retains
every whole-handle parameter, in both directions.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} {U V : SmoothBoundaryBody J} (e : Equiv U V)
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F U.boundary)
  (A' : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F V.boundary)
  (hface : ∀ z, e.boundary (A.map z) = A'.map z)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]
  (P : FramedSurgery.SmoothBoundaryData A n) (Q : FramedSurgery.SmoothBoundaryData A' n)

def attachEquiv : Equiv (U.attach A n P) (V.attach A' n Q) :=
  SmoothBoundaryBodyEquiv.attach e U.closedEmbedding V.closedEmbedding A A' hface n P Q

theorem attachEquiv_old (y : U.body) :
    (attachEquiv e A A' hface n P Q).body
      (FaceAttachment.oldMap (FramedSurgery.bodyFaceMap A U.inclusion) y) =
      FaceAttachment.oldMap (FramedSurgery.bodyFaceMap A' V.inclusion) (e.body y) :=
  e.attach_old U.closedEmbedding V.closedEmbedding A A' hface n P Q y

theorem attachEquiv_handle (k : FramedSurgery.WholeHandle E F) :
    (attachEquiv e A A' hface n P Q).body
      (FaceAttachment.handleMap (FramedSurgery.bodyFaceMap A U.inclusion) k) =
      FaceAttachment.handleMap (FramedSurgery.bodyFaceMap A' V.inclusion) k :=
  e.attach_handle U.closedEmbedding V.closedEmbedding A A' hface n P Q k

theorem attachEquiv_symm_old (y : V.body) :
    (attachEquiv e A A' hface n P Q).body.symm
      (FaceAttachment.oldMap (FramedSurgery.bodyFaceMap A' V.inclusion) y) =
      FaceAttachment.oldMap (FramedSurgery.bodyFaceMap A U.inclusion) (e.body.symm y) := by
  have h := attachEquiv_old e A A' hface n P Q (e.body.symm y)
  rw [Homeomorph.apply_symm_apply] at h
  have hi := congrArg (attachEquiv e A A' hface n P Q).body.symm h
  exact hi.symm.trans ((attachEquiv e A A' hface n P Q).body.symm_apply_apply _)

theorem attachEquiv_symm_handle (k : FramedSurgery.WholeHandle E F) :
    (attachEquiv e A A' hface n P Q).body.symm
      (FaceAttachment.handleMap (FramedSurgery.bodyFaceMap A' V.inclusion) k) =
      FaceAttachment.handleMap (FramedSurgery.bodyFaceMap A U.inclusion) k := by
  have h := attachEquiv_handle e A A' hface n P Q k
  have hi := congrArg (attachEquiv e A A' hface n P Q).body.symm h
  exact hi.symm.trans ((attachEquiv e A A' hface n P Q).body.symm_apply_apply _)

theorem attachEquiv_boundary :
    (attachEquiv e A A' hface n P Q).boundary.toHomeomorph =
      FramedSurgery.baseChangeBoundary A A' n e.boundary.toHomeomorph hface := rfl

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
