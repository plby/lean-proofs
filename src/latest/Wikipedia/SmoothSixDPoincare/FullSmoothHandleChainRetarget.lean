import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

/-! # Exact terminal coordinate changes for full smooth handle chains -/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} {dimension : ℕ}
  {U V : SmoothBoundaryBody J} {k : ℕ}

def retarget (c : FullSmoothHandleChain J dimension U V k) :
    {W : SmoothBoundaryBody J} → SmoothBoundaryBody.Equiv V W →
      FullSmoothHandleChain J dimension U W k := by
  induction c with
  | nil r => intro W e; exact .nil (r.trans e)
  | birth D hdim r c ih => intro W e; exact .birth D hdim r (ih e)
  | interior A P hdim r c ih => intro W e; exact .interior A P hdim r (ih e)
  | cap j hj hopen hdim r c ih => intro W e; exact .cap j hj hopen hdim r (ih e)

def retargetPieces (c : FullSmoothHandleChain J dimension U V k) :
    {W : SmoothBoundaryBody J} → (e : SmoothBoundaryBody.Equiv V W) →
      c.pieces ≃ₜ (c.retarget e).pieces := by
  induction c with
  | nil r => intro W e; exact Homeomorph.refl _
  | birth D hdim r c ih => intro W e; exact (Homeomorph.refl _).sumCongr (ih e)
  | interior A P hdim r c ih => intro W e; exact (Homeomorph.refl _).sumCongr (ih e)
  | cap j hj hopen hdim r c ih => intro W e; exact (Homeomorph.refl _).sumCongr (ih e)

variable {W : SmoothBoundaryBody J}

theorem retarget_sourceMap (c : FullSmoothHandleChain J dimension U V k)
    (e : SmoothBoundaryBody.Equiv V W) (x : U.body) :
    (c.retarget e).sourceMap x = e.body (c.sourceMap x) := by
  induction c with
  | nil r => rfl
  | birth D hdim r c ih => exact ih e (r.body (Sum.inl x))
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P hdim r c ih =>
      exact ih e (r.body (FaceAttachment.oldMap (FramedSurgery.bodyFaceMap A U.inclusion) x))
  | @cap U V W k N _ _ _ j hj hopen hdim r c ih =>
      exact ih e (r.body (FaceAttachment.oldMap (U.capFaceMap j) x))

theorem retarget_piecesMap (c : FullSmoothHandleChain J dimension U V k)
    (e : SmoothBoundaryBody.Equiv V W) (z : c.pieces) :
    (c.retarget e).piecesMap (c.retargetPieces e z) = e.body (c.piecesMap z) := by
  induction c with
  | nil r => exact PEmpty.elim z
  | birth D hdim r c ih =>
      cases z with
      | inl z => exact c.retarget_sourceMap e (r.body (Sum.inr z))
      | inr z => exact ih e z
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P hdim r c ih =>
      cases z with
      | inl z =>
          exact c.retarget_sourceMap e
            (r.body (FaceAttachment.handleMap (FramedSurgery.bodyFaceMap A U.inclusion) z))
      | inr z => exact ih e z
  | @cap U V W k N _ _ _ j hj hopen hdim r c ih =>
      cases z with
      | inl z => exact c.retarget_sourceMap e (r.body (FaceAttachment.handleMap (U.capFaceMap j) z))
      | inr z => exact ih e z

theorem retarget_indices (c : FullSmoothHandleChain J dimension U V k)
    (e : SmoothBoundaryBody.Equiv V W) : (c.retarget e).indices = c.indices := by
  induction c with
  | nil r => rfl
  | birth D hdim r c ih => exact congrArg (List.cons 0) (ih e)
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P hdim r c ih =>
      exact congrArg (List.cons (Module.finrank ℝ E)) (ih e)
  | @cap U V W k N _ _ _ j hj hopen hdim r c ih =>
      exact congrArg (List.cons (Module.finrank ℝ N)) (ih e)

end Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain
