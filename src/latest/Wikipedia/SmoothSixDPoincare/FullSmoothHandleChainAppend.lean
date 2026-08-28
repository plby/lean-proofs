import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainRebase

/-!
# Compose full finite smooth chains without discarding their piece maps

The terminal equivalence of the initial chain transports the first step
of the tail. Births, caps, and interior handles all retain their actual
whole-piece coordinates and index lists.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  {dimension : ℕ} {U V : SmoothBoundaryBody J} {k : ℕ}

def append (c : FullSmoothHandleChain J dimension U V k) :
    {W : SmoothBoundaryBody J} → {l : ℕ} → FullSmoothHandleChain J dimension V W l →
      FullSmoothHandleChain J dimension U W (l + k) := by
  induction c with
  | nil r => intro W l tail; exact tail.rebase r.symm
  | birth D hdim r c ih => intro W l tail; exact .birth D hdim r (ih tail)
  | interior A P hdim r c ih => intro W l tail; exact .interior A P hdim r (ih tail)
  | cap j hj hopen hdim r c ih => intro W l tail; exact .cap j hj hopen hdim r (ih tail)

def appendOldPiece (c : FullSmoothHandleChain J dimension U V k) :
    {W : SmoothBoundaryBody J} → {l : ℕ} → (tail : FullSmoothHandleChain J dimension V W l) →
      c.pieces → (c.append tail).pieces := by
  induction c with
  | nil r => intro W l tail; exact PEmpty.elim
  | birth D hdim r c ih => intro W l tail; exact Sum.map id (ih tail)
  | interior A P hdim r c ih => intro W l tail; exact Sum.map id (ih tail)
  | cap j hj hopen hdim r c ih => intro W l tail; exact Sum.map id (ih tail)

def appendTailPiece (c : FullSmoothHandleChain J dimension U V k) :
    {W : SmoothBoundaryBody J} → {l : ℕ} → (tail : FullSmoothHandleChain J dimension V W l) →
      tail.pieces → (c.append tail).pieces := by
  induction c with
  | nil r => intro W l tail z; exact tail.rebasePieces r.symm z
  | birth D hdim r c ih => intro W l tail; exact Sum.inr ∘ ih tail
  | interior A P hdim r c ih => intro W l tail; exact Sum.inr ∘ ih tail
  | cap j hj hopen hdim r c ih => intro W l tail; exact Sum.inr ∘ ih tail

variable {W : SmoothBoundaryBody J} {l : ℕ}

theorem append_sourceMap (c : FullSmoothHandleChain J dimension U V k)
    (tail : FullSmoothHandleChain J dimension V W l) (x : U.body) :
    (c.append tail).sourceMap x = tail.sourceMap (c.sourceMap x) := by
  induction c with
  | nil r => exact tail.rebase_sourceMap r.symm x
  | birth D hdim r c ih => exact ih tail (r.body (Sum.inl x))
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P hdim r c ih =>
      exact ih tail (r.body (FaceAttachment.oldMap (FramedSurgery.bodyFaceMap A U.inclusion) x))
  | @cap U V W k N _ _ _ j hj hopen hdim r c ih =>
      exact ih tail (r.body (FaceAttachment.oldMap (U.capFaceMap j) x))

theorem appendOldPiece_map (c : FullSmoothHandleChain J dimension U V k)
    (tail : FullSmoothHandleChain J dimension V W l) (z : c.pieces) :
    (c.append tail).piecesMap (c.appendOldPiece tail z) = tail.sourceMap (c.piecesMap z) := by
  induction c with
  | nil r => exact PEmpty.elim z
  | birth D hdim r c ih =>
      cases z with
      | inl z => exact c.append_sourceMap tail (r.body (Sum.inr z))
      | inr z => exact ih tail z
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P hdim r c ih =>
      cases z with
      | inl z =>
          exact c.append_sourceMap tail
            (r.body (FaceAttachment.handleMap (FramedSurgery.bodyFaceMap A U.inclusion) z))
      | inr z => exact ih tail z
  | @cap U V W k N _ _ _ j hj hopen hdim r c ih =>
      cases z with
      | inl z =>
          exact c.append_sourceMap tail (r.body (FaceAttachment.handleMap (U.capFaceMap j) z))
      | inr z => exact ih tail z

theorem appendTailPiece_map (c : FullSmoothHandleChain J dimension U V k)
    (tail : FullSmoothHandleChain J dimension V W l) (z : tail.pieces) :
    (c.append tail).piecesMap (c.appendTailPiece tail z) = tail.piecesMap z := by
  induction c with
  | nil r => exact tail.rebase_piecesMap r.symm z
  | birth D hdim r c ih => exact ih tail z
  | interior A P hdim r c ih => exact ih tail z
  | cap j hj hopen hdim r c ih => exact ih tail z

theorem append_indices (c : FullSmoothHandleChain J dimension U V k)
    (tail : FullSmoothHandleChain J dimension V W l) :
    (c.append tail).indices = c.indices ++ tail.indices := by
  induction c with
  | nil r => exact tail.rebase_indices r.symm
  | birth D hdim r c ih => exact congrArg (List.cons 0) (ih tail)
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P hdim r c ih =>
      exact congrArg (List.cons (Module.finrank ℝ E)) (ih tail)
  | @cap U V W k N _ _ _ j hj hopen hdim r c ih =>
      exact congrArg (List.cons (Module.finrank ℝ N)) (ih tail)

end Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain
