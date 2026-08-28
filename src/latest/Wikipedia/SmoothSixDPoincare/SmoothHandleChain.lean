import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyAttachmentEquiv
import Wikipedia.SmoothSixDPoincare.FiniteFaceAttachment

/-!
# Finite framed attachment chains with exact smooth boundary realizations

Every step records its original smooth face, constructed boundary atlas,
and commuting body/boundary realization. Forgetting only the boundary
data gives a genuine finite whole-piece attachment chain, retaining all
old-body and whole-handle maps.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  (J : ModelWithCorners ℝ G H)

inductive SmoothHandleChain : SmoothBoundaryBody J → SmoothBoundaryBody J → ℕ → Type 1
  | nil {U V : SmoothBoundaryBody J} (r : SmoothBoundaryBody.Equiv U V) :
      SmoothHandleChain U V 0
  | cons {U V W : SmoothBoundaryBody J} {k : ℕ}
      {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      {m n : ℕ} [Fact (Module.finrank ℝ E = m + 1)] [Fact (Module.finrank ℝ F = n + 1)]
      (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F U.boundary)
      (P : FramedSurgery.SmoothBoundaryData A n)
      (r : SmoothBoundaryBody.Equiv (U.attach A n P) V)
      (tail : SmoothHandleChain V W k) : SmoothHandleChain U W (k + 1)

namespace SmoothHandleChain

variable {J} {U V W : SmoothBoundaryBody J} {k : ℕ}

def toAttachmentChain (c : SmoothHandleChain J U V k) :
    FaceAttachment.Chain U.body V.body k := by
  induction c with
  | nil r => exact .nil r.body
  | @cons U V W k E F _ _ _ _ _ _ m n _ _ A P r tail ih =>
      exact .cons (TopCat.of (FramedSurgery.WholeHandle E F))
        (FramedSurgery.wholeAttachingFace E F) (FramedSurgery.bodyFaceMap A U.inclusion) r.body ih

def sourceMap (c : SmoothHandleChain J U V k) : C(U.body, V.body) :=
  c.toAttachmentChain.sourceMap

def pieces (c : SmoothHandleChain J U V k) : TopCat.{0} := c.toAttachmentChain.pieces

def piecesMap (c : SmoothHandleChain J U V k) : C(c.pieces, V.body) :=
  c.toAttachmentChain.piecesMap

theorem sourceMap_nil (r : SmoothBoundaryBody.Equiv U V) (x : U.body) :
    (nil r).sourceMap x = r.body x := rfl

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m n : ℕ} [Fact (Module.finrank ℝ E = m + 1)] [Fact (Module.finrank ℝ F = n + 1)]
  (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F U.boundary)
  (P : FramedSurgery.SmoothBoundaryData A n)
  (r : SmoothBoundaryBody.Equiv (U.attach A n P) V) (tail : SmoothHandleChain J V W k)

theorem sourceMap_cons (x : U.body) :
    (cons A P r tail).sourceMap x =
      tail.sourceMap (r.body (FaceAttachment.oldMap (FramedSurgery.bodyFaceMap A U.inclusion) x)) :=
  rfl

theorem piecesMap_cons_handle (z : FramedSurgery.WholeHandle E F) :
    (cons A P r tail).piecesMap (Sum.inl z) =
      tail.sourceMap (r.body
        (FaceAttachment.handleMap (FramedSurgery.bodyFaceMap A U.inclusion) z)) :=
  rfl

theorem piecesMap_cons_tail (z : tail.pieces) :
    (cons A P r tail).piecesMap (Sum.inr z) = tail.piecesMap z := rfl

end SmoothHandleChain

end Wikipedia.SmoothSixDPoincare
