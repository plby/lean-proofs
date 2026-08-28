import Wikipedia.SmoothSixDPoincare.SmoothHandleChain
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryDisk
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodySum
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCap
import Wikipedia.SmoothSixDPoincare.EmptyFaceAttachment

/-!
# Finite smooth-boundary handle chains including both extreme indices

Births use a body with actual whole-disk coordinates. Caps attach an actual
disk along an entire open-and-closed sphere component. Interior steps keep
the original framed-face data. All three constructors record the actual
piece dimension, and forget to genuine whole-piece attachment quotients.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  (J : ModelWithCorners ℝ G H) (dimension : ℕ)

inductive FullSmoothHandleChain : SmoothBoundaryBody J → SmoothBoundaryBody J → ℕ → Type 1
  | nil {U V : SmoothBoundaryBody J} (r : SmoothBoundaryBody.Equiv U V) :
      FullSmoothHandleChain U V 0
  | birth {U V W : SmoothBoundaryBody J} {k : ℕ}
      {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
      (D : SmoothBoundaryDisk J N) (hdim : Module.finrank ℝ N = dimension)
      (r : SmoothBoundaryBody.Equiv (U.sum D.space) V)
      (tail : FullSmoothHandleChain V W k) : FullSmoothHandleChain U W (k + 1)
  | interior {U V W : SmoothBoundaryBody J} {k : ℕ}
      {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      {m n : ℕ} [Fact (Module.finrank ℝ E = m + 1)] [Fact (Module.finrank ℝ F = n + 1)]
      (A : SmoothClosedFace (𝓡 m) J (PuncturedHandle.UnitSphere E) F U.boundary)
      (P : FramedSurgery.SmoothBoundaryData A n)
      (hdim : Module.finrank ℝ E + Module.finrank ℝ F = dimension)
      (r : SmoothBoundaryBody.Equiv (U.attach A n P) V)
      (tail : FullSmoothHandleChain V W k) : FullSmoothHandleChain U W (k + 1)
  | cap {U V W : SmoothBoundaryBody J} {k : ℕ}
      {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
      (j : C(PuncturedHandle.UnitSphere N, U.boundary)) (hj : IsClosedEmbedding j)
      (hopen : IsOpen (range j)) (hdim : Module.finrank ℝ N = dimension)
      (r : SmoothBoundaryBody.Equiv (U.cap j hj hopen) V)
      (tail : FullSmoothHandleChain V W k) : FullSmoothHandleChain U W (k + 1)

namespace FullSmoothHandleChain

variable {J dimension} {U V W : SmoothBoundaryBody J} {k : ℕ}

def birthFaceMap (U D : SmoothBoundaryBody J) : C((∅ : Set D.body), U.body) :=
  ⟨fun x => False.elim x.property, by fun_prop⟩

def toAttachmentChain (c : FullSmoothHandleChain J dimension U V k) :
    FaceAttachment.Chain U.body V.body k := by
  induction c with
  | nil r => exact .nil r.body
  | birth D _ r _ ih =>
      exact .cons D.space.body ∅ (birthFaceMap _ D.space)
        ((FaceAttachment.emptyFaceHomeomorph (birthFaceMap _ D.space)).trans r.body) ih
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P _ r _ ih =>
      exact .cons (TopCat.of (FramedSurgery.WholeHandle E F))
        (FramedSurgery.wholeAttachingFace E F) (FramedSurgery.bodyFaceMap A U.inclusion) r.body ih
  | @cap U V W k N _ _ _ j hj hopen _ r _ ih =>
      exact .cons (TopCat.of (MorseHandle.UnitDisk N)) (DiskCap.boundary N)
        (U.capFaceMap j) r.body ih

def sourceMap (c : FullSmoothHandleChain J dimension U V k) : C(U.body, V.body) :=
  c.toAttachmentChain.sourceMap

def pieces (c : FullSmoothHandleChain J dimension U V k) : TopCat.{0} :=
  c.toAttachmentChain.pieces

def piecesMap (c : FullSmoothHandleChain J dimension U V k) : C(c.pieces, V.body) :=
  c.toAttachmentChain.piecesMap

def indices (c : FullSmoothHandleChain J dimension U V k) : List ℕ := by
  induction c with
  | nil _ => exact []
  | birth _ _ _ _ ih => exact 0 :: ih
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P _ r _ ih =>
      exact Module.finrank ℝ E :: ih
  | @cap U V W k N _ _ _ j hj hopen _ r _ ih => exact Module.finrank ℝ N :: ih

theorem indices_length (c : FullSmoothHandleChain J dimension U V k) : c.indices.length = k := by
  induction c with
  | nil _ => rfl
  | birth _ _ _ _ ih => exact congrArg Nat.succ ih
  | interior _ _ _ _ _ ih => exact congrArg Nat.succ ih
  | cap _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

theorem indices_le_dimension (c : FullSmoothHandleChain J dimension U V k) :
    ∀ a ∈ c.indices, a ≤ dimension := by
  induction c with
  | nil _ => simp only [indices, List.not_mem_nil, false_implies, implies_true]
  | birth D hdim r tail ih =>
      intro a ha
      rcases List.mem_cons.mp ha with h | h
      · exact h ▸ Nat.zero_le dimension
      · exact ih a h
  | @interior U V W k E F _ _ _ _ _ _ m n _ _ A P hdim r tail ih =>
      intro a ha
      rcases List.mem_cons.mp ha with h | h
      · omega
      · exact ih a h
  | @cap U V W k N _ _ _ j hj hopen hdim r tail ih =>
      intro a ha
      rcases List.mem_cons.mp ha with h | h
      · exact h ▸ hdim.le
      · exact ih a h

end FullSmoothHandleChain
end Wikipedia.SmoothSixDPoincare
