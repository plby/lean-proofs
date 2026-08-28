import Wikipedia.SmoothSixDPoincare.CompactClosedQuotient
import Wikipedia.SmoothSixDPoincare.FaceAttachmentExact

/-!
# Compact Hausdorff whole-piece attachments

For a compact Hausdorff old space and whole piece, attachment along a closed
face with an injective continuous attaching map is Hausdorff. Both original
piece maps are closed embeddings in the original quotient topology.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K X : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {B : Set K} (b : C(B, X))

theorem isClosed_exactRel (hB : IsClosed B) :
    IsClosed {p : (X ⊕ K) × (X ⊕ K) | ExactRel b p.1 p.2} := by
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let dX : X → (X ⊕ K) × (X ⊕ K) := fun x => (.inl x, .inl x)
  let dK : K → (X ⊕ K) × (X ⊕ K) := fun k => (.inr k, .inr k)
  let f : B → (X ⊕ K) × (X ⊕ K) := fun u => (.inl (b u), .inr u.val)
  let g : B → (X ⊕ K) × (X ⊕ K) := fun u => (.inr u.val, .inl (b u))
  have hdX : Continuous dX := continuous_inl.prodMk continuous_inl
  have hdK : Continuous dK := continuous_inr.prodMk continuous_inr
  have hf : Continuous f := (continuous_inl.comp b.continuous).prodMk
    (continuous_inr.comp continuous_subtype_val)
  have hg : Continuous g := (continuous_inr.comp continuous_subtype_val).prodMk
    (continuous_inl.comp b.continuous)
  have heq : {p : (X ⊕ K) × (X ⊕ K) | ExactRel b p.1 p.2} =
      (range dX ∪ range dK) ∪ (range f ∪ range g) := by
    ext p
    rcases p with ⟨x | k, y | l⟩
    · simp [ExactRel, dX, dK, f, g, eq_comm]
    · simp [ExactRel, dX, dK, f, g]
    · simp [ExactRel, dX, dK, f, g, and_comm]
    · simp [ExactRel, dX, dK, f, g, eq_comm]
  rw [heq]
  exact ((isCompact_range hdX).union (isCompact_range hdK)).union
    ((isCompact_range hf).union (isCompact_range hg)) |>.isClosed

theorem t2Space (hB : IsClosed B) (hb : Injective b) : T2Space (Space b) := by
  apply CompactClosedQuotient.t2Space isQuotientMap_quot_mk
  convert isClosed_exactRel b hB using 1
  ext p
  exact quotient_eq_iff b hb p.1 p.2

theorem oldMap_isClosedEmbedding (hB : IsClosed B) (hb : Injective b) :
    IsClosedEmbedding (oldMap b) := by
  let _ : T2Space (Space b) := t2Space b hB hb
  exact (oldMap b).continuous.isClosedEmbedding (fun x y h => (oldMap_eq_oldMap b hb x y).mp h)

theorem handleMap_isClosedEmbedding (hB : IsClosed B) (hb : Injective b) :
    IsClosedEmbedding (handleMap b) := by
  let _ : T2Space (Space b) := t2Space b hB hb
  exact (handleMap b).continuous.isClosedEmbedding
    (fun k l h => (handleMap_eq_handleMap b hb k l).mp h)

end Wikipedia.SmoothSixDPoincare.FaceAttachment
