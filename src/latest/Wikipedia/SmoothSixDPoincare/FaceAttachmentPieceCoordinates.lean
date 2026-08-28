import Wikipedia.SmoothSixDPoincare.FaceAttachment

/-! # Change whole-piece coordinates and their exact attaching-face coordinates -/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K L X : Type*} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
  {B : Set K} {C : Set L} (b : C(B, X)) (c : C(C, X))
  (q : K ≃ₜ L) (hface : ∀ k, q k ∈ C ↔ k ∈ B)
  (hpoint : ∀ u : B, c ⟨q u.val, (hface u.val).mpr u.property⟩ = b u)

def pieceCoordinates : Space b ≃ₜ Space c := by
  apply Homeomorph.Quot.congr ((Homeomorph.refl X).sumCongr q)
  rintro (x | k) (y | l)
  · exact Iff.rfl
  · change (∃ hl : l ∈ B, x = b ⟨l, hl⟩) ↔ ∃ hl : q l ∈ C, x = c ⟨q l, hl⟩
    constructor
    · rintro ⟨hl, hx⟩
      exact ⟨(hface l).mpr hl, hx.trans (hpoint ⟨l, hl⟩).symm⟩
    · rintro ⟨hl, hx⟩
      exact ⟨(hface l).mp hl, hx.trans (hpoint ⟨l, (hface l).mp hl⟩)⟩
  · exact Iff.rfl
  · exact Iff.rfl

theorem pieceCoordinates_old (x : X) :
    pieceCoordinates b c q hface hpoint (oldMap b x) = oldMap c x := rfl

theorem pieceCoordinates_handle (k : K) :
    pieceCoordinates b c q hface hpoint (handleMap b k) = handleMap c (q k) := rfl

theorem pieceCoordinates_symm_old (x : X) :
    (pieceCoordinates b c q hface hpoint).symm (oldMap c x) = oldMap b x := rfl

theorem pieceCoordinates_symm_handle (l : L) :
    (pieceCoordinates b c q hface hpoint).symm (handleMap c l) = handleMap b (q.symm l) := rfl

end Wikipedia.SmoothSixDPoincare.FaceAttachment
