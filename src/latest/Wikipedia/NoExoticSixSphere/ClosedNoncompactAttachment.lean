import Wikipedia.SmoothSixDPoincare.ClosedAttachment

/-!
# Recognizing the actual attachment to a closed, possibly noncompact subspace

The old ambient subspace need only be closed. If the attaching map is closed,
the sum map and its induced quotient map are closed. Exact intersection at
the designated face then identifies the quotient with the actual union.
No compactness of the old subspace or of the attaching domain is required.
-/

noncomputable section

open Set

namespace Wikipedia.SmoothSixDPoincare.ClosedAttachment

variable {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
  (A : Set M) (B : Set K) (h : C(K, M))

theorem isClosedMap_sumMap (hA : IsClosed A) (hh : IsClosedMap h) :
    IsClosedMap (sumMap A h) :=
  isClosedMap_sum.mpr
    ⟨hA.isClosedMap_subtype_val.subtype_mk (fun a ↦ Or.inl a.property),
      hh.subtype_mk (fun k ↦ Or.inr ⟨k, rfl⟩)⟩

theorem isClosedMap_quotientMap (hA : IsClosed A) (hh : IsClosedMap h) :
    IsClosedMap (quotientMap A B h) := by
  intro S hS
  have hc := isClosedMap_sumMap A h hA hh _ (hS.preimage continuous_quot_mk)
  have he : sumMap A h '' ((Quot.mk (Rel A B h)) ⁻¹' S) = quotientMap A B h '' S := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Quot.mk (Rel A B h) p, hp, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨p, rfl⟩ := Quot.mk_surjective q
      exact ⟨p, hq, rfl⟩
  exact he ▸ hc

def unionHomeomorphOfIsClosed (hA : IsClosed A) (hh : IsClosedMap h)
    (hinj : Function.Injective h) (hface : ∀ k, h k ∈ A ↔ k ∈ B) :
    Space A B h ≃ₜ ↥(A ∪ range h) := by
  let e := Equiv.ofBijective (quotientMap A B h)
    ⟨quotientMap_injective A B h hinj hface, quotientMap_surjective A B h⟩
  exact e.toHomeomorphOfContinuousClosed (continuous_quotientMap A B h)
    (isClosedMap_quotientMap A B h hA hh)

end Wikipedia.SmoothSixDPoincare.ClosedAttachment
