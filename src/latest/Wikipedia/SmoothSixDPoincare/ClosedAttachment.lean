import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Recognizing a closed attachment inside an ambient space

If an embedded compact piece meets a compact subspace in precisely a
specified boundary subset, their actual union is homeomorphic to the
quotient obtained by attaching that piece along its boundary map.
-/

noncomputable section

open Set

namespace Wikipedia.SmoothSixDPoincare.ClosedAttachment

variable {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
  (A : Set M) (B : Set K) (h : C(K, M))

/-- Attach precisely the designated boundary points to their images in the old subspace. -/
def Rel : A ⊕ K → A ⊕ K → Prop
  | .inl a, .inr k => k ∈ B ∧ (a : M) = h k
  | _, _ => False

abbrev Space := Quot (Rel A B h)

def sumMap : A ⊕ K → ↥(A ∪ range h)
  | .inl a => ⟨a, Or.inl a.2⟩
  | .inr k => ⟨h k, Or.inr ⟨k, rfl⟩⟩

theorem continuous_sumMap : Continuous (sumMap A h) :=
  continuous_sum_dom.mpr
    ⟨continuous_subtype_val.subtype_mk _, h.continuous.subtype_mk _⟩

theorem sumMap_respects (x y : A ⊕ K) (hxy : Rel A B h x y) :
    sumMap A h x = sumMap A h y := by
  cases x with
  | inl a =>
    cases y with
    | inl a' => exact hxy.elim
    | inr k => exact Subtype.ext hxy.2
  | inr k => cases y <;> exact hxy.elim

def quotientMap : Space A B h → ↥(A ∪ range h) :=
  Quot.lift (sumMap A h) (sumMap_respects A B h)

theorem continuous_quotientMap : Continuous (quotientMap A B h) :=
  continuous_quot_lift (sumMap_respects A B h) (continuous_sumMap A h)

theorem quotientMap_injective (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) : Function.Injective (quotientMap A B h) := by
  intro q r
  induction q using Quot.inductionOn with
  | _ x =>
    induction r using Quot.inductionOn with
    | _ y =>
      intro heq
      have heq' := congrArg Subtype.val heq
      cases x with
      | inl a =>
        cases y with
        | inl a' =>
          have haa : a = a' := Subtype.ext heq'
          subst a'
          rfl
        | inr k =>
          change (a : M) = h k at heq'
          have hk : h k ∈ A := by rw [← heq']; exact a.2
          exact Quot.sound ⟨(hface k).mp hk, heq'⟩
      | inr k =>
        cases y with
        | inl a =>
          change h k = (a : M) at heq'
          have hk : h k ∈ A := by rw [heq']; exact a.2
          exact (Quot.sound (r := Rel A B h) (a := .inl a) (b := .inr k)
            ⟨(hface k).mp hk, heq'.symm⟩).symm
        | inr k' =>
          have hkk : k = k' := hinj heq'
          subst k'
          rfl

theorem quotientMap_surjective : Function.Surjective (quotientMap A B h) := by
  rintro ⟨x, hx | ⟨k, rfl⟩⟩
  · exact ⟨Quot.mk _ (.inl ⟨x, hx⟩), rfl⟩
  · exact ⟨Quot.mk _ (.inr k), rfl⟩

/-- The actual compact union is exactly the prescribed boundary-attachment quotient. -/
def unionHomeomorph [CompactSpace K] [T2Space M] (hA : IsCompact A)
    (hinj : Function.Injective h) (hface : ∀ k, h k ∈ A ↔ k ∈ B) :
    Space A B h ≃ₜ ↥(A ∪ range h) := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (quotientMap A B h)
      ⟨quotientMap_injective A B h hinj hface, quotientMap_surjective A B h⟩)
    (continuous_quotientMap A B h)

end Wikipedia.SmoothSixDPoincare.ClosedAttachment
