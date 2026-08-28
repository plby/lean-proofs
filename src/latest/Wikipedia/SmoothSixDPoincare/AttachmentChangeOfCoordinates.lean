import Wikipedia.SmoothSixDPoincare.ClosedAttachment

/-!
# Changing coordinates on an actual attachment

An ambient homeomorphism carrying the old subspace onto the new one changes
the attaching map on its whole designated face. The quotient homeomorphism
has the prescribed map on the old subspace and is the identity on the handle
coordinates. Values of the handle map away from the attaching face are not
needed for this comparison.
-/

noncomputable section

open Set

namespace Wikipedia.SmoothSixDPoincare.ClosedAttachment

variable {K M N : Type*} [TopologicalSpace K] [TopologicalSpace M] [TopologicalSpace N]
  {A : Set M} {A' : Set N} {B : Set K} {h : C(K, M)} {h' : C(K, N)}

/-- Change the old ambient coordinates while retaining all handle coordinates. -/
def ambientCongr (e : M ≃ₜ N) (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (hface : ∀ k ∈ B, h' k = e (h k)) : Space A B h ≃ₜ Space A' B h' := by
  let a : A ≃ₜ A' := e.subtype hA
  apply Homeomorph.Quot.congr (a.sumCongr (Homeomorph.refl K))
  intro x y
  cases x with
  | inl x =>
    cases y with
    | inl y => exact Iff.rfl
    | inr k =>
      change (k ∈ B ∧ (x : M) = h k) ↔ (k ∈ B ∧ e (x : M) = h' k)
      constructor
      · rintro ⟨hk, hx⟩
        exact ⟨hk, (congrArg e hx).trans (hface k hk).symm⟩
      · rintro ⟨hk, hx⟩
        exact ⟨hk, e.injective (hx.trans (hface k hk))⟩
  | inr k => cases y <;> exact Iff.rfl

/-- The comparison has the original ambient homeomorphism on the old subspace. -/
theorem ambientCongr_inl (e : M ≃ₜ N) (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (hface : ∀ k ∈ B, h' k = e (h k)) (x : A) :
    ambientCongr e hA hface (Quot.mk _ (Sum.inl x)) =
      Quot.mk _ (Sum.inl (⟨e x, (hA x).mp x.property⟩ : A')) := rfl

/-- The comparison retains the entire handle parametrization, not just its core sphere. -/
theorem ambientCongr_inr (e : M ≃ₜ N) (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (hface : ∀ k ∈ B, h' k = e (h k)) (k : K) :
    ambientCongr e hA hface (Quot.mk _ (Sum.inr k)) = Quot.mk _ (Sum.inr k) := rfl

/-- Any homeomorphic realization of the old attachment also realizes the changed attachment. -/
def changedRealization {Y : Type*} [TopologicalSpace Y]
    (e : M ≃ₜ N) (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (hface : ∀ k ∈ B, h' k = e (h k)) (r : Space A B h ≃ₜ Y) :
    Space A' B h' ≃ₜ Y := (ambientCongr e hA hface).symm.trans r

/-- The changed realization agrees with the old one on every handle point. -/
theorem changedRealization_inr {Y : Type*} [TopologicalSpace Y]
    (e : M ≃ₜ N) (hA : ∀ x, x ∈ A ↔ e x ∈ A')
    (hface : ∀ k ∈ B, h' k = e (h k)) (r : Space A B h ≃ₜ Y) (k : K) :
    changedRealization e hA hface r (Quot.mk _ (Sum.inr k)) = r (Quot.mk _ (Sum.inr k)) := by
  change r ((ambientCongr e hA hface).symm (Quot.mk _ (Sum.inr k))) = _
  rw [← ambientCongr_inr e hA hface k, Homeomorph.symm_apply_apply]

end Wikipedia.SmoothSixDPoincare.ClosedAttachment
