import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Equiv

/-!
# Attach a whole piece by its specified face map into the old space

The quotient uses only the original attaching face and its continuous map
into the old space. Changing that old space by a homeomorphism retains every
whole-handle coordinate and requires no ambient extension.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K X Y Z : Type*} [TopologicalSpace K] [TopologicalSpace X]
  [TopologicalSpace Y] [TopologicalSpace Z] {B : Set K} (b : C(B, X))

def Rel : X ⊕ K → X ⊕ K → Prop
  | .inl x, .inr k => ∃ hk : k ∈ B, x = b ⟨k, hk⟩
  | _, _ => False

abbrev Space := Quot (Rel b)

def oldMap : C(X, Space b) :=
  ⟨fun x => Quot.mk _ (Sum.inl x), continuous_quot_mk.comp continuous_inl⟩

def handleMap : C(K, Space b) :=
  ⟨fun k => Quot.mk _ (Sum.inr k), continuous_quot_mk.comp continuous_inr⟩

theorem face_identification (u : B) : oldMap b (b u) = handleMap b u.val :=
  Quot.sound ⟨u.property, rfl⟩

def baseCongr (e : X ≃ₜ Y) :
    Space b ≃ₜ Space (e.toHomotopyEquiv.toFun.comp b) := by
  apply Homeomorph.Quot.congr (e.sumCongr (Homeomorph.refl K))
  intro x y
  cases x with
  | inl x =>
      cases y with
      | inl y => exact Iff.rfl
      | inr k =>
          change (∃ hk : k ∈ B, x = b ⟨k, hk⟩) ↔
            ∃ hk : k ∈ B, e x = e (b ⟨k, hk⟩)
          constructor
          · rintro ⟨hk, hx⟩
            exact ⟨hk, congrArg e hx⟩
          · rintro ⟨hk, hx⟩
            exact ⟨hk, e.injective hx⟩
  | inr k => cases y <;> exact Iff.rfl

theorem baseCongr_old (e : X ≃ₜ Y) (x : X) :
    baseCongr b e (oldMap b x) = oldMap (e.toHomotopyEquiv.toFun.comp b) (e x) := rfl

theorem baseCongr_handle (e : X ≃ₜ Y) (k : K) :
    baseCongr b e (handleMap b k) = handleMap (e.toHomotopyEquiv.toFun.comp b) k := rfl

def changedRealization (e : X ≃ₜ Y) (r : Space b ≃ₜ Z) :
    Space (e.toHomotopyEquiv.toFun.comp b) ≃ₜ Z :=
  (baseCongr b e).symm.trans r

theorem changedRealization_old (e : X ≃ₜ Y) (r : Space b ≃ₜ Z) (y : Y) :
    changedRealization b e r (oldMap (e.toHomotopyEquiv.toFun.comp b) y) =
      r (oldMap b (e.symm y)) := by
  change r ((baseCongr b e).symm (oldMap (e.toHomotopyEquiv.toFun.comp b) y)) = _
  have h := baseCongr_old b e (e.symm y)
  rw [Homeomorph.apply_symm_apply] at h
  rw [← h, Homeomorph.symm_apply_apply]

theorem changedRealization_handle (e : X ≃ₜ Y) (r : Space b ≃ₜ Z) (k : K) :
    changedRealization b e r (handleMap (e.toHomotopyEquiv.toFun.comp b) k) =
      r (handleMap b k) := by
  change r ((baseCongr b e).symm (handleMap (e.toHomotopyEquiv.toFun.comp b) k)) = _
  rw [← baseCongr_handle b e k, Homeomorph.symm_apply_apply]

end Wikipedia.SmoothSixDPoincare.FaceAttachment
