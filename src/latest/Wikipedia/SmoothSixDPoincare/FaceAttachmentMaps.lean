import Wikipedia.SmoothSixDPoincare.FaceAttachment

/-!
# Maps out of the actual face-attachment quotient

Continuous maps agreeing on the specified face descend to the quotient,
with their entire old-space and whole-piece parametrizations retained.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K X Y : Type*} [TopologicalSpace K] [TopologicalSpace X]
  [TopologicalSpace Y] {B : Set K} (b : C(B, X))

def desc (f : C(X, Y)) (h : C(K, Y)) (hag : ∀ u : B, f (b u) = h u.val) :
    C(Space b, Y) := by
  have hr : ∀ x y, Rel b x y → Sum.elim f h x = Sum.elim f h y := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact hxy.elim
        | inr k =>
            obtain ⟨hk, rfl⟩ := hxy
            exact hag ⟨k, hk⟩
    | inr k => cases y <;> exact hxy.elim
  exact ⟨Quot.lift (Sum.elim f h) hr,
    continuous_quot_lift hr (continuous_sum_dom.mpr ⟨f.continuous, h.continuous⟩)⟩

theorem desc_old (f : C(X, Y)) (h : C(K, Y)) (hag : ∀ u : B, f (b u) = h u.val) (x : X) :
    desc b f h hag (oldMap b x) = f x := rfl

theorem desc_handle (f : C(X, Y)) (h : C(K, Y)) (hag : ∀ u : B, f (b u) = h u.val) (k : K) :
    desc b f h hag (handleMap b k) = h k := rfl

theorem induction_on (z : Space b) {P : Space b → Prop}
    (hX : ∀ x, P (oldMap b x)) (hK : ∀ k, P (handleMap b k)) : P z := by
  refine Quot.inductionOn z ?_
  intro x
  cases x with
  | inl x => exact hX x
  | inr k => exact hK k

end Wikipedia.SmoothSixDPoincare.FaceAttachment
