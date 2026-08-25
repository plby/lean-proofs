import StackExchange.Puzzling139335.Definitions

/-! # Elementary set algebra for an order-four homeomorphism -/

open Set

namespace Puzzling139335.QuarterTurnTopology

variable (e : Plane ≃ₜ Plane) {c : Plane}

/-- Any square root of the half-turn fixes its center. -/
theorem fixed_center
    (hsquare : ∀ x, e (e x) = AffineIsometryEquiv.pointReflection ℝ c x) : e c = c := by
  apply (AffineIsometryEquiv.pointReflection_fixed_iff (𝕜 := ℝ) (x := c)).mp
  calc
    AffineIsometryEquiv.pointReflection ℝ c (e c) = e (e (e c)) := (hsquare (e c)).symm
    _ = e (AffineIsometryEquiv.pointReflection ℝ c c) := congrArg e (hsquare c)
    _ = e c := by rw [AffineIsometryEquiv.pointReflection_self]

/-- Four applications of a square root of the half-turn are the identity. -/
theorem fourth_apply
    (hsquare : ∀ x, e (e x) = AffineIsometryEquiv.pointReflection ℝ c x) (x : Plane) :
    e (e (e (e x))) = x := by
  rw [hsquare, hsquare]
  exact AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) c x

theorem fourth_image
    (hfour : ∀ x, e (e (e (e x))) = x) (T : Set Plane) :
    e '' (e '' (e '' (e '' T))) = T := by
  rw [← image_comp, ← image_comp, ← image_comp]
  have hid : (((e ∘ e) ∘ e) ∘ e : Plane → Plane) = id := funext hfour
  rw [hid, image_id]

/-- The even and odd translates are disjoint whenever adjacent translates
are disjoint.  This statement is pure set algebra; it uses no separation
claim about the opposite translates. -/
theorem disjoint_even_odd {T : Set Plane}
    (hfour : ∀ x, e (e (e (e x))) = x) (h01 : Disjoint T (e '' T)) :
    Disjoint (T ∪ e '' (e '' T)) (e '' (T ∪ e '' (e '' T))) := by
  have h12 : Disjoint (e '' T) (e '' (e '' T)) :=
    (disjoint_image_iff e.injective).2 h01
  have h23 : Disjoint (e '' (e '' T)) (e '' (e '' (e '' T))) :=
    (disjoint_image_iff e.injective).2 h12
  have h30 : Disjoint (e '' (e '' (e '' T))) T := by
    simpa only [fourth_image e hfour] using (disjoint_image_iff e.injective).2 h23
  rw [image_union, disjoint_union_left, disjoint_union_right, disjoint_union_right]
  exact ⟨⟨h01, h30.symm⟩, ⟨h12.symm, h23⟩⟩

end Puzzling139335.QuarterTurnTopology
