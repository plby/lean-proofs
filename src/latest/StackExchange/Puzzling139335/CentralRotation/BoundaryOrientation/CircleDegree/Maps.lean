import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Algebra
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Homotopy

/-! # Degree of a continuous map of the additive circle -/

noncomputable section

namespace Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

open unitInterval

/-- The degree of a continuous circle map, expressed as a real number.  The
theorem `degree_eq_int` proves that this number is integral. -/
def degree (f : C(Circle, Circle)) : ℝ := displacement (f.comp onceAround)

theorem degree_eq_sub_of_lift (f : C(Circle, Circle)) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hlift : ∀ t : ℝ, (φ t : Circle) = f (t : Circle)) :
    degree f = φ 1 - φ 0 := by
  exact displacement_eq_sub_of_lift (f.comp onceAround)
    ⟨fun t : I => φ (t : ℝ), hφ.comp continuous_subtype_val⟩
    (fun t => hlift t)

theorem degree_eq_int (f : C(Circle, Circle)) : ∃ n : ℤ, degree f = n := by
  apply displacement_eq_int
  change f ((1 : ℝ) : Circle) = f ((0 : ℝ) : Circle)
  rw [AddCircle.coe_period]
  rfl

@[simp] theorem degree_id : degree (ContinuousMap.id Circle) = 1 := by
  simpa only [degree, ContinuousMap.id_comp] using displacement_onceAround

@[simp] theorem degree_const (x : Circle) : degree (ContinuousMap.const Circle x) = 0 := by
  change displacement (ContinuousMap.const I x) = 0
  exact displacement_const x

@[simp] theorem degree_add (f g : C(Circle, Circle)) :
    degree (f + g) = degree f + degree g := by
  change displacement (f.comp onceAround + g.comp onceAround) = degree f + degree g
  exact displacement_add _ _

@[simp] theorem degree_neg (f : C(Circle, Circle)) : degree (-f) = -degree f := by
  change displacement (-(f.comp onceAround)) = -degree f
  exact displacement_neg _

@[simp] theorem degree_add_const (f : C(Circle, Circle)) (x : Circle) :
    degree (f + ContinuousMap.const Circle x) = degree f := by simp

@[simp] theorem degree_const_add (f : C(Circle, Circle)) (x : Circle) :
    degree (ContinuousMap.const Circle x + f) = degree f := by simp

/-- A homotopy of circle maps gives a free homotopy of their once-around loops. -/
theorem degree_eq_of_homotopy {f g : C(Circle, Circle)} (H : f.Homotopy g) :
    degree f = degree g := by
  apply displacement_eq_of_homotopy (H.compContinuousMap onceAround)
  intro s
  change H (s, ((1 : ℝ) : Circle)) = H (s, ((0 : ℝ) : Circle))
  rw [AddCircle.coe_period]
  rfl

theorem degree_eq_of_homotopic {f g : C(Circle, Circle)} (h : f.Homotopic g) :
    degree f = degree g := by
  obtain ⟨H⟩ := h
  exact degree_eq_of_homotopy H

end Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

end
