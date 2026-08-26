import ErdosProblems.Erdos633b.DirectionColorRules
import ErdosProblems.Erdos633b.DirectionRays

/-! Direction-color rules on genuine directed triangle edges. The three
cyclic edges have one color, and reversing an edge changes that color. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem parity_sub_shift (f : Real.Angle → ZMod 2) (a : Real.Angle)
    (h : ∀ x, f (x + a) = f x + 1) (x : Real.Angle) :
    f (x - a) = f x + 1 := by
  have hh := h (x - a)
  rw [sub_add_cancel] at hh
  calc
    f (x - a) = (f (x - a) + 1) + 1 := by
      rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
    _ = f x + 1 := congrArg (fun y => y + 1) hh.symm

theorem direction_reverse (o : Orientation ℝ Plane (Fin 2)) {u A B : Plane}
    (hu : u ≠ 0) (hAB : A ≠ B) :
    direction o u B A = direction o u A B + (Real.pi : Real.Angle) := by
  unfold direction
  rw [show A - B = -(B - A) by abel]
  exact o.oangle_neg_right hu (sub_ne_zero.mpr hAB.symm)

theorem direction_color_reverse (o : Orientation ℝ Plane (Fin 2)) {u A B : Plane}
    (hu : u ≠ 0) (hAB : A ≠ B) (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1) :
    f (direction o u B A) = f (direction o u A B) + 1 := by
  rw [direction_reverse o hu hAB, hp]

theorem direction_color_turn (o : Orientation ℝ Plane (Fin 2)) {u A B C : Plane}
    (hu : u ≠ 0) (hAB : A ≠ B) (hCB : C ≠ B) (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x, f (x + (EuclideanGeometry.angle A B C : Real.Angle)) = f x + 1) :
    f (direction o u B C) = f (direction o u A B) := by
  have hb := sub_ne_zero.mpr hAB
  have hc := sub_ne_zero.mpr hCB
  have hturn : o.oangle (B - A) (C - B) =
      o.oangle (A - B) (C - B) + (Real.pi : Real.Angle) := by
    simpa only [neg_sub] using o.oangle_neg_left hb hc
  have hadd := o.oangle_add hu (sub_ne_zero.mpr hAB.symm) hc
  change direction o u A B + o.oangle (B - A) (C - B) = direction o u B C at hadd
  rw [hturn] at hadd
  have hor := o.oangle_eq_angle_or_eq_neg_angle hb hc
  change o.oangle (A - B) (C - B) = (EuclideanGeometry.angle A B C : Real.Angle) ∨
    o.oangle (A - B) (C - B) = -(EuclideanGeometry.angle A B C : Real.Angle) at hor
  rcases hor with he | he
  · rw [← hadd, he, ← add_assoc, hp, ht, add_assoc,
      show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  · rw [← hadd, he, ← add_assoc, hp, ← sub_eq_add_neg, parity_sub_shift f _ ht,
      add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]

namespace Triangle

noncomputable def edgeDirection (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (u : Plane) (j : Fin 3) : Real.Angle :=
  direction o u (S.points (j + 1)) (S.points (j + 2))

theorem cyclic_edge_color (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x j, f (x + (S.angle j : Real.Angle)) = f x + 1) (j : Fin 3) :
    f (S.edgeDirection o u j) = f (S.edgeDirection o u 0) := by
  have h01 : f (direction o u (S.points 1) (S.points 2)) =
      f (direction o u (S.points 0) (S.points 1)) := by
    apply direction_color_turn o hu (S.independent.injective.ne (by decide))
      (S.independent.injective.ne (by decide)) f hp
    intro x
    have h := ht x 1
    change f (x + (EuclideanGeometry.angle (S.points 2) (S.points 1) (S.points 0) : Real.Angle)) =
      f x + 1 at h
    simpa only [EuclideanGeometry.angle_comm (S.points 2)] using h
  have h12 : f (direction o u (S.points 2) (S.points 0)) =
      f (direction o u (S.points 1) (S.points 2)) := by
    apply direction_color_turn o hu (S.independent.injective.ne (by decide))
      (S.independent.injective.ne (by decide)) f hp
    intro x
    have h := ht x 2
    change f (x + (EuclideanGeometry.angle (S.points 0) (S.points 2) (S.points 1) : Real.Angle)) =
      f x + 1 at h
    simpa only [EuclideanGeometry.angle_comm (S.points 0)] using h
  fin_cases j
  · rfl
  · exact h12
  · exact h01.symm

end Triangle
end Erdos633b
