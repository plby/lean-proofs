import ErdosProblems.Erdos633b.EvenAngleTurns

/-! Arbitrary parity shifts at genuine corners, and the two edge-color
patterns used by the group-2 signed perimeter identities. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem parity_sub_shift_value (f : Real.Angle → ZMod 2) (a : Real.Angle) (δ : ZMod 2)
    (h : ∀ x, f (x + a) = f x + δ) (x : Real.Angle) :
    f (x - a) = f x + δ := by
  have hh := h (x - a)
  rw [sub_add_cancel] at hh
  have hd : δ + δ = 0 := (by decide : ∀ d : ZMod 2, d + d = 0) δ
  calc
    f (x - a) = (f (x - a) + δ) + δ := by rw [add_assoc, hd, add_zero]
    _ = f x + δ := congrArg (fun y => y + δ) hh.symm

theorem direction_color_turn_shift (o : Orientation ℝ Plane (Fin 2)) {u A B C : Plane}
    (hu : u ≠ 0) (hAB : A ≠ B) (hCB : C ≠ B) (f : Real.Angle → ZMod 2) (δ : ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x, f (x + (EuclideanGeometry.angle A B C : Real.Angle)) = f x + δ) :
    f (direction o u B C) = f (direction o u A B) + (δ + 1) := by
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
  · rw [← hadd, he, ← add_assoc, hp, ht, add_assoc]
  · rw [← hadd, he, ← add_assoc, hp, ← sub_eq_add_neg,
      parity_sub_shift_value f _ δ ht, add_assoc]

namespace Triangle

theorem positive_edge_one_zero_shift (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (f : Real.Angle → ZMod 2) (δ : ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x, f (x + (S.angle 2 : Real.Angle)) = f x + δ) :
    f (S.positiveEdgeDirection o u 1) = f (S.positiveEdgeDirection o u 0) + (δ + 1) := by
  apply S.positive_edge_color_difference o hu f hp 1 0 (δ + 1)
  apply direction_color_turn_shift o hu (S.independent.injective.ne (by decide))
    (S.independent.injective.ne (by decide)) f δ hp
  intro x
  change f (x + (EuclideanGeometry.angle (S.points 1) (S.points 2)
    (S.points 0) : Real.Angle)) = f x + δ
  have h := ht x
  change f (x + (EuclideanGeometry.angle (S.points 0) (S.points 2)
    (S.points 1) : Real.Angle)) = f x + δ at h
  simpa only [EuclideanGeometry.angle_comm (S.points 0)] using h

theorem positive_edge_zero_two_shift (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (f : Real.Angle → ZMod 2) (δ : ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x, f (x + (S.angle 1 : Real.Angle)) = f x + δ) :
    f (S.positiveEdgeDirection o u 0) = f (S.positiveEdgeDirection o u 2) + (δ + 1) := by
  apply S.positive_edge_color_difference o hu f hp 0 2 (δ + 1)
  apply direction_color_turn_shift o hu (S.independent.injective.ne (by decide))
    (S.independent.injective.ne (by decide)) f δ hp
  intro x
  change f (x + (EuclideanGeometry.angle (S.points 0) (S.points 1)
    (S.points 2) : Real.Angle)) = f x + δ
  have h := ht x
  change f (x + (EuclideanGeometry.angle (S.points 2) (S.points 1)
    (S.points 0) : Real.Angle)) = f x + δ at h
  simpa only [EuclideanGeometry.angle_comm (S.points 2)] using h

theorem positive_color_pattern_odd_even (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (h1 : ∀ x, f (x + (S.angle 1 : Real.Angle)) = f x + 1)
    (h2 : ∀ x, f (x + (S.angle 2 : Real.Angle)) = f x) :
    f (S.positiveEdgeDirection o u 1) = f (S.positiveEdgeDirection o u 0) + 1 ∧
      f (S.positiveEdgeDirection o u 2) = f (S.positiveEdgeDirection o u 0) := by
  constructor
  · simpa only [zero_add] using S.positive_edge_one_zero_shift o hu f 0 hp
      (fun x => by simpa only [add_zero] using h2 x)
  · have h := S.positive_edge_zero_two_shift o hu f 1 hp h1
    simpa only [show (1 : ZMod 2) + 1 = 0 from by decide, add_zero] using h.symm

theorem positive_color_pattern_even_odd (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (h1 : ∀ x, f (x + (S.angle 1 : Real.Angle)) = f x)
    (h2 : ∀ x, f (x + (S.angle 2 : Real.Angle)) = f x + 1) :
    f (S.positiveEdgeDirection o u 1) = f (S.positiveEdgeDirection o u 0) ∧
      f (S.positiveEdgeDirection o u 2) = f (S.positiveEdgeDirection o u 0) + 1 := by
  constructor
  · simpa only [show (1 : ZMod 2) + 1 = 0 from by decide, add_zero] using
      S.positive_edge_one_zero_shift o hu f 1 hp h2
  · have h := S.positive_edge_zero_two_shift o hu f 0 hp
      (fun x => by simpa only [add_zero] using h1 x)
    rw [zero_add] at h
    rw [h, add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]

end Triangle
end Erdos633b
