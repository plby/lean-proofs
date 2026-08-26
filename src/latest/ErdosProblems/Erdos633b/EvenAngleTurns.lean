import ErdosProblems.Erdos633b.TriangleEdgeOrientation

/-! Even-character corner angles flip edge colors on a turn. Normalizing
all cyclic edges to positive orientation preserves their color differences. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem invariant_sub_shift (f : Real.Angle → ZMod 2) (a : Real.Angle)
    (h : ∀ x, f (x + a) = f x) (x : Real.Angle) : f (x - a) = f x := by
  have hh := h (x - a)
  rw [sub_add_cancel] at hh
  exact hh.symm

theorem direction_color_turn_even (o : Orientation ℝ Plane (Fin 2)) {u A B C : Plane}
    (hu : u ≠ 0) (hAB : A ≠ B) (hCB : C ≠ B) (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x, f (x + (EuclideanGeometry.angle A B C : Real.Angle)) = f x) :
    f (direction o u B C) = f (direction o u A B) + 1 := by
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
  · rw [← hadd, he, ← add_assoc, hp, ht]
  · rw [← hadd, he, ← add_assoc, hp, ← sub_eq_add_neg, invariant_sub_shift f _ ht]

namespace Triangle

theorem positive_edge_color_difference (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1) (i j : Fin 3) (δ : ZMod 2)
    (he : f (S.edgeDirection o u i) = f (S.edgeDirection o u j) + δ) :
    f (S.positiveEdgeDirection o u i) = f (S.positiveEdgeDirection o u j) + δ := by
  by_cases hs : S.orientationSign o = 1
  · simpa only [positiveEdgeDirection, positiveEdgeVector, if_pos hs, edgeDirection,
      direction, cyclicEdgeVector] using he
  · simp only [positiveEdgeDirection, positiveEdgeVector, if_neg hs]
    rw [o.oangle_neg_right hu (S.cyclicEdgeVector_ne_zero i),
      o.oangle_neg_right hu (S.cyclicEdgeVector_ne_zero j), hp, hp]
    change f (S.edgeDirection o u i) + 1 = (f (S.edgeDirection o u j) + 1) + δ
    rw [he]
    abel

theorem caseSeven_outer_color_pattern (S T : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x j, f (x + (S.angle j : Real.Angle)) = f x + 1)
    (h1 : T.angle 1 = S.angle 1) (h2 : T.angle 2 = S.angle 0 + S.angle 1) :
    f (T.positiveEdgeDirection o u 1) = f (T.positiveEdgeDirection o u 0) + 1 ∧
      f (T.positiveEdgeDirection o u 2) = f (T.positiveEdgeDirection o u 0) := by
  have hodd (x : Real.Angle) : f (x + (T.angle 1 : Real.Angle)) = f x + 1 := by
    rw [h1, ht]
  have heven (x : Real.Angle) : f (x + (T.angle 2 : Real.Angle)) = f x := by
    rw [h2, Real.Angle.coe_add, ← add_assoc, ht, ht, add_assoc,
      show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  constructor
  · apply T.positive_edge_color_difference o hu f hp 1 0 1
    apply direction_color_turn_even o hu (T.independent.injective.ne (by decide))
      (T.independent.injective.ne (by decide)) f hp
    intro x
    change f (x + (EuclideanGeometry.angle (T.points 1) (T.points 2)
      (T.points 0) : Real.Angle)) = f x
    have h := heven x
    change f (x + (EuclideanGeometry.angle (T.points 0) (T.points 2)
      (T.points 1) : Real.Angle)) = f x at h
    simpa only [EuclideanGeometry.angle_comm (T.points 0)] using h
  · have hcyc : f (T.edgeDirection o u 0) = f (T.edgeDirection o u 2) := by
      apply direction_color_turn o hu (T.independent.injective.ne (by decide))
        (T.independent.injective.ne (by decide)) f hp
      intro x
      change f (x + (EuclideanGeometry.angle (T.points 0) (T.points 1)
        (T.points 2) : Real.Angle)) = f x + 1
      have h := hodd x
      change f (x + (EuclideanGeometry.angle (T.points 2) (T.points 1)
        (T.points 0) : Real.Angle)) = f x + 1 at h
      simpa only [EuclideanGeometry.angle_comm (T.points 2)] using h
    simpa only [add_zero] using T.positive_edge_color_difference o hu f hp 2 0 0
      (by simpa only [add_zero] using hcyc.symm)

end Triangle
end Erdos633b
