import ErdosProblems.Erdos633b.DirectedEdgeColor
import ErdosProblems.Erdos633b.BoundaryRayCoordinates
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine

/-! Positively oriented boundary vectors are defined from actual vertex
positions. Their side tests agree with the barycentric half-planes. -/

namespace Erdos633b.Triangle

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

noncomputable def orientationSign (S : Triangle) (o : Orientation ℝ Plane (Fin 2)) : SignType :=
  (o.oangle (S.points 1 - S.points 0) (S.points 2 - S.points 0)).sign

noncomputable def cyclicEdgeVector (S : Triangle) (j : Fin 3) : Plane :=
  S.points (j + 2) - S.points (j + 1)

theorem cyclicEdgeVector_ne_zero (S : Triangle) (j : Fin 3) : S.cyclicEdgeVector j ≠ 0 :=
  sub_ne_zero.mpr (S.independent.injective.ne
    ((by decide : ∀ j : Fin 3, j + 2 ≠ j + 1) j))

theorem orientationSign_ne_zero (S : Triangle) (o : Orientation ℝ Plane (Fin 2)) :
    S.orientationSign o ≠ 0 := by
  let _ : Module.Oriented ℝ Plane (Fin 2) := ⟨o⟩
  intro h
  have hn := S.cyclic_not_collinear 0
  apply hn
  apply EuclideanGeometry.oangle_sign_eq_zero_iff_collinear.mp
  exact h

theorem orientationSign_cyclic (S : Triangle) (o : Orientation ℝ Plane (Fin 2)) (j : Fin 3) :
    (o.oangle (S.cyclicEdgeVector j) (S.points j - S.points (j + 1))).sign =
      S.orientationSign o := by
  let _ : Module.Oriented ℝ Plane (Fin 2) := ⟨o⟩
  have h1 := EuclideanGeometry.oangle_rotate_sign (S.points 1) (S.points 0) (S.points 2)
  have h2 := EuclideanGeometry.oangle_rotate_sign (S.points 0) (S.points 2) (S.points 1)
  fin_cases j
  · exact h2.trans h1
  · exact h1
  · rfl

noncomputable def positiveEdgeVector (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (j : Fin 3) : Plane :=
  if S.orientationSign o = 1 then S.cyclicEdgeVector j else -S.cyclicEdgeVector j

noncomputable def positiveEdgeDirection (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (u : Plane) (j : Fin 3) : Real.Angle := o.oangle u (S.positiveEdgeVector o j)

theorem positiveEdgeVector_ne_zero (S : Triangle) (o : Orientation ℝ Plane (Fin 2)) (j : Fin 3) :
    S.positiveEdgeVector o j ≠ 0 := by
  unfold positiveEdgeVector
  split_ifs
  · exact S.cyclicEdgeVector_ne_zero j
  · exact neg_ne_zero.mpr (S.cyclicEdgeVector_ne_zero j)

theorem positive_edge_color (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x j, f (x + (S.angle j : Real.Angle)) = f x + 1) (j : Fin 3) :
    f (S.positiveEdgeDirection o u j) = f (S.positiveEdgeDirection o u 0) := by
  have h := S.cyclic_edge_color o hu f hp ht j
  by_cases hs : S.orientationSign o = 1
  · simpa only [positiveEdgeDirection, positiveEdgeVector, if_pos hs, edgeDirection,
      direction, cyclicEdgeVector] using h
  · simp only [positiveEdgeDirection, positiveEdgeVector, if_neg hs]
    rw [o.oangle_neg_right hu (S.cyclicEdgeVector_ne_zero j),
      o.oangle_neg_right hu (S.cyclicEdgeVector_ne_zero 0), hp, hp]
    exact congrArg (fun z : ZMod 2 => z + 1) h

theorem relative_edge_coordinates (S : Triangle) (j : Fin 3) (q : Plane) :
    q - S.points (j + 1) = S.coord (j + 2) q • S.cyclicEdgeVector j +
      S.coord j q • (S.points j - S.points (j + 1)) := by
  rw [S.relative_barycentric_cyclic j (S.points (j + 1)) q]
  simp only [sub_self, smul_zero, add_zero, cyclicEdgeVector]
  module

theorem cyclicEdgeVector_side_sign (S : Triangle) (o : Orientation ℝ Plane (Fin 2)) (j : Fin 3)
    (p q : Plane) (hp : S.coord j p = 0) :
    (o.oangle (S.cyclicEdgeVector j) (q - p)).sign =
      SignType.sign (S.coord j q) * S.orientationSign o := by
  have he : q - p = (S.coord (j + 2) q - S.coord (j + 2) p) • S.cyclicEdgeVector j +
      S.coord j q • (S.points j - S.points (j + 1)) := by
    calc
      q - p = (q - S.points (j + 1)) - (p - S.points (j + 1)) := by abel
      _ = _ := by rw [S.relative_edge_coordinates j q, S.relative_edge_coordinates j p, hp]; module
  rw [he, o.oangle_sign_smul_add_smul_right, S.orientationSign_cyclic]

theorem positiveEdgeVector_side_sign (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (j : Fin 3) (p q : Plane) (hp : S.coord j p = 0) :
    (o.oangle (S.positiveEdgeVector o j) (q - p)).sign = SignType.sign (S.coord j q) := by
  unfold positiveEdgeVector
  split_ifs with hs
  · rw [S.cyclicEdgeVector_side_sign o j p q hp, hs, mul_one]
  · have hneg : S.orientationSign o = -1 :=
      (by decide : ∀ s : SignType, s ≠ 0 → s ≠ 1 → s = -1) _ (S.orientationSign_ne_zero o) hs
    rw [o.oangle_sign_neg_left, S.cyclicEdgeVector_side_sign o j p q hp, hneg, mul_neg_one, neg_neg]

end Erdos633b.Triangle
