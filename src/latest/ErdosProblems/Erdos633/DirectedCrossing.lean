import ErdosProblems.Erdos633.AreaBoundary

/-!
# Directed crossings and collinear subdivisions

The crossing of an oriented edge with the positive horizontal ray is an
integer. Writing it as a vertical step difference times the sign of the
line intercept makes subdivision independent of the order of collinear
points. This is the cancellation identity needed after field embeddings.
-/

namespace Erdos633

noncomputable def positiveStep (r : ℝ) : ℤ := if 0 < r then 1 else 0

noncomputable def rayEdgeCrossing (a b : ℂ) : ℤ :=
  (positiveStep b.im - positiveStep a.im) *
    positiveStep (planeDet a b * (b.im - a.im))

@[simp] theorem rayEdgeCrossing_self (a : ℂ) : rayEdgeCrossing a a = 0 := by
  simp [rayEdgeCrossing]

theorem rayEdgeCrossing_reverse (a b : ℂ) :
    rayEdgeCrossing b a = -rayEdgeCrossing a b := by
  have h : planeDet b a * (a.im - b.im) = planeDet a b * (b.im - a.im) := by
    unfold planeDet
    ring
  simp only [rayEdgeCrossing, h]
  ring

theorem positiveStep_pos_mul (x y : ℝ) (hx : 0 < x) :
    positiveStep (x * y) = positiveStep y := by
  have h : 0 < x * y ↔ 0 < y := by
    constructor
    · exact fun h => pos_of_mul_pos_right h hx.le
    · exact fun h => mul_pos hx h
  simp only [positiveStep, h]

theorem rayEdgeCrossing_on_line (p d : ℂ) (t u : ℝ) :
    rayEdgeCrossing (p + t • d) (p + u • d) =
      (positiveStep (p + u • d).im - positiveStep (p + t • d).im) *
        positiveStep (planeDet p d * d.im) := by
  by_cases htu : u = t
  · subst u
    simp
  have hdet : planeDet (p + t • d) (p + u • d) = (u - t) * planeDet p d := by
    simp [planeDet]
    ring
  have him : (p + u • d).im - (p + t • d).im = (u - t) * d.im := by
    simp
    ring
  have hprod : ((u - t) * planeDet p d) * ((u - t) * d.im) =
      (u - t) ^ 2 * (planeDet p d * d.im) := by ring
  rw [rayEdgeCrossing, hdet, him, hprod,
    positiveStep_pos_mul _ _ (sq_pos_of_ne_zero (sub_ne_zero.mpr htu))]

/-- Collinear directed edges telescope even when the subdivision parameters
are not monotone. No betweenness or injectivity assumption is needed. -/
theorem rayEdgeCrossing_line_add (p d : ℂ) (t u v : ℝ) :
    rayEdgeCrossing (p + t • d) (p + u • d) +
      rayEdgeCrossing (p + u • d) (p + v • d) =
        rayEdgeCrossing (p + t • d) (p + v • d) := by
  rw [rayEdgeCrossing_on_line, rayEdgeCrossing_on_line, rayEdgeCrossing_on_line]
  ring

theorem rayEdgeCrossing_lineMap_add (a b : ℂ) (t u v : ℝ) :
    rayEdgeCrossing (AffineMap.lineMap a b t) (AffineMap.lineMap a b u) +
      rayEdgeCrossing (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) =
        rayEdgeCrossing (AffineMap.lineMap a b t) (AffineMap.lineMap a b v) := by
  simpa only [AffineMap.lineMap_apply_module', add_comm] using
    rayEdgeCrossing_line_add a (b - a) t u v

noncomputable def edgeCrossingAt (z a b : ℂ) : ℤ := rayEdgeCrossing (a - z) (b - z)

theorem edgeCrossingAt_reverse (z a b : ℂ) :
    edgeCrossingAt z b a = -edgeCrossingAt z a b :=
  rayEdgeCrossing_reverse (a - z) (b - z)

theorem edgeCrossingAt_lineMap_add (z a b : ℂ) (t u v : ℝ) :
    edgeCrossingAt z (AffineMap.lineMap a b t) (AffineMap.lineMap a b u) +
      edgeCrossingAt z (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) =
        edgeCrossingAt z (AffineMap.lineMap a b t) (AffineMap.lineMap a b v) := by
  have h (r : ℝ) : AffineMap.lineMap a b r - z =
      (a - z) + r • (b - a) := by
    rw [AffineMap.lineMap_apply_module']
    abel
  simp only [edgeCrossingAt, h]
  exact rayEdgeCrossing_line_add (a - z) (b - a) t u v

end Erdos633
