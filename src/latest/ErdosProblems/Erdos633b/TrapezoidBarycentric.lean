import ErdosProblems.Erdos633b.SixtyCorner

/-! The closed ideal trapezoid in coordinates of the triangle on its two axis edges. -/

namespace Erdos633b.Sixty

theorem corner_coords (d : ℝ) (hd : 0 < d) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (p : Plane) :
    (frame d hd).coord 1 p = x * (cornerTriangle d hd x y hx hy).coord 1 p ∧
      (frame d hd).coord 2 p = y * (cornerTriangle d hd x y hx hy).coord 2 p := by
  simpa only [zero_mul, zero_add, add_zero] using
    coords_of_points d hd (cornerTriangle d hd x y hx hy) 0 0 x 0 0 y
      (cornerTriangle_points d hd x y hx hy) p

theorem mem_trapezoid_iff_corner_coords (d : ℝ) (hd : 0 < d) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (p : Plane) :
    let U := cornerTriangle d hd (x + y) y (add_pos hx hy) hy
    p ∈ TrapezoidPartition.trapezoidSet (frame d hd) x y ↔
      0 ≤ U.coord 1 p ∧ 0 ≤ U.coord 2 p ∧ U.coord 2 p ≤ 1 ∧
        (x + y) * U.coord 1 p + y * U.coord 2 p ≤ x + y := by
  let U := cornerTriangle d hd (x + y) y (add_pos hx hy) hy
  change TrapezoidPartition.trapezoid x y ((frame d hd).coord 1 p) ((frame d hd).coord 2 p) ↔ _
  rw [(corner_coords d hd (x + y) y (add_pos hx hy) hy p).1,
    (corner_coords d hd (x + y) y (add_pos hx hy) hy p).2]
  constructor
  · rintro ⟨hs, ht, hty, hsum⟩
    have hh : y * U.coord 2 p ≤ y * 1 := by simpa only [mul_one] using hty
    exact ⟨nonneg_of_mul_nonneg_right hs (add_pos hx hy),
      nonneg_of_mul_nonneg_right ht hy, le_of_mul_le_mul_left hh hy, hsum⟩
  · rintro ⟨hs, ht, hty, hsum⟩
    refine ⟨mul_nonneg (add_pos hx hy).le hs, mul_nonneg hy.le ht, ?_, hsum⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hty hy.le

end Erdos633b.Sixty
