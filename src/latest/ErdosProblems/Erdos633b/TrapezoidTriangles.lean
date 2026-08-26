import ErdosProblems.Erdos633b.SixtyCoordinates
import ErdosProblems.Erdos633b.TrapezoidRegions

/-! Nondegenerate triangles with exactly the three basic-trapezoid supports. -/

namespace Erdos633b.Sixty

noncomputable def leftTriangle (d : ℝ) (hd : 0 < d) (p y : ℝ) (hp : 0 < p) (hy : 0 < y) :
    Triangle := triangle d hd 0 y 0 0 p y (by
      rw [show (0 - 0) * (y - y) - (p - 0) * (0 - y) = p * y by ring]
      exact (mul_pos hp hy).ne')

noncomputable def rightTriangle (d : ℝ) (hd : 0 < d) (p q y : ℝ) (hq : 0 < q) (hy : 0 < y) :
    Triangle := triangle d hd (p + q) y p y (p + q + y) 0 (by
      rw [show (p - (p + q)) * (0 - y) - (p + q + y - (p + q)) * (y - y) = q * y by ring]
      exact (mul_pos hq hy).ne')

noncomputable def middleTriangle (d : ℝ) (hd : 0 < d) (p q y : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hy : 0 < y) : Triangle :=
  triangle d hd p y (p + q + y) 0 0 0 (by
    rw [show (p + q + y - p) * (0 - y) - (0 - p) * (0 - y) = -((p + q + y) * y) by ring]
    exact neg_ne_zero.mpr (mul_pos (by linarith) hy).ne')

theorem leftTriangle_points (d : ℝ) (hd : 0 < d) (p y : ℝ) (hp : 0 < p) (hy : 0 < y) :
    (leftTriangle d hd p y hp hy).points = ![point d 0 y, point d 0 0, point d p y] := rfl

theorem rightTriangle_points (d : ℝ) (hd : 0 < d) (p q y : ℝ) (hq : 0 < q) (hy : 0 < y) :
    (rightTriangle d hd p q y hq hy).points =
      ![point d (p + q) y, point d p y, point d (p + q + y) 0] := rfl

theorem middleTriangle_points (d : ℝ) (hd : 0 < d) (p q y : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hy : 0 < y) :
    (middleTriangle d hd p q y hp hq hy).points =
      ![point d p y, point d (p + q + y) 0, point d 0 0] := rfl

theorem leftTriangle_coords (d : ℝ) (hd : 0 < d) (p y : ℝ) (hp : 0 < p) (hy : 0 < y)
    (v : Plane) :
    (frame d hd).coord 1 v = p * (leftTriangle d hd p y hp hy).coord 2 v ∧
      (frame d hd).coord 2 v = y * (1 - (leftTriangle d hd p y hp hy).coord 1 v) := by
  let T := leftTriangle d hd p y hp hy
  obtain ⟨hx, hz⟩ := coords_of_points d hd T 0 y 0 0 p y (leftTriangle_points d hd p y hp hy) v
  refine ⟨by simpa using hx, ?_⟩
  linear_combination hz + y * (T.coord_sum v)

theorem rightTriangle_coords (d : ℝ) (hd : 0 < d) (p q y : ℝ) (hq : 0 < q) (hy : 0 < y)
    (v : Plane) :
    (frame d hd).coord 1 v = p + q - q * (rightTriangle d hd p q y hq hy).coord 1 v +
      y * (rightTriangle d hd p q y hq hy).coord 2 v ∧
      (frame d hd).coord 2 v = y * (1 - (rightTriangle d hd p q y hq hy).coord 2 v) := by
  let T := rightTriangle d hd p q y hq hy
  obtain ⟨hx, hz⟩ := coords_of_points d hd T (p + q) y p y (p + q + y) 0
    (rightTriangle_points d hd p q y hq hy) v
  constructor
  · linear_combination hx + (p + q) * (T.coord_sum v)
  · linear_combination hz + y * (T.coord_sum v)

theorem middleTriangle_coords (d : ℝ) (hd : 0 < d) (p q y : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hy : 0 < y) (v : Plane) :
    (frame d hd).coord 1 v = p * (1 - (middleTriangle d hd p q y hp hq hy).coord 1 v -
      (middleTriangle d hd p q y hp hq hy).coord 2 v) +
      (p + q + y) * (middleTriangle d hd p q y hp hq hy).coord 1 v ∧
    (frame d hd).coord 2 v = y * (1 - (middleTriangle d hd p q y hp hq hy).coord 1 v -
      (middleTriangle d hd p q y hp hq hy).coord 2 v) := by
  let T := middleTriangle d hd p q y hp hq hy
  obtain ⟨hx, hz⟩ := coords_of_points d hd T p y (p + q + y) 0 0 0
    (middleTriangle_points d hd p q y hp hq hy) v
  constructor
  · linear_combination hx + p * (T.coord_sum v)
  · linear_combination hz + y * (T.coord_sum v)

theorem leftTriangle_support (d : ℝ) (hd : 0 < d) (p q y : ℝ) (hp : 0 < p) (hy : 0 < y) :
    (leftTriangle d hd p y hp hy).support = TrapezoidPartition.region (frame d hd) p q y .left := by
  ext v
  obtain ⟨hx, ht⟩ := leftTriangle_coords d hd p y hp hy v
  rw [Triangle.mem_support_iff_coords, TrapezoidPartition.mem_region, hx, ht,
    TrapezoidPartition.left_coords_iff p q y hp hy]

theorem rightTriangle_support (d : ℝ) (hd : 0 < d) (p q y : ℝ) (hq : 0 < q) (hy : 0 < y) :
    (rightTriangle d hd p q y hq hy).support =
      TrapezoidPartition.region (frame d hd) p q y .right := by
  ext v
  obtain ⟨hx, ht⟩ := rightTriangle_coords d hd p q y hq hy v
  rw [Triangle.mem_support_iff_coords, TrapezoidPartition.mem_region, hx, ht,
    TrapezoidPartition.right_coords_iff p q y hq hy]

theorem middleTriangle_support (d : ℝ) (hd : 0 < d) (p q y : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hy : 0 < y) :
    (middleTriangle d hd p q y hp hq hy).support =
      TrapezoidPartition.region (frame d hd) p q y .middle := by
  ext v
  obtain ⟨hx, ht⟩ := middleTriangle_coords d hd p q y hp hq hy v
  rw [Triangle.mem_support_iff_coords, TrapezoidPartition.mem_region, hx, ht,
    TrapezoidPartition.middle_coords_iff p q y hp hq hy]

end Erdos633b.Sixty
