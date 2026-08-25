import StackExchange.Puzzling139335.N6.TripleSectors.Maps
import StackExchange.Puzzling139335.SquareGeometry

/-!
# The unique diameter pair of the equal-parity quadrilateral

An exact quadratic identity places the quadrilateral in the disk with
diameter from the origin to `(1, 2 - sqrt 3)`. Equality in its diameter
bound identifies this pair, without replacing the quadrilateral by a
polygonal approximation.
-/

open Set
open Puzzling139335.N6.TripleSectors

namespace Puzzling139335.N6.TripleEqualParity

noncomputable section

def t : ℝ := 2 - Real.sqrt 3

def diagonalEnd : Plane := point 1 t

@[simp] theorem diagonalEnd_zero : diagonalEnd 0 = 1 := rfl

@[simp] theorem diagonalEnd_one : diagonalEnd 1 = t := rfl

theorem t_pos : 0 < t := sub_pos.mpr sqrt_three_lt_two

theorem t_lt_one : t < 1 := by
  unfold t
  linarith only [one_lt_sqrt_three]

theorem t_quadratic : t ^ 2 - 4 * t + 1 = 0 := by
  unfold t
  nlinarith only [sqrt_three_sq]

/-- The deficit from the circle with the named diameter is a sum of
products of defining nonnegative inequalities. -/
theorem circle_deficit_identity (x y : ℝ) :
    x - x ^ 2 + t * y - y ^ 2 =
      y * (2 - Real.sqrt 3 * x - y) +
        (x - Real.sqrt 3 * y) * (1 - x) := by
  unfold t
  ring

theorem circle_deficit_nonneg_of_bounds {p : Plane}
    (hp : 0 ≤ p 1 ∧ Real.sqrt 3 * p 1 ≤ p 0 ∧
      p 0 ≤ 1 ∧ Real.sqrt 3 * p 0 + p 1 ≤ 2) :
    0 ≤ p 0 - p 0 ^ 2 + t * p 1 - p 1 ^ 2 := by
  rw [circle_deficit_identity]
  exact add_nonneg (mul_nonneg hp.1 (by linarith only [hp.2.2.2]))
    (mul_nonneg (sub_nonneg.mpr hp.2.1) (sub_nonneg.mpr hp.2.2.1))

theorem diameter_deficit_identity (p q : Plane) :
    1 + t ^ 2 - dist p q ^ 2 =
      2 * (p 0 - p 0 ^ 2 + t * p 1 - p 1 ^ 2) +
      2 * (q 0 - q 0 ^ 2 + t * q 1 - q 1 ^ 2) +
      (p 0 + q 0 - 1) ^ 2 + (p 1 + q 1 - t) ^ 2 := by
  rw [plane_dist_sq]
  ring

theorem dist_sq_le_diagonal_of_bounds {p q : Plane}
    (hp : 0 ≤ p 1 ∧ Real.sqrt 3 * p 1 ≤ p 0 ∧
      p 0 ≤ 1 ∧ Real.sqrt 3 * p 0 + p 1 ≤ 2)
    (hq : 0 ≤ q 1 ∧ Real.sqrt 3 * q 1 ≤ q 0 ∧
      q 0 ≤ 1 ∧ Real.sqrt 3 * q 0 + q 1 ≤ 2) :
    dist p q ^ 2 ≤ 1 + t ^ 2 := by
  have hp0 := circle_deficit_nonneg_of_bounds hp
  have hq0 := circle_deficit_nonneg_of_bounds hq
  have hid := diameter_deficit_identity p q
  nlinarith only [hp0, hq0, hid, sq_nonneg (p 0 + q 0 - 1),
    sq_nonneg (p 1 + q 1 - t)]

theorem diameter_equality_coordinates_of_bounds {p q : Plane}
    (hp : 0 ≤ p 1 ∧ Real.sqrt 3 * p 1 ≤ p 0 ∧
      p 0 ≤ 1 ∧ Real.sqrt 3 * p 0 + p 1 ≤ 2)
    (hq : 0 ≤ q 1 ∧ Real.sqrt 3 * q 1 ≤ q 0 ∧
      q 0 ≤ 1 ∧ Real.sqrt 3 * q 0 + q 1 ≤ 2)
    (hd : dist p q ^ 2 = 1 + t ^ 2) :
    p 0 + q 0 = 1 ∧ p 1 + q 1 = t ∧
      p 0 - p 0 ^ 2 + t * p 1 - p 1 ^ 2 = 0 := by
  have hp0 := circle_deficit_nonneg_of_bounds hp
  have hq0 := circle_deficit_nonneg_of_bounds hq
  have hid := diameter_deficit_identity p q
  rw [hd] at hid
  have hx : (p 0 + q 0 - 1) ^ 2 = 0 := by
    nlinarith only [hp0, hq0, hid, sq_nonneg (p 0 + q 0 - 1),
      sq_nonneg (p 1 + q 1 - t)]
  have hy : (p 1 + q 1 - t) ^ 2 = 0 := by
    nlinarith only [hp0, hq0, hid, sq_nonneg (p 0 + q 0 - 1),
      sq_nonneg (p 1 + q 1 - t)]
  refine ⟨?_, ?_, ?_⟩
  · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hy)
  · nlinarith only [hp0, hq0, hid, hx, hy]

theorem second_eq_zero_of_first_eq_zero_of_bounds {p : Plane}
    (hp : 0 ≤ p 1 ∧ Real.sqrt 3 * p 1 ≤ p 0 ∧
      p 0 ≤ 1 ∧ Real.sqrt 3 * p 0 + p 1 ≤ 2) (hx : p 0 = 0) : p 1 = 0 := by
  have hw := hp.2.1
  rw [hx] at hw
  exact le_antisymm (nonpos_of_mul_nonpos_right hw sqrt_three_pos) hp.1

/-- The unique pair at the maximal distance consists of the two named
endpoints, in either order. -/
theorem endpoints_of_dist_sq_eq_diagonal_of_bounds {p q : Plane}
    (hp : 0 ≤ p 1 ∧ Real.sqrt 3 * p 1 ≤ p 0 ∧
      p 0 ≤ 1 ∧ Real.sqrt 3 * p 0 + p 1 ≤ 2)
    (hq : 0 ≤ q 1 ∧ Real.sqrt 3 * q 1 ≤ q 0 ∧
      q 0 ≤ 1 ∧ Real.sqrt 3 * q 0 + q 1 ≤ 2)
    (hd : dist p q ^ 2 = 1 + t ^ 2) :
    (p = 0 ∧ q = diagonalEnd) ∨ (p = diagonalEnd ∧ q = 0) := by
  obtain ⟨hsx, hsy, hdef⟩ := diameter_equality_coordinates_of_bounds hp hq hd
  have hx0 : 0 ≤ p 0 := (mul_nonneg sqrt_three_pos.le hp.1).trans hp.2.1
  have hyt : p 1 ≤ t := by linarith only [hsy, hq.1]
  have hprod : p 0 * (1 - p 0) = 0 := by
    have hxprod := mul_nonneg hx0 (sub_nonneg.mpr hp.2.2.1)
    have hyprod := mul_nonneg hp.1 (sub_nonneg.mpr hyt)
    nlinarith only [hxprod, hyprod, hdef]
  rcases mul_eq_zero.mp hprod with hx | hx
  · have hy := second_eq_zero_of_first_eq_zero_of_bounds hp hx
    left
    constructor
    · exact point_ext hx hy
    · apply point_ext
      · change q 0 = 1
        linarith only [hsx, hx]
      · change q 1 = t
        linarith only [hsy, hy]
  · have hqx : q 0 = 0 := by linarith only [hsx, hx]
    have hqy := second_eq_zero_of_first_eq_zero_of_bounds hq hqx
    right
    constructor
    · apply point_ext
      · change p 0 = 1
        linarith only [hx]
      · change p 1 = t
        linarith only [hsy, hqy]
    · exact point_ext hqx hqy

theorem dist_zero_diagonalEnd_sq : dist (0 : Plane) diagonalEnd ^ 2 = 1 + t ^ 2 := by
  rw [plane_dist_sq]
  simp [diagonalEnd, point]

theorem dist_sq_eq_diagonal_iff_of_bounds {p q : Plane}
    (hp : 0 ≤ p 1 ∧ Real.sqrt 3 * p 1 ≤ p 0 ∧
      p 0 ≤ 1 ∧ Real.sqrt 3 * p 0 + p 1 ≤ 2)
    (hq : 0 ≤ q 1 ∧ Real.sqrt 3 * q 1 ≤ q 0 ∧
      q 0 ≤ 1 ∧ Real.sqrt 3 * q 0 + q 1 ≤ 2) :
    dist p q ^ 2 = 1 + t ^ 2 ↔
      (p = 0 ∧ q = diagonalEnd) ∨ (p = diagonalEnd ∧ q = 0) := by
  constructor
  · exact endpoints_of_dist_sq_eq_diagonal_of_bounds hp hq
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact dist_zero_diagonalEnd_sq
    · simpa only [dist_comm] using dist_zero_diagonalEnd_sq

end

end Puzzling139335.N6.TripleEqualParity
