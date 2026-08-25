import StackExchange.Puzzling139335.UnitPairs.SideSupport

/-!
# The unit partner at a supported diagonal corner

The hypotheses below concern actual points of the piece. In particular,
the positive diagonal sample is not inferred from a convex-hull chord.
A square-side placement of a unit pair forces the sample and the
bottom-left corner to lie on the same side of the pair. The diagonal
support bound then locates any second partner strictly above height one half.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

/-- A point on the diagonal issuing into the square from the bottom-right
corner. A positive parameter makes this point distinct from that corner. -/
def diagonalSample (t : ℝ) : Plane := !₂[1 - t, t]

@[simp] theorem diagonalSample_zero (t : ℝ) : diagonalSample t 0 = 1 - t := rfl

@[simp] theorem diagonalSample_one (t : ℝ) : diagonalSample t 1 = t := rfl

theorem diagonal_sample_sideDet_product (b : Plane) (t : ℝ) :
    UnitPairs.sideDet (corner 1) b (corner 0) *
        UnitPairs.sideDet (corner 1) b (diagonalSample t) =
      (b 1 * t) * (b 0 + b 1 - 1) := by
  simp [UnitPairs.sideDet, corner, diagonalSample]
  ring

/-- A point of the square at unit distance from the bottom-right corner
and on the bottom edge is the bottom-left corner. -/
theorem unit_partner_on_bottom_eq_corner_zero {b : Plane}
    (hb : b ∈ unitSquare) (hd : dist (corner 1) b = 1) (hy : b 1 = 0) :
    b = corner 0 := by
  have hsquare : dist (corner 1) b ^ 2 = 1 := by rw [hd]; norm_num
  rw [plane_dist_sq] at hsquare
  have hx : b 0 = 0 := by
    norm_num [corner, Fin.ext_iff, hy] at hsquare
    rcases hsquare with hzero | htwo
    · exact hzero
    · linarith only [htwo, hb.1.2]
  ext i
  fin_cases i
  · simpa [corner] using hx
  · simpa [corner] using hy

/-- At a diagonal supporting corner, an actual unit-side partner other
than the bottom-left corner lies on the diagonal support line. -/
theorem diagonal_partner_on_support {P : Set Plane} {b : Plane} {t : ℝ}
    (hP : P ⊆ unitSquare) (hr : corner 0 ∈ P)
    (hsupport : ∀ p ∈ P, p 0 + p 1 ≤ 1)
    (ht : 0 < t) (hsample : diagonalSample t ∈ P)
    (hpair : UnitPairs.IsUnitSidePair P (corner 1) b) (hne : b ≠ corner 0) :
    b 0 + b 1 = 1 := by
  have hb : b ∈ unitSquare := hP hpair.2.1
  have hyne : b 1 ≠ 0 := by
    intro hy
    exact hne (unit_partner_on_bottom_eq_corner_zero hb hpair.2.2.1 hy)
  have hy : 0 < b 1 := lt_of_le_of_ne hb.2.1 (Ne.symm hyne)
  have hdet := hpair.sideDet_mul_nonneg hr hsample
  rw [diagonal_sample_sideDet_product] at hdet
  have hsum : 0 ≤ b 0 + b 1 - 1 :=
    (mul_nonneg_iff_of_pos_left (mul_pos hy ht)).mp hdet
  linarith only [hsum, hsupport b hpair.2.1]

/-- The diagonal support point at distance one from the bottom-right
corner has height strictly greater than one half. -/
theorem diagonal_partner_second_gt_half {P : Set Plane} {b : Plane} {t : ℝ}
    (hP : P ⊆ unitSquare) (hr : corner 0 ∈ P)
    (hsupport : ∀ p ∈ P, p 0 + p 1 ≤ 1)
    (ht : 0 < t) (hsample : diagonalSample t ∈ P)
    (hpair : UnitPairs.IsUnitSidePair P (corner 1) b) (hne : b ≠ corner 0) :
    (1 / 2 : ℝ) < b 1 := by
  have hb : b ∈ unitSquare := hP hpair.2.1
  have hsum := diagonal_partner_on_support hP hr hsupport ht hsample hpair hne
  have hsquare : dist (corner 1) b ^ 2 = 1 := by rw [hpair.2.2.1]; norm_num
  rw [plane_dist_sq] at hsquare
  have hx : b 0 = 1 - b 1 := by linarith only [hsum]
  norm_num [corner, Fin.ext_iff, hx] at hsquare
  by_contra hnot
  have hhalf : b 1 ≤ 1 / 2 := le_of_not_gt hnot
  have hproduct := mul_nonneg (sub_nonneg.mpr hhalf)
    (show 0 ≤ 1 / 2 + b 1 by linarith only [hb.2.1])
  nlinarith only [hsquare, hproduct]

/-- The supported diagonal corner has no second actual unit-side partner
in a piece contained in the lower half of the square. -/
theorem diagonal_partner_lower_half_impossible {P : Set Plane} {b : Plane} {t : ℝ}
    (hP : P ⊆ unitSquare) (hr : corner 0 ∈ P)
    (hhalf : ∀ p ∈ P, p 1 ≤ 1 / 2)
    (hsupport : ∀ p ∈ P, p 0 + p 1 ≤ 1)
    (ht : 0 < t) (hsample : diagonalSample t ∈ P)
    (hpair : UnitPairs.IsUnitSidePair P (corner 1) b) (hne : b ≠ corner 0) :
    False :=
  (not_lt_of_ge (hhalf b hpair.2.1))
    (diagonal_partner_second_gt_half hP hr hsupport ht hsample hpair hne)

end Puzzling139335.N6.TwoDouble
