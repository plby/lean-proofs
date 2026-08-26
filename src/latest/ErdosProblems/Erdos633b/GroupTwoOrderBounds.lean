import ErdosProblems.Erdos633b.ConicAreaObstructions
import ErdosProblems.Erdos633b.GroupTwoSixtyMetric
import ErdosProblems.Erdos633b.SixAngleShapes

/-! Exact primitive-order degree bounds for actual tilings in all four
group-2 outer shapes. Boundary rows and area discharge every algebraic premise. -/

namespace Erdos633b.Tiling

theorem groupTwo_first_totient_bound {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) (D : ℕ) (hD : 0 < D)
    (hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) D) :
    D.totient ≤ 8 := by
  by_contra hn
  have hi := d.tile.groupTwo_quadratic_independent_of_order hg D hD hz (lt_of_not_ge hn)
  obtain ⟨hY, hZ⟩ := d.tile.caseFive_normalized_sides T hg h0 h1 h2
  simp only [d.conic_normalized_boundary] at hY hZ
  exact conic_first_shape_obstruction _ _ (d.tile.groupTwo_normalized_conic hg)
    d.boundarySideCount (d.conic_boundary_row_pos 0) hY hZ hi

theorem groupTwo_second_totient_bound {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) (D : ℕ) (hD : 0 < D)
    (hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) D) :
    D.totient ≤ 8 := by
  by_contra hn
  have hi := d.tile.groupTwo_quadratic_independent_of_order hg D hD hz (lt_of_not_ge hn)
  obtain ⟨hX, hY, hZ⟩ := d.tile.caseEight_normalized_sides T hg h0 h1 h2
  simp only [d.conic_normalized_boundary] at hX hY hZ
  apply conic_second_shape_obstruction _ _ (div_pos (d.tile.side_pos 0) (d.tile.side_pos 2))
    (d.tile.groupTwo_normalized_conic hg) d.boundarySideCount (d.conic_boundary_row_pos 0)
    _ _ hi
  · rw [hY, hX]
    ring
  · rw [hZ, hX]
    ring

theorem groupTwo_third_totient_bound {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = d.tile.angle 0 + d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) (D : ℕ) (hD : 0 < D)
    (hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) D) :
    D.totient ≤ 8 := by
  by_contra hn
  have hi := d.tile.groupTwo_quadratic_independent_of_order hg D hD hz (lt_of_not_ge hn)
  obtain ⟨hX, hZ⟩ := d.tile.groupTwoSixty_normalized_sides T hg h0 h1 h2
  simp only [d.conic_normalized_boundary] at hX hZ
  have harea := d.normalized_count_of_shared_angle h0
  simp only [d.conic_normalized_boundary] at harea
  apply conic_third_shape_obstruction _ _ d.boundarySideCount n (d.conic_boundary_row_pos 1)
    _ hZ _ hi
  · simpa only [mul_comm] using hX
  · exact (eq_div_iff (div_ne_zero (d.tile.side_pos 1).ne' (d.tile.side_pos 2).ne')).mp harea

theorem groupTwo_fourth_totient_bound {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = 2 * d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + d.tile.angle 1) (D : ℕ) (hD : 0 < D)
    (hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) D) :
    D.totient ≤ 12 := by
  by_contra hn
  have hi := d.tile.groupTwo_cubic_independent_of_order hg D hD hz (lt_of_not_ge hn)
  have hX := (d.tile.groupTwoDouble_normalized_sides T hg h0 h1 h2).1
  simp only [d.conic_normalized_boundary] at hX
  apply conic_fourth_shape_obstruction _ _ (d.tile.groupTwo_normalized_conic hg)
    d.boundarySideCount (d.conic_boundary_row_pos 2) _ hi
  simpa only [mul_assoc] using hX

theorem groupTwo_order_totient_bound {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hshape : GroupTwoShape d.tile T) (D : ℕ) (hD : 0 < D)
    (hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) D) :
    D.totient ≤ 12 := by
  obtain ⟨hg, hs⟩ := hshape
  rcases hs with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact (d.groupTwo_first_totient_bound hg h0 h1 h2 D hD hz).trans (by decide)
  · exact (d.groupTwo_second_totient_bound hg h0 h1 h2 D hD hz).trans (by decide)
  · exact (d.groupTwo_third_totient_bound hg h0 h1 h2 D hD hz).trans (by decide)
  · exact d.groupTwo_fourth_totient_bound hg h0 h1 h2 D hD hz

end Erdos633b.Tiling
