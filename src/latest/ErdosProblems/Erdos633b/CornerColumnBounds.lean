import ErdosProblems.Erdos633b.NonouterAngleSums
import ErdosProblems.Erdos633b.AngleCoefficientIndependence
import ErdosProblems.Erdos633b.AngleCountBound

/-! The corner-column bound for an actual tiling with incommensurable outer
angles and one missing corner angle. Local angle equations are now derived. -/

namespace Erdos633b.Tiling

theorem corner_columns_le_three {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) :
    d.cornerColumnCount 0 ≤ 3 ∧ d.cornerColumnCount 1 ≤ 3 := by
  classical
  choose k hkpos hkbound hsum using d.nonouter_vertex_angle_multiple
  have he (v : d.NonouterVertex) :
      d.vertexAngleCount v.val 0 + d.cornerColumnCount 0 * d.vertexAngleCount v.val 2 =
        d.cornerColumnCount 0 * k v + d.vertexAngleCount v.val 2 ∧
      d.vertexAngleCount v.val 1 + d.cornerColumnCount 1 * d.vertexAngleCount v.val 2 =
        d.cornerColumnCount 1 * k v + d.vertexAngleCount v.val 2 := by
    apply d.vertex_angle_integer_equations h2 hirr
    simpa only [Fin.sum_univ_three] using hsum v
  exact corner_bounds_of_inventory
    (fun v : d.NonouterVertex => d.vertexAngleCount v.val 0)
    (fun v : d.NonouterVertex => d.vertexAngleCount v.val 1)
    (fun v : d.NonouterVertex => d.vertexAngleCount v.val 2)
    k (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (d.other_corner_columns_pos h2 hirr).1 (d.nonouter_count_balance h2 0) hkbound
    (fun v => (he v).1) (fun v => (he v).2)

theorem corner_columns_between_one_three {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi)) :
    1 ≤ d.cornerColumnCount 0 ∧ d.cornerColumnCount 0 ≤ 3 ∧
      1 ≤ d.cornerColumnCount 1 ∧ d.cornerColumnCount 1 ≤ 3 := by
  have hpos := d.other_corner_columns_pos h2 hirr
  have hbound := d.corner_columns_le_three h2 hirr
  omega

end Erdos633b.Tiling
