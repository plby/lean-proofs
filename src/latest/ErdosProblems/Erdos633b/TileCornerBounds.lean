import ErdosProblems.Erdos633b.TileAngleIndependence
import ErdosProblems.Erdos633b.CornerColumnBounds

/-! The actual corner-column bound with an incommensurable reference tile.
One of the two remaining columns may be zero. -/

namespace Erdos633b.Tiling

theorem corner_columns_le_three_of_tile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (d.tile.angle i / Real.pi)) :
    d.cornerColumnCount 0 ≤ 3 ∧ d.cornerColumnCount 1 ≤ 3 := by
  classical
  choose k hkpos hkbound hsum using d.nonouter_vertex_angle_multiple
  have he (v : d.NonouterVertex) :
      d.vertexAngleCount v.val 0 + d.cornerColumnCount 0 * d.vertexAngleCount v.val 2 =
        d.cornerColumnCount 0 * k v + d.vertexAngleCount v.val 2 ∧
      d.vertexAngleCount v.val 1 + d.cornerColumnCount 1 * d.vertexAngleCount v.val 2 =
        d.cornerColumnCount 1 * k v + d.vertexAngleCount v.val 2 := by
    apply d.vertex_angle_integer_equations_of_tile h2 hirr
    simpa only [Fin.sum_univ_three] using hsum v
  by_cases hP : 0 < d.cornerColumnCount 0
  · exact corner_bounds_of_inventory
      (fun v : d.NonouterVertex => d.vertexAngleCount v.val 0)
      (fun v : d.NonouterVertex => d.vertexAngleCount v.val 1)
      (fun v : d.NonouterVertex => d.vertexAngleCount v.val 2)
      k (d.cornerColumnCount 0) (d.cornerColumnCount 1) hP
      (d.nonouter_count_balance h2 0) hkbound (fun v => (he v).1) (fun v => (he v).2)
  · have hQ : 0 < d.cornerColumnCount 1 := by
      by_contra hn
      have hP0 : d.cornerColumnCount 0 = 0 := by omega
      have hQ0 : d.cornerColumnCount 1 = 0 := by omega
      have h := d.corner_two_angle_sum h2
      simp only [hP0, hQ0, Nat.cast_zero, zero_mul, zero_add] at h
      exact Real.pi_ne_zero h.symm
    have hb := corner_bounds_of_inventory
      (fun v : d.NonouterVertex => d.vertexAngleCount v.val 1)
      (fun v : d.NonouterVertex => d.vertexAngleCount v.val 0)
      (fun v : d.NonouterVertex => d.vertexAngleCount v.val 2)
      k (d.cornerColumnCount 1) (d.cornerColumnCount 0) hQ
      (d.nonouter_count_balance h2 1) hkbound (fun v => (he v).2) (fun v => (he v).1)
    exact ⟨hb.2, hb.1⟩

end Erdos633b.Tiling
