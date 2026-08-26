import ErdosProblems.Erdos633b.InteriorVertexAngles
import ErdosProblems.Erdos633b.NonouterInventory

/-! At every actual nonouter vertex the sum of tile vertex angles is pi or
2 pi, including vertices on the outer boundary and non-edge-to-edge incidences. -/

namespace Erdos633b.Tiling

theorem nonouter_vertex_angle_sum {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : d.NonouterVertex) :
    (∑ j : Fin 3, (d.vertexAngleCount p.val j : ℝ) * d.tile.angle j) = Real.pi ∨
      (∑ j : Fin 3, (d.vertexAngleCount p.val j : ℝ) * d.tile.angle j) = 2 * Real.pi := by
  by_cases hp : p.val.val ∈ interior T.support
  · obtain ⟨⟨a, j⟩, ha⟩ := p.val.property
    rw [← d.vertex_angle_sum_eq_counts]
    exact d.interior_vertex_angle_sum hp a j ha
  · obtain ⟨i, hi⟩ := T.openEdge_of_not_interior_nonvertex (d.vertex_mem_support p.val) hp
      (d.nonouter_vertex_ne p)
    exact Or.inl (d.vertexAngleCount_boundary_sum p.val i hi)

theorem nonouter_vertex_angle_multiple {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : d.NonouterVertex) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ∧
      (∑ j : Fin 3, (d.vertexAngleCount p.val j : ℝ) * d.tile.angle j) = k * Real.pi := by
  rcases d.nonouter_vertex_angle_sum p with h | h
  · exact ⟨1, le_rfl, by norm_num, by simpa only [Nat.cast_one, one_mul] using h⟩
  · exact ⟨2, by norm_num, le_rfl, by simpa only [Nat.cast_ofNat] using h⟩

end Erdos633b.Tiling
