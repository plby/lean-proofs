import ErdosProblems.Erdos633b.LocalAngleTypes
import Mathlib.Algebra.Ring.Parity

/-! Exact incidence cardinalities and the parity required by the group-1
coloring argument, including a tile passing through an interior vertex. -/

namespace Erdos633b.Tiling

theorem vertexPiece_card_eq_counts {T : Triangle} {n : ℕ} (d : Tiling T n) (p : d.Vertex) :
    Fintype.card (d.VertexPiece p.val) = ∑ j : Fin 3, d.vertexAngleCount p j := by
  have h := Fintype.card_congr (d.vertexPieceEquiv p)
  simpa only [Fintype.card_sigma, vertexAngleCount] using h.symm

theorem incidentPiece_card_eq_vertex_add_edge {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p) :
    Fintype.card (d.IncidentPiece p) =
      Fintype.card (d.VertexPiece p) + Fintype.card (d.EdgePiece p) := by
  simpa only [Fintype.card_sum] using (Fintype.card_congr (d.incidenceSumEquiv a j ha)).symm

theorem groupOne_vertexPiece_card_mod_two {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) (p : d.Vertex) (k : ℕ)
    (hk : k = 1 ∨ k = 2)
    (hs : (∑ e : d.VertexPiece p.val, d.tile.angle e.val.2) = k * Real.pi) :
    Fintype.card (d.VertexPiece p.val) % 2 = k % 2 := by
  have hsum : (d.vertexAngleCount p 0 : ℝ) * d.tile.angle 0 +
      (d.vertexAngleCount p 1 : ℝ) * d.tile.angle 1 +
      (d.vertexAngleCount p 2 : ℝ) * d.tile.angle 2 = k * Real.pi := by
    simpa only [d.vertex_angle_sum_eq_counts, Fin.sum_univ_three] using hs
  have htype := d.tile.groupOne_local_angle_type hrel hirr _ _ _ k hk hsum
  rw [d.vertexPiece_card_eq_counts, Fin.sum_univ_three]
  exact groupOne_vertex_count_mod_two _ _ _ k htype

theorem groupOne_interior_incident_even {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) (p : d.Vertex)
    (hp : p.val ∈ interior T.support) : Even (Fintype.card (d.IncidentPiece p.val)) := by
  obtain ⟨⟨a, j⟩, ha⟩ := p.property
  have hsum : ∃ k : ℕ, (k = 1 ∨ k = 2) ∧
      (∑ e : d.VertexPiece p.val, d.tile.angle e.val.2) = k * Real.pi := by
    rcases d.interior_vertex_angle_sum hp a j ha with h | h
    · exact ⟨1, Or.inl rfl, by simpa only [Nat.cast_one, one_mul] using h⟩
    · exact ⟨2, Or.inr rfl, by simpa only [Nat.cast_ofNat] using h⟩
  obtain ⟨k, hk, hs⟩ := hsum
  have hmod := d.groupOne_vertexPiece_card_mod_two hrel hirr p k hk hs
  have hbalance := d.interior_vertex_angle_balance hp a j ha
  rw [hs] at hbalance
  have hreal : (k : ℝ) + (Fintype.card (d.EdgePiece p.val) : ℝ) = 2 := by
    nlinarith [Real.pi_pos]
  have hnat : k + Fintype.card (d.EdgePiece p.val) = 2 := by exact_mod_cast hreal
  apply Nat.even_iff.mpr
  rw [d.incidentPiece_card_eq_vertex_add_edge a j ha]
  omega

theorem boundary_edgePiece_isEmpty {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : d.Vertex) (i : Fin 3) (hp : p.val ∈ T.openEdge i) : IsEmpty (d.EdgePiece p.val) := by
  obtain ⟨⟨a, j⟩, ha⟩ := p.property
  refine ⟨fun e => ?_⟩
  have hep : p.val ∈ d.place e.val.1 '' d.tile.support := by
    rw [← Triangle.support_move]
    exact ((d.tile.move (d.place e.val.1)).openEdge_subset_edge e.val.2 e.property).1
  obtain ⟨k, hk⟩ := d.boundary_vertex_of_mem_piece i (T.openEdge_subset_edge i hp) a j ha
    e.val.1 hep
  apply (d.tile.move (d.place e.val.1)).vertex_not_mem_openEdge e.val.2 k
  have hpoint : (d.tile.move (d.place e.val.1)).points k = p.val := hk
  simpa only [hpoint] using e.property

theorem groupOne_boundary_incident_odd {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrel : 3 * d.tile.angle 0 + 2 * d.tile.angle 1 = Real.pi)
    (hirr : Irrational (d.tile.angle 0 / Real.pi)) (p : d.Vertex) (i : Fin 3)
    (hp : p.val ∈ T.openEdge i) : Odd (Fintype.card (d.IncidentPiece p.val)) := by
  obtain ⟨⟨a, j⟩, ha⟩ := p.property
  have hs : (∑ e : d.VertexPiece p.val, d.tile.angle e.val.2) = (1 : ℕ) * Real.pi := by
    simpa only [Nat.cast_one, one_mul] using d.boundary_vertex_angle_sum i hp a j ha
  have hmod := d.groupOne_vertexPiece_card_mod_two hrel hirr p 1 (Or.inl rfl) hs
  let _ := d.boundary_edgePiece_isEmpty p i hp
  have hz : Fintype.card (d.EdgePiece p.val) = 0 := Fintype.card_eq_zero
  apply Nat.odd_iff.mpr
  rw [d.incidentPiece_card_eq_vertex_add_edge a j ha, hz, add_zero]
  exact hmod

end Erdos633b.Tiling
