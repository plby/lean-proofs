import ErdosProblems.Erdos633b.IncidentPieceTypes

/-! The exact pi-or-two-pi angle sum at an actual interior tile vertex.
A tile whose open edge passes through the point contributes a straight angle. -/

namespace Erdos633b.Tiling

open scoped ENNReal

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem vertexPiece_sector_measure {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (p : Plane) (e : d.VertexPiece p) :
    CircleArcMeasure.measure (closedDirections o u p (d.tile.move (d.place e.val.1))) =
      ENNReal.ofReal (d.tile.angle e.val.2) := by
  have h := ((d.tile.move (d.place e.val.1)).vertex_sector_properties o hu e.val.2).2.2
  have he : (d.tile.move (d.place e.val.1)).points e.val.2 = p := e.property
  rw [he, Triangle.angle_move] at h
  exact h

theorem edgePiece_sector_measure {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (p : Plane) (e : d.EdgePiece p) :
    CircleArcMeasure.measure (closedDirections o u p (d.tile.move (d.place e.val.1))) =
      ENNReal.ofReal Real.pi :=
  ((d.tile.move (d.place e.val.1)).openEdge_sector_properties o hu e.val.2 e.property).2.2

theorem sum_vertex_and_edge_sector_measures {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u p : Plane} (hu : u ≠ 0)
    (hp : p ∈ interior T.support) (a : Fin n) (j : Fin 3)
    (ha : d.place a (d.tile.points j) = p) :
    (∑ e : d.VertexPiece p, ENNReal.ofReal (d.tile.angle e.val.2)) +
      (Fintype.card (d.EdgePiece p) : ℝ≥0∞) * ENNReal.ofReal Real.pi =
        ENNReal.ofReal (2 * Real.pi) := by
  classical
  have he := Fintype.sum_equiv (d.incidenceSumEquiv a j ha)
    (Sum.elim (fun e : d.VertexPiece p => ENNReal.ofReal (d.tile.angle e.val.2))
      (fun _ : d.EdgePiece p => ENNReal.ofReal Real.pi))
    (fun b : d.IncidentPiece p => CircleArcMeasure.measure
      (closedDirections o u p (d.tile.move (d.place b.val)))) (by
        intro x
        cases x with
        | inl e => exact (d.vertexPiece_sector_measure o hu p e).symm
        | inr e => exact (d.edgePiece_sector_measure o hu p e).symm)
  rw [Fintype.sum_sum_type, d.sum_incident_sector_measures o hu hp a j ha] at he
  simpa only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using he

theorem interior_vertex_angle_balance {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (hp : p ∈ interior T.support) (a : Fin n) (j : Fin 3)
    (ha : d.place a (d.tile.points j) = p) :
    (∑ e : d.VertexPiece p, d.tile.angle e.val.2) +
      (Fintype.card (d.EdgePiece p) : ℝ) * Real.pi = 2 * Real.pi := by
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let u : Plane := d.tile.points 1 - d.tile.points 0
  have hu : u ≠ 0 := sub_ne_zero.mpr (d.tile.independent.injective.ne (by decide))
  have he := d.sum_vertex_and_edge_sector_measures o hu hp a j ha
  rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => (d.tile.angle_pos e.val.2).le),
    ← ENNReal.ofReal_natCast (Fintype.card (d.EdgePiece p)),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (Finset.sum_nonneg (fun e _ => (d.tile.angle_pos e.val.2).le))
      (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)] at he
  exact (ENNReal.ofReal_eq_ofReal_iff
    (add_nonneg (Finset.sum_nonneg (fun e _ => (d.tile.angle_pos e.val.2).le))
      (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)) Real.two_pi_pos.le).mp he

theorem vertex_angle_sum_pos {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (a : Fin n) (j : Fin 3) (ha : d.place a (d.tile.points j) = p) :
    0 < ∑ e : d.VertexPiece p, d.tile.angle e.val.2 := by
  classical
  let e : d.VertexPiece p := ⟨(a, j), ha⟩
  have hle := Finset.single_le_sum (fun f (_ : f ∈ Finset.univ) => (d.tile.angle_pos f.val.2).le)
    (Finset.mem_univ e)
  exact (d.tile.angle_pos j).trans_le hle

theorem interior_edgePiece_card_le_one {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (hp : p ∈ interior T.support) (a : Fin n) (j : Fin 3)
    (ha : d.place a (d.tile.points j) = p) : Fintype.card (d.EdgePiece p) ≤ 1 := by
  have he := d.interior_vertex_angle_balance hp a j ha
  have hpos := d.vertex_angle_sum_pos a j ha
  have hlt : (Fintype.card (d.EdgePiece p) : ℝ) < 2 := by nlinarith [Real.pi_pos]
  have hn : Fintype.card (d.EdgePiece p) < 2 := by exact_mod_cast hlt
  omega

theorem interior_vertex_angle_sum {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (hp : p ∈ interior T.support) (a : Fin n) (j : Fin 3)
    (ha : d.place a (d.tile.points j) = p) :
    (∑ e : d.VertexPiece p, d.tile.angle e.val.2) = Real.pi ∨
      (∑ e : d.VertexPiece p, d.tile.angle e.val.2) = 2 * Real.pi := by
  have he := d.interior_vertex_angle_balance hp a j ha
  have hcard := d.interior_edgePiece_card_le_one hp a j ha
  have hc : Fintype.card (d.EdgePiece p) = 0 ∨ Fintype.card (d.EdgePiece p) = 1 := by omega
  rcases hc with hc | hc
  · right
    simpa only [hc, Nat.cast_zero, zero_mul, add_zero] using he
  · left
    rw [hc, Nat.cast_one, one_mul] at he
    linarith

end Erdos633b.Tiling
