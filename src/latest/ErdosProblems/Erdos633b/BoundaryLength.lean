import ErdosProblems.Erdos633b.SegmentLength

/-! The outer side lengths are natural linear combinations of reference
tile sides. The coefficients count complete boundary edges of actual tiles. -/

namespace Erdos633b.Tiling

noncomputable instance {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    Fintype (d.BoundaryEdge i) := Fintype.ofFinite _

theorem side_eq_sum_boundaryEdges {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    T.side i = ∑ e : d.BoundaryEdge i, d.tile.side e.val.2 := by
  let A : d.BoundaryEdge i → Plane := fun e =>
    (d.tile.move (d.place e.val.1)).points (e.val.2 + 1)
  let B : d.BoundaryEdge i → Plane := fun e =>
    (d.tile.move (d.place e.val.1)).points (e.val.2 + 2)
  have hPQ : T.points (i + 1) ≠ T.points (i + 2) := T.independent.injective.ne
    ((by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) i)
  have hAB (e : d.BoundaryEdge i) : A e ≠ B e :=
    (d.tile.move (d.place e.val.1)).independent.injective.ne
      ((by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) e.val.2)
  have hc : (⋃ e, segment ℝ (A e) (B e)) =
      segment ℝ (T.points (i + 1)) (T.points (i + 2)) := by
    simpa only [boundaryEdges, Triangle.edge_eq_segment, A, B] using
      (d.edge_eq_boundaryEdges i).symm
  have hd : Pairwise fun e f => Disjoint (openSegment ℝ (A e) (B e))
      (openSegment ℝ (A f) (B f)) := by
    simpa only [Triangle.openEdge_eq_openSegment, A, B] using
      d.boundaryEdges_open_pairwise i
  have h := segment_partition_length (T.points (i + 1)) (T.points (i + 2)) hPQ A B hAB hc hd
  change T.side i = ∑ e : d.BoundaryEdge i,
    (d.tile.move (d.place e.val.1)).side e.val.2 at h
  simpa only [Triangle.side_move] using h

/-- Number of complete sides of index `j` occurring on outer side `i`. -/
noncomputable def boundarySideCount {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : d.BoundaryEdge i => e.val.2 = j)).card

theorem side_eq_sum_counts {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    T.side i = ∑ j : Fin 3, (d.boundarySideCount i j : ℝ) * d.tile.side j := by
  classical
  rw [d.side_eq_sum_boundaryEdges]
  rw [← Finset.sum_fiberwise' Finset.univ (fun e : d.BoundaryEdge i => e.val.2) d.tile.side]
  simp only [Finset.sum_const, nsmul_eq_mul, boundarySideCount]

theorem exists_side_coefficients {T : Triangle} {n : ℕ} (d : Tiling T n) :
    ∃ m : Fin 3 → Fin 3 → ℕ,
      ∀ i, T.side i = ∑ j : Fin 3, (m i j : ℝ) * d.tile.side j :=
  ⟨d.boundarySideCount, d.side_eq_sum_counts⟩

theorem side_eq_three_counts {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    T.side i = (d.boundarySideCount i 0 : ℝ) * d.tile.side 0 +
      (d.boundarySideCount i 1 : ℝ) * d.tile.side 1 +
      (d.boundarySideCount i 2 : ℝ) * d.tile.side 2 := by
  simpa only [Fin.sum_univ_three] using d.side_eq_sum_counts i

end Erdos633b.Tiling
