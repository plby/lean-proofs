import ErdosProblems.Erdos633b.BoundaryEdgeIncidence
import ErdosProblems.Erdos633b.EdgeLengthMeasure
import ErdosProblems.Erdos633b.CornerAngles

/-! The weighted edge identity holds pointwise off the actual finite
vertex set. An odd direction weight cancels on every internal pair. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

namespace Triangle

noncomputable def edgeWeightAt (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (u : Plane) (w : Real.Angle → ℝ) (p : Plane) : ℝ :=
  ∑ j : Fin 3, (S.openEdge j).indicator (fun _ => w (S.positiveEdgeDirection o u j)) p

theorem edgeWeightAt_eq_of_openEdge (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (u : Plane) (w : Real.Angle → ℝ) (i : Fin 3) {p : Plane} (hp : p ∈ S.openEdge i) :
    S.edgeWeightAt o u w p = w (S.positiveEdgeDirection o u i) := by
  classical
  unfold edgeWeightAt
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hp _
  · intro j _ hji
    apply Set.indicator_of_notMem
    exact fun hj => Set.disjoint_left.mp (S.openEdge_disjoint hji) hj hp
  · exact fun h => (h (Finset.mem_univ i)).elim

theorem edgeWeightAt_eq_zero_of_no_openEdge (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (u : Plane) (w : Real.Angle → ℝ) {p : Plane} (hp : ∀ i, p ∉ S.openEdge i) :
    S.edgeWeightAt o u w p = 0 := by
  unfold edgeWeightAt
  exact Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (hp i) _)

end Triangle
namespace Tiling

theorem sum_tile_edgeWeightAt_eq {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) (u : Plane) (w : Real.Angle → ℝ) (p : Plane) :
    (∑ a : Fin n, (d.tile.move (d.place a)).edgeWeightAt o u w p) =
      ∑ e : d.EdgePiece p,
        w ((d.tile.move (d.place e.val.1)).positiveEdgeDirection o u e.val.2) := by
  classical
  unfold Triangle.edgeWeightAt
  rw [← Fintype.sum_prod_type (fun e : Fin n × Fin 3 =>
    ((d.tile.move (d.place e.1)).openEdge e.2).indicator
      (fun _ => w ((d.tile.move (d.place e.1)).positiveEdgeDirection o u e.2)) p)]
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro e; simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]) _

theorem interior_edgeWeight_sum_zero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u p : Plane} (hu : u ≠ 0)
    (w : Real.Angle → ℝ) (hw : ∀ x, w (x + (Real.pi : Real.Angle)) = -w x)
    (hp : p ∈ interior T.support) (hv : p ∉ d.vertices) :
    (∑ e : d.EdgePiece p,
      w ((d.tile.move (d.place e.val.1)).positiveEdgeDirection o u e.val.2)) = 0 := by
  classical
  by_cases h : Nonempty (d.EdgePiece p)
  · let e := Classical.choice h
    obtain ⟨f, hfe⟩ := d.exists_other_edgePiece hp hv e
    have huniv : (Finset.univ : Finset (d.EdgePiece p)) = {e, f} := by
      symm
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, d.interior_edgePiece_card_eq_two hp hv e,
        Finset.card_pair hfe.symm]
    rw [huniv, Finset.sum_pair hfe.symm,
      d.edgePiece_positive_directions o hu hfe.symm, hw, neg_add_cancel]
  · let _ : IsEmpty (d.EdgePiece p) := not_nonempty_iff.mp h
    simp only [Finset.univ_eq_empty, Finset.sum_empty]

theorem boundary_edgeWeight_sum {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) (u : Plane) (w : Real.Angle → ℝ)
    {p : Plane} (i : Fin 3) (hp : p ∈ T.edge i) (hv : p ∉ d.vertices) :
    (∑ e : d.EdgePiece p,
      w ((d.tile.move (d.place e.val.1)).positiveEdgeDirection o u e.val.2)) =
        w (T.positiveEdgeDirection o u i) := by
  simp only [d.boundary_edgePiece_direction o u i hp, Finset.sum_const,
    Finset.card_univ, d.boundary_edgePiece_card_eq_one i hp hv, one_nsmul]

theorem edgeWeightAt_cancellation {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (w : Real.Angle → ℝ) (hw : ∀ x, w (x + (Real.pi : Real.Angle)) = -w x)
    {p : Plane} (hv : p ∉ d.vertices) :
    (∑ a : Fin n, (d.tile.move (d.place a)).edgeWeightAt o u w p) =
      T.edgeWeightAt o u w p := by
  classical
  rw [d.sum_tile_edgeWeightAt_eq]
  by_cases hpT : p ∈ T.support
  · by_cases hpint : p ∈ interior T.support
    · rw [d.interior_edgeWeight_sum_zero o hu w hw hpint hv]
      symm
      apply T.edgeWeightAt_eq_zero_of_no_openEdge
      intro i hi
      have hc := (T.mem_interior_support_iff_all_coords p).mp hpint i
      rw [hi.1] at hc
      exact lt_irrefl _ hc
    · obtain ⟨i, hi⟩ := T.openEdge_of_not_interior_nonvertex hpT hpint (by
        intro i he
        obtain ⟨a, j, ha⟩ := d.outer_vertex_is_tile_vertex i
        exact hv ⟨(a, j), ha.trans he.symm⟩)
      rw [d.boundary_edgeWeight_sum o u w i (T.openEdge_subset_edge i hi) hv,
        T.edgeWeightAt_eq_of_openEdge o u w i hi]
  · have hemp : IsEmpty (d.EdgePiece p) := ⟨fun e => hpT (d.piece_subset e.val.1 (by
      rw [← Triangle.support_move]
      exact ((d.tile.move (d.place e.val.1)).openEdge_subset_edge e.val.2 e.property).1))⟩
    let _ := hemp
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    symm
    exact T.edgeWeightAt_eq_zero_of_no_openEdge o u w
      (fun i hi => hpT (T.openEdge_subset_edge i hi).1)

end Tiling
end Erdos633b
