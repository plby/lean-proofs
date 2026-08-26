import ErdosProblems.Erdos633b.BoundaryIntervalChain
import ErdosProblems.Erdos633b.BoundaryLength

/-! Endpoint collisions transported to actual boundary edges by injective
real affine coordinates on the outer segment. -/

namespace Erdos633b

theorem segment_partition_endpoint_collision {ι : Type*} [Finite ι]
    (P Q : Plane) (hPQ : P ≠ Q) (A B selected : ι → Plane) (hAB : ∀ i, A i ≠ B i)
    (hc : (⋃ i, segment ℝ (A i) (B i)) = segment ℝ P Q)
    (hd : Pairwise fun i j => Disjoint (openSegment ℝ (A i) (B i))
      (openSegment ℝ (A j) (B j)))
    (he : ∀ i, selected i = A i ∨ selected i = B i)
    (hP : ∀ i, selected i ≠ P) (hQ : ∀ i, selected i ≠ Q) :
    ∃ i j, i ≠ j ∧ selected i = selected j := by
  classical
  obtain ⟨a, b, hAa, hBb, hab, hcover, hdisj⟩ :=
    segment_partition_coordinates P Q hPQ A B hAB hc hd
  let L : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap P Q
  let chosen : ι → ℝ := fun i => if selected i = A i then a i else b i
  have hchosen (i : ι) : chosen i = a i ∨ chosen i = b i := by
    by_cases h : selected i = A i <;> simp only [chosen, h, if_true, if_false, or_true, true_or]
  have hL (i : ι) : L (chosen i) = selected i := by
    by_cases h : selected i = A i
    · simpa only [chosen, if_pos h] using (hAa i).trans h.symm
    · simpa only [chosen, if_neg h] using (hBb i).trans ((he i).resolve_left h).symm
  have h0 (i : ι) : chosen i ≠ 0 := by
    intro h
    have hz := hL i
    rw [h] at hz
    exact hP i (hz.symm.trans (AffineMap.lineMap_apply_zero P Q))
  have h1 (i : ι) : chosen i ≠ 1 := by
    intro h
    have hz := hL i
    rw [h] at hz
    exact hQ i (hz.symm.trans (AffineMap.lineMap_apply_one P Q))
  have horder (i : ι) : min (a i) (b i) < max (a i) (b i) := min_lt_max.mpr (hab i)
  have he' (i : ι) : chosen i = min (a i) (b i) ∨ chosen i = max (a i) (b i) := by
    rcases le_total (a i) (b i) with h | h
    · simpa only [min_eq_left h, max_eq_right h] using hchosen i
    · simpa only [min_eq_right h, max_eq_left h] using (hchosen i).symm
  simp_rw [segment_eq_Icc'] at hcover
  simp_rw [openSegment_eq_Ioo' (hab _)] at hdisj
  obtain ⟨i, j, hij, heq⟩ := IntervalPartition.endpoint_collision
    (fun i => min (a i) (b i)) (fun i => max (a i) (b i)) chosen horder hcover hdisj he' h0 h1
  exact ⟨i, j, hij, (hL i).symm.trans ((congrArg L heq).trans (hL j))⟩

namespace Tiling

theorem boundary_endpoint_collision {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3)
    (selected : d.BoundaryEdge i → Plane)
    (he : ∀ e, selected e = (d.tile.move (d.place e.val.1)).points (e.val.2 + 1) ∨
      selected e = (d.tile.move (d.place e.val.1)).points (e.val.2 + 2))
    (hP : ∀ e, selected e ≠ T.points (i + 1))
    (hQ : ∀ e, selected e ≠ T.points (i + 2)) :
    ∃ e f, e ≠ f ∧ selected e = selected f := by
  let A : d.BoundaryEdge i → Plane := fun e =>
    (d.tile.move (d.place e.val.1)).points (e.val.2 + 1)
  let B : d.BoundaryEdge i → Plane := fun e =>
    (d.tile.move (d.place e.val.1)).points (e.val.2 + 2)
  have hPQ : T.points (i + 1) ≠ T.points (i + 2) := T.independent.injective.ne
    ((by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) i)
  have hAB (e : d.BoundaryEdge i) : A e ≠ B e :=
    (d.tile.move (d.place e.val.1)).independent.injective.ne
      ((by decide : ∀ j : Fin 3, j + 1 ≠ j + 2) e.val.2)
  have hc : (⋃ e, segment ℝ (A e) (B e)) =
      segment ℝ (T.points (i + 1)) (T.points (i + 2)) := by
    simpa only [boundaryEdges, Triangle.edge_eq_segment, A, B] using
      (d.edge_eq_boundaryEdges i).symm
  have hd : Pairwise fun e f => Disjoint (openSegment ℝ (A e) (B e))
      (openSegment ℝ (A f) (B f)) := by
    simpa only [Triangle.openEdge_eq_openSegment, A, B] using d.boundaryEdges_open_pairwise i
  exact segment_partition_endpoint_collision _ _ hPQ A B selected hAB hc hd he hP hQ

end Tiling

end Erdos633b
