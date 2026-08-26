import ErdosProblems.Erdos633b.BoundaryTopology

/-! Every outer side is exactly a finite union of whole tile edges.
Isolated vertex contacts cannot fill a gap in this closed union. -/

namespace Erdos633b

theorem segment_subset_closed_of_finite_remainder {P Q : Plane} (hPQ : P ≠ Q)
    {C F : Set Plane} (hC : IsClosed C) (hF : F.Finite)
    (hcover : segment ℝ P Q ⊆ C ∪ F) : segment ℝ P Q ⊆ C := by
  let L : ℝ → Plane := AffineMap.lineMap P Q
  have hL : Continuous L :=
    (AffineMap.lineMap P Q : ℝ →ᵃ[ℝ] Plane).continuous_of_finiteDimensional
  have hLf : Function.Injective L := AffineMap.lineMap_injective ℝ hPQ
  have hpre : (L ⁻¹' F).Finite := Set.Finite.preimage hLf.injOn hF
  have hd : Dense (Set.univ \ L ⁻¹' F) := dense_univ.sdiff_finite hpre
  have hcpre : IsClosed (L ⁻¹' C) := hC.preimage hL
  have hIo : Set.Ioo (0 : ℝ) 1 ⊆ L ⁻¹' C := by
    intro t ht
    rw [← hcpre.closure_eq]
    rw [mem_closure_iff]
    intro U hU htU
    obtain ⟨r, hrU, hrD⟩ := hd.inter_open_nonempty (U ∩ Set.Ioo 0 1)
      (hU.inter isOpen_Ioo) ⟨t, htU, ht⟩
    refine ⟨r, hrU.1, ?_⟩
    have hr : L r ∈ segment ℝ P Q := lineMap_mem_segment ℝ P Q ⟨hrU.2.1.le, hrU.2.2.le⟩
    exact (hcover hr).resolve_right hrD.2
  have hIc : Set.Icc (0 : ℝ) 1 ⊆ L ⁻¹' C := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact closure_minimal hIo hcpre
  rw [segment_eq_image_lineMap]
  rintro p ⟨t, ht, rfl⟩
  exact hIc ht

namespace Triangle

theorem edge_isClosed (T : Triangle) (i : Fin 3) : IsClosed (T.edge i) :=
  T.support_isCompact.isClosed.inter
    (isClosed_eq (continuous_barycentric_coord T.affineBasis i) continuous_const)

end Triangle

namespace Tiling

/-- Edges of placed tiles lying on the specified outer edge. This subtype
is finite without requiring that the tiling be edge-to-edge. -/
def BoundaryEdge {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :=
  {e : Fin n × Fin 3 // (d.tile.move (d.place e.1)).edge e.2 ⊆ T.edge i}

instance {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) : Finite (d.BoundaryEdge i) := by
  unfold BoundaryEdge
  infer_instance

def boundaryEdges {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) : Set Plane :=
  ⋃ e : d.BoundaryEdge i, (d.tile.move (d.place e.val.1)).edge e.val.2

def vertices {T : Triangle} {n : ℕ} (d : Tiling T n) : Set Plane :=
  Set.range (fun e : Fin n × Fin 3 => d.place e.1 (d.tile.points e.2))

theorem vertices_finite {T : Triangle} {n : ℕ} (d : Tiling T n) : d.vertices.Finite :=
  Set.finite_range _

theorem boundaryEdges_isClosed {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    IsClosed (d.boundaryEdges i) := by
  apply isClosed_iUnion_of_finite
  intro e
  exact Triangle.edge_isClosed _ _

theorem edge_subset_boundaryEdges_union_vertices {T : Triangle} {n : ℕ}
    (d : Tiling T n) (i : Fin 3) : T.edge i ⊆ d.boundaryEdges i ∪ d.vertices := by
  intro p hp
  have houter := hp.1
  rw [← d.covers, Set.mem_iUnion] at houter
  obtain ⟨k, hk⟩ := houter
  let S : Triangle := d.tile.move (d.place k)
  have hS : S.support = d.place k '' d.tile.support := Triangle.support_move _ _
  have hST : S.support ⊆ T.support := by rw [hS]; exact d.piece_subset k
  have hpS : p ∈ S.support := by rwa [hS]
  rcases T.support_inter_edge_cases S hST i with he | ⟨j, he⟩ | ⟨j, he⟩
  · have hm : p ∈ S.support ∩ T.edge i := ⟨hpS, hp⟩
    rw [he] at hm
    exact hm.elim
  · right
    have hm : p ∈ ({S.points j} : Set Plane) := he ▸ ⟨hpS, hp⟩
    exact ⟨(k, j), (Set.mem_singleton_iff.mp hm).symm⟩
  · left
    have hsub : S.edge j ⊆ T.edge i := by rw [← he]; exact Set.inter_subset_right
    exact Set.mem_iUnion.mpr ⟨⟨(k, j), hsub⟩, he ▸ ⟨hpS, hp⟩⟩

theorem edge_eq_boundaryEdges {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    T.edge i = d.boundaryEdges i := by
  apply Set.Subset.antisymm
  · have hPQ : T.points (i + 1) ≠ T.points (i + 2) := T.independent.injective.ne
      ((by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) i)
    rw [T.edge_eq_segment]
    apply segment_subset_closed_of_finite_remainder hPQ (d.boundaryEdges_isClosed i)
      d.vertices_finite
    rw [← T.edge_eq_segment]
    exact d.edge_subset_boundaryEdges_union_vertices i
  · intro p hp
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hp
    exact e.property he

theorem boundaryEdges_open_pairwise {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    Pairwise fun e f : d.BoundaryEdge i =>
      Disjoint ((d.tile.move (d.place e.val.1)).openEdge e.val.2)
        ((d.tile.move (d.place f.val.1)).openEdge f.val.2) := by
  intro e f hef
  by_cases htile : e.val.1 = f.val.1
  · have hedge : e.val.2 ≠ f.val.2 := by
      intro h
      apply hef
      exact Subtype.ext (Prod.ext htile h)
    have h := Triangle.openEdge_disjoint (d.tile.move (d.place e.val.1)) hedge
    simpa only [htile] using h
  · exact d.boundary_openEdges_disjoint htile i e.val.2 f.val.2 e.property f.property

end Tiling

end Erdos633b
