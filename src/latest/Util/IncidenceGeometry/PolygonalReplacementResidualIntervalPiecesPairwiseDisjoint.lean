import Util.IncidenceGeometry.PolygonalReplacementResidualIntervalPieceBasicData
import Util.IncidenceGeometry.PolygonalReplacementOutsideControlDisksDistinctEdgesDisjoint

open Classical
noncomputable section

universe u

lemma PolygonalReplacementResidualIntervalPiecesPairwiseDisjoint {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (B : PolygonalReplacementResidualIntervalPieceBasicData G D controlDisks
        boundaryPoints edgeEndpoints)
    (originalPiece_avoids_vertex_disk_interiors :
      ∀ i v,
        Disjoint (B.originalPiece i)
          (Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)))
    (originalPiece_avoids_intersection_disk_interiors :
      ∀ i (x : {p // p ∈ D.intersectionPoints}),
        Disjoint (B.originalPiece i)
          (Metric.ball x.1 (controlDisks.intersectionRadius x))) :
    ∀ ⦃i j : B.pieceIndex⦄, i ≠ j →
      Disjoint (B.originalPiece i) (B.originalPiece j) := by
  classical
  have distinct_edge_carriers_disjoint_outside :
      ∀ ⦃e₁ e₂ : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        e₁ ≠ e₂ →
          p ∈ D.edgeCarrier e₁ →
            p ∈ D.edgeCarrier e₂ →
              (∀ v : V,
                p ∉ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)) →
                (∀ x : {q // q ∈ D.intersectionPoints},
                  p ∉ Metric.ball x.1 (controlDisks.intersectionRadius x)) →
                  False :=
    PolygonalReplacementOutsideControlDisksDistinctEdgesDisjoint G D controlDisks
  have indexed_gap :
      ∀ (e : G.edgeFinset) (m d : ℕ)
        (hbound : m + d + 1 < (B.edgePieceOrder e).length),
          B.targetParam ((B.edgePieceOrder e)[m]) <
            B.sourceParam ((B.edgePieceOrder e)[m + d + 1]) := by
    intro e m d
    induction d with
    | zero =>
        intro hbound
        simpa [Nat.add_assoc] using
          B.edgePieceOrder_consecutive_param_order e m hbound
    | succ d ih =>
        intro hbound
        have hprev_bound : m + d + 1 < (B.edgePieceOrder e).length := by
          omega
        have hprev :
            B.targetParam ((B.edgePieceOrder e)[m]) <
              B.sourceParam ((B.edgePieceOrder e)[m + d + 1]) :=
          ih hprev_bound
        have hinside :
            B.sourceParam ((B.edgePieceOrder e)[m + d + 1]) <
              B.targetParam ((B.edgePieceOrder e)[m + d + 1]) :=
          B.sourceParam_lt_targetParam ((B.edgePieceOrder e)[m + d + 1])
        have hnext :
            B.targetParam ((B.edgePieceOrder e)[m + d + 1]) <
              B.sourceParam ((B.edgePieceOrder e)[m + d + 1 + 1]) :=
          B.edgePieceOrder_consecutive_param_order e (m + d + 1) (by omega)
        have hgap :
            B.targetParam ((B.edgePieceOrder e)[m]) <
              B.sourceParam ((B.edgePieceOrder e)[m + d + 1 + 1]) :=
          lt_trans (lt_trans hprev hinside) hnext
        simpa [Nat.add_assoc, Nat.succ_eq_add_one] using hgap
  have ordered_gap :
      ∀ (e : G.edgeFinset) (m n : ℕ)
        (hm : m < (B.edgePieceOrder e).length)
        (hn : n < (B.edgePieceOrder e).length),
          m < n →
            B.targetParam ((B.edgePieceOrder e)[m]) <
              B.sourceParam ((B.edgePieceOrder e)[n]) := by
    intro e m n hm hn hmn
    let d := n - (m + 1)
    have hn_eq : n = m + d + 1 := by
      dsimp [d]
      omega
    have hbound : m + d + 1 < (B.edgePieceOrder e).length := by
      simpa [← hn_eq] using hn
    simpa [hn_eq] using indexed_gap e m d hbound
  have same_owner_ordered_gap :
      ∀ {e : G.edgeFinset} {i j : B.pieceIndex},
        B.owner i = e → B.owner j = e → i ≠ j →
          B.targetParam i < B.sourceParam j ∨
            B.targetParam j < B.sourceParam i := by
    intro e i j hi_owner hj_owner hij
    have hi_mem : i ∈ B.edgePieceOrder e :=
      (B.edgePieceOrder_owner_iff e i).2 hi_owner
    have hj_mem : j ∈ B.edgePieceOrder e :=
      (B.edgePieceOrder_owner_iff e j).2 hj_owner
    rcases (List.mem_iff_getElem.mp hi_mem) with ⟨m, hm, hmi⟩
    rcases (List.mem_iff_getElem.mp hj_mem) with ⟨n, hn, hnj⟩
    have hmn_ne : m ≠ n := by
      intro hmn
      subst n
      exact hij (hmi.symm.trans hnj)
    by_cases hmn : m < n
    · left
      have hgap := ordered_gap e m n hm hn hmn
      simpa [hmi, hnj] using hgap
    · right
      have hnm : n < m := by omega
      have hgap := ordered_gap e n m hn hm hnm
      simpa [hmi, hnj] using hgap
  intro i j hij
  rw [Set.disjoint_left]
  intro p hpi hpj
  by_cases howner : B.owner i = B.owner j
  · have hgap :=
      same_owner_ordered_gap (e := B.owner i) (i := i) (j := j) rfl
        (by simp [← howner]) hij
    have hpi_image :
        p ∈ B.edgeParam (B.owner i) ''
          Set.Icc (B.sourceParam i) (B.targetParam i) := by
      simpa [B.originalPiece_eq_parameter_interval i] using hpi
    have hpj_image :
        p ∈ B.edgeParam (B.owner j) ''
          Set.Icc (B.sourceParam j) (B.targetParam j) := by
      simpa [B.originalPiece_eq_parameter_interval j] using hpj
    rcases hpi_image with ⟨u, hu, hpu⟩
    rcases hpj_image with ⟨v, hv, hpv⟩
    have hpv' : B.edgeParam (B.owner i) v = p := by
      simpa [← howner] using hpv
    have huv : u = v := by
      exact (B.edgeParam_spec (B.owner i)).2.1 (hpu.trans hpv'.symm)
    rcases hgap with hgap | hgap
    · have hle : B.sourceParam j ≤ B.targetParam i := by
        calc
          B.sourceParam j ≤ v := hv.1
          _ = u := huv.symm
          _ ≤ B.targetParam i := hu.2
      exact (not_lt_of_ge hle) hgap
    · have hle : B.sourceParam i ≤ B.targetParam j := by
        calc
          B.sourceParam i ≤ u := hu.1
          _ = v := huv
          _ ≤ B.targetParam j := hv.2
      exact (not_lt_of_ge hle) hgap
  · have hcarrier_i : p ∈ D.edgeCarrier (B.owner i) :=
      B.originalPiece_subset_owner i hpi
    have hcarrier_j : p ∈ D.edgeCarrier (B.owner j) :=
      B.originalPiece_subset_owner j hpj
    have hnot_vertex :
        ∀ v : V,
          p ∉ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v) := by
      intro v hpball
      exact
        (Set.disjoint_left.mp
          (originalPiece_avoids_vertex_disk_interiors i v)) hpi hpball
    have hnot_intersection :
        ∀ x : {q // q ∈ D.intersectionPoints},
          p ∉ Metric.ball x.1 (controlDisks.intersectionRadius x) := by
      intro x hpball
      exact
        (Set.disjoint_left.mp
          (originalPiece_avoids_intersection_disk_interiors i x)) hpi hpball
    exact distinct_edge_carriers_disjoint_outside howner hcarrier_i hcarrier_j
      hnot_vertex hnot_intersection
