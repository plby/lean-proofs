import Util.IncidenceGeometry.PolygonalReplacementResidualPieceData
import Util.IncidenceGeometry.PositiveSeparation
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Data.Finset.Max

open Classical
noncomputable section

universe u

lemma PolygonalReplacementResidualPieceTubeNeighborhoods {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (residualPieceData :
      PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints) :
    ∃ tube : residualPieceData.pieceIndex → Set (EuclideanSpace ℝ (Fin 2)),
      (∀ i, IsOpen (tube i)) ∧
        (∀ i, residualPieceData.originalPiece i ⊆ tube i) ∧
          (∀ ⦃i j⦄, i ≠ j → Disjoint (tube i) (tube j)) := by
  classical
  let : Fintype residualPieceData.pieceIndex :=
    residualPieceData.pieceIndex_fintype
  let PairIndex : Type u :=
    {ij : residualPieceData.pieceIndex × residualPieceData.pieceIndex //
      ij.1 ≠ ij.2}
  have originalPiece_nonempty :
      ∀ i, (residualPieceData.originalPiece i).Nonempty := by
    intro i
    exact ⟨residualPieceData.source i,
      residualPieceData.source_mem_originalPiece i⟩
  have pair_separation :
      ∀ q : PairIndex,
        ∃ δ : ℝ, 0 < δ ∧
          ∀ a, a ∈ residualPieceData.originalPiece q.1.1 →
            ∀ b, b ∈ residualPieceData.originalPiece q.1.2 →
              δ ≤ dist a b := by
    intro q
    exact PositiveSeparation
      (originalPiece_nonempty q.1.1)
      (originalPiece_nonempty q.1.2)
      (residualPieceData.originalPiece_compact q.1.1)
      (residualPieceData.originalPiece_compact q.1.2)
      (residualPieceData.originalPieces_pairwise_disjoint q.2)
  let pairSep : PairIndex → ℝ := fun q =>
    Classical.choose (pair_separation q)
  have pairSep_pos : ∀ q : PairIndex, 0 < pairSep q := by
    intro q
    exact (Classical.choose_spec (pair_separation q)).1
  have pairSep_le_dist :
      ∀ q : PairIndex,
        ∀ a, a ∈ residualPieceData.originalPiece q.1.1 →
          ∀ b, b ∈ residualPieceData.originalPiece q.1.2 →
            pairSep q ≤ dist a b := by
    intro q
    exact (Classical.choose_spec (pair_separation q)).2
  by_cases hpair : Nonempty PairIndex
  · let : Nonempty PairIndex := hpair
    let minSep : ℝ :=
      (Finset.univ : Finset PairIndex).inf' Finset.univ_nonempty pairSep
    let radius : ℝ := minSep / 3
    have minSep_pos : 0 < minSep := by
      dsimp [minSep]
      rw [Finset.lt_inf'_iff]
      intro q _hq
      exact pairSep_pos q
    have radius_pos : 0 < radius := by
      dsimp [radius]
      linarith
    refine ⟨fun i => Metric.thickening radius
      (residualPieceData.originalPiece i), ?_, ?_, ?_⟩
    · intro i
      exact Metric.isOpen_thickening
    · intro i p hp
      rw [Metric.mem_thickening_iff]
      exact ⟨p, hp, by simpa using radius_pos⟩
    · intro i j hij
      rw [Set.disjoint_left]
      intro p hpi hpj
      rw [Metric.mem_thickening_iff] at hpi hpj
      rcases hpi with ⟨a, ha, hpa⟩
      rcases hpj with ⟨b, hb, hpb⟩
      let q : PairIndex := ⟨(i, j), hij⟩
      have minSep_le_pairSep : minSep ≤ pairSep q := by
        dsimp [minSep]
        exact Finset.inf'_le pairSep (by simp)
      have upper : dist a b < pairSep q := by
        calc
          dist a b ≤ dist a p + dist p b := dist_triangle a p b
          _ = dist p a + dist p b := by rw [dist_comm a p]
          _ < radius + radius := add_lt_add hpa hpb
          _ = 2 * radius := by ring
          _ < minSep := by
            dsimp [radius]
            linarith
          _ ≤ pairSep q := minSep_le_pairSep
      exact (not_lt_of_ge (pairSep_le_dist q a ha b hb)) upper
  · refine ⟨fun _ => Set.univ, ?_, ?_, ?_⟩
    · intro i
      exact isOpen_univ
    · intro i p hp
      trivial
    · intro i j hij
      exact False.elim (hpair ⟨⟨(i, j), hij⟩⟩)
