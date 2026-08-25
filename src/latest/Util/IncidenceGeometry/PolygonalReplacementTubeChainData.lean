import Util.IncidenceGeometry.PolygonalReplacementControlDiskData
import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

structure PolygonalReplacementTubeChainData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D) where
  pieceIndex : Type
  pieceIndex_fintype : Fintype pieceIndex
  owner : pieceIndex → G.edgeFinset
  originalPiece : pieceIndex → Set (EuclideanSpace ℝ (Fin 2))
  source : pieceIndex → EuclideanSpace ℝ (Fin 2)
  target : pieceIndex → EuclideanSpace ℝ (Fin 2)
  tube : pieceIndex → Set (EuclideanSpace ℝ (Fin 2))
  chain : pieceIndex → PolygonalArc
  edgeSourceVertex : G.edgeFinset → V
  edgeTargetVertex : G.edgeFinset → V
  edgeSourceVertex_mem : ∀ e, edgeSourceVertex e ∈ e.1
  edgeTargetVertex_mem : ∀ e, edgeTargetVertex e ∈ e.1
  edgeSource_eq_vertexPlacement :
    ∀ e, D.edgeSource e = D.vertexPlacement (edgeSourceVertex e)
  edgeTarget_eq_vertexPlacement :
    ∀ e, D.edgeTarget e = D.vertexPlacement (edgeTargetVertex e)
  edgePieceOrder : G.edgeFinset → List pieceIndex
  edgePieceOrder_nonempty : ∀ e, (edgePieceOrder e).length ≠ 0
  edgePieceOrder_nodup : ∀ e, (edgePieceOrder e).Nodup
  edgePieceOrder_owner_iff :
    ∀ e i, i ∈ edgePieceOrder e ↔ owner i = e
  edgePieceOrder_first_source_boundary :
    ∀ e i,
      (edgePieceOrder e).head? = some i →
        source i ∈
            Metric.sphere (D.vertexPlacement (edgeSourceVertex e))
              (controlDisks.vertexRadius (edgeSourceVertex e)) ∧
          source i ∈ D.edgeCarrier e
  edgePieceOrder_last_target_boundary :
    ∀ e i,
      (edgePieceOrder e).getLast? = some i →
        target i ∈
            Metric.sphere (D.vertexPlacement (edgeTargetVertex e))
              (controlDisks.vertexRadius (edgeTargetVertex e)) ∧
          target i ∈ D.edgeCarrier e
  edgePieceOrder_consecutive_intersection :
    ∀ e n (hn : n + 1 < (edgePieceOrder e).length),
      ∃ x : {p // p ∈ D.intersectionPoints},
        x.1 ∈ D.edgeRelativeInterior e ∧
          target ((edgePieceOrder e)[n]) ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
            target ((edgePieceOrder e)[n]) ∈ D.edgeCarrier e ∧
              source ((edgePieceOrder e)[n + 1]) ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                source ((edgePieceOrder e)[n + 1]) ∈ D.edgeCarrier e ∧
                  target ((edgePieceOrder e)[n]) ≠
                    source ((edgePieceOrder e)[n + 1])
  edgePieceOrder_intersection_between :
    ∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset),
      x.1 ∈ D.edgeRelativeInterior e →
        ∃ n, ∃ hn : n + 1 < (edgePieceOrder e).length,
          target ((edgePieceOrder e)[n]) ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
            target ((edgePieceOrder e)[n]) ∈ D.edgeCarrier e ∧
              source ((edgePieceOrder e)[n + 1]) ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                source ((edgePieceOrder e)[n + 1]) ∈ D.edgeCarrier e ∧
                  target ((edgePieceOrder e)[n]) ≠
                    source ((edgePieceOrder e)[n + 1])
  originalPiece_compact : ∀ i, IsCompact (originalPiece i)
  originalPiece_subset_owner : ∀ i, originalPiece i ⊆ D.edgeCarrier (owner i)
  source_mem_originalPiece : ∀ i, source i ∈ originalPiece i
  target_mem_originalPiece : ∀ i, target i ∈ originalPiece i
  source_ne_target : ∀ i, source i ≠ target i
  source_on_control_boundary :
    ∀ i,
      (∃ v : V,
        v ∈ (owner i).1 ∧
          source i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
            source i ∈ D.edgeCarrier (owner i)) ∨
        (∃ x : {p // p ∈ D.intersectionPoints},
          x.1 ∈ D.edgeRelativeInterior (owner i) ∧
            source i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              source i ∈ D.edgeCarrier (owner i))
  target_on_control_boundary :
    ∀ i,
      (∃ v : V,
        v ∈ (owner i).1 ∧
          target i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
            target i ∈ D.edgeCarrier (owner i)) ∨
        (∃ x : {p // p ∈ D.intersectionPoints},
          x.1 ∈ D.edgeRelativeInterior (owner i) ∧
            target i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              target i ∈ D.edgeCarrier (owner i))
  remaining_arc_covered :
    ∀ ⦃e p⦄,
      p ∈ D.edgeCarrier e →
        (∀ v : V,
          p ∉ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)) →
          (∀ x : {q // q ∈ D.intersectionPoints},
            p ∉ Metric.ball x.1 (controlDisks.intersectionRadius x)) →
            ∃ i : pieceIndex, owner i = e ∧ p ∈ originalPiece i
  vertex_boundary_attached :
    ∀ ⦃v e p⦄,
      v ∈ e.1 →
        p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          p ∈ D.edgeCarrier e →
            ∃! i : pieceIndex, owner i = e ∧ (source i = p ∨ target i = p)
  intersection_boundary_attached :
    ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e p⦄,
      x.1 ∈ D.edgeRelativeInterior e →
        p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          p ∈ D.edgeCarrier e →
            ∃! i : pieceIndex, owner i = e ∧ (source i = p ∨ target i = p)
  originalPiece_avoids_vertex_disk_interiors :
    ∀ i v,
      Disjoint (originalPiece i)
        (Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v))
  originalPiece_avoids_intersection_disk_interiors :
    ∀ i (x : {p // p ∈ D.intersectionPoints}),
      Disjoint (originalPiece i)
        (Metric.ball x.1 (controlDisks.intersectionRadius x))
  originalPieces_pairwise_disjoint :
    ∀ ⦃i j⦄, i ≠ j → Disjoint (originalPiece i) (originalPiece j)
  tube_open : ∀ i, IsOpen (tube i)
  originalPiece_subset_tube : ∀ i, originalPiece i ⊆ tube i
  chain_endpoints : ∀ i, (chain i).source = source i ∧ (chain i).target = target i
  chain_carrier_subset_tube : ∀ i, (chain i).carrier ⊆ tube i
  chain_relativeInterior_avoids_vertex_disk_interiors :
    ∀ i v,
      Disjoint (chain i).relativeInterior
        (Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v))
  chain_relativeInterior_avoids_intersection_disk_interiors :
    ∀ i (x : {p // p ∈ D.intersectionPoints}),
      Disjoint (chain i).relativeInterior
        (Metric.ball x.1 (controlDisks.intersectionRadius x))
  chain_carrier_meets_vertex_closedBall_only_endpoint :
    ∀ i v p,
      p ∈ (chain i).carrier →
        p ∈ Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v) →
          (p = source i ∧
              source i ∈
                Metric.sphere (D.vertexPlacement v)
                  (controlDisks.vertexRadius v)) ∨
            (p = target i ∧
              target i ∈
                Metric.sphere (D.vertexPlacement v)
                  (controlDisks.vertexRadius v))
  chain_carrier_meets_intersection_closedBall_only_endpoint :
    ∀ i (x : {p // p ∈ D.intersectionPoints}) p,
      p ∈ (chain i).carrier →
        p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) →
          (p = source i ∧
              source i ∈ Metric.sphere x.1
                (controlDisks.intersectionRadius x)) ∨
            (p = target i ∧
              target i ∈ Metric.sphere x.1
                (controlDisks.intersectionRadius x))
  tubes_pairwise_disjoint :
    ∀ ⦃i j⦄, i ≠ j → Disjoint (tube i) (tube j)
  chain_carriers_pairwise_disjoint :
    ∀ ⦃i j⦄, i ≠ j → Disjoint (chain i).carrier (chain j).carrier
