import Util.IncidenceGeometry.PolygonalReplacementTubeChainData

open Classical
noncomputable section

structure PolygonalReplacementLocalDiskFillingData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks) where
  vertex_spoke :
    (v : V) → {e : G.edgeFinset // v ∈ e.1} → PolygonalArc
  vertex_spoke_source :
    ∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
      (vertex_spoke v e).source = D.vertexPlacement v
  vertex_spoke_source_ne_target :
    ∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
      (vertex_spoke v e).source ≠ (vertex_spoke v e).target
  vertex_spoke_target_boundary :
    ∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
      (vertex_spoke v e).target ∈
          Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
        (vertex_spoke v e).target ∈ D.edgeCarrier e.1
  vertex_spoke_attached_to_tube :
    ∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
      ∃! i : tubeChains.pieceIndex,
        tubeChains.owner i = e.1 ∧
          (tubeChains.source i = (vertex_spoke v e).target ∨
            tubeChains.target i = (vertex_spoke v e).target)
  vertex_boundary_covered :
    ∀ ⦃v : V⦄ ⦃e : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄
      (hve : v ∈ e.1),
      p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
        p ∈ D.edgeCarrier e →
          (vertex_spoke v ⟨e, hve⟩).target = p
  vertex_spoke_carrier_subset_closedBall :
    ∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
      (vertex_spoke v e).carrier ⊆
        Metric.closedBall (D.vertexPlacement v) (controlDisks.vertexRadius v)
  vertex_spoke_relativeInterior_subset_ball :
    ∀ v (e : {e : G.edgeFinset // v ∈ e.1}),
      (vertex_spoke v e).relativeInterior ⊆
        Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)
  vertex_spokes_same_vertex_disjoint :
    ∀ v ⦃e f : {e : G.edgeFinset // v ∈ e.1}⦄,
      e ≠ f →
        Disjoint (vertex_spoke v e).relativeInterior
          (vertex_spoke v f).relativeInterior
  intersection_chain :
    (x : {p // p ∈ D.intersectionPoints}) →
      {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} → PolygonalArc
  intersection_chain_source_ne_target :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      (intersection_chain x e).source ≠ (intersection_chain x e).target
  intersection_chain_source_boundary :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      (intersection_chain x e).source ∈
          Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
        (intersection_chain x e).source ∈ D.edgeCarrier e.1
  intersection_chain_target_boundary :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      (intersection_chain x e).target ∈
          Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
        (intersection_chain x e).target ∈ D.edgeCarrier e.1
  intersection_chain_source_attached_to_tube :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      ∃! i : tubeChains.pieceIndex,
        tubeChains.owner i = e.1 ∧
          (tubeChains.source i = (intersection_chain x e).source ∨
            tubeChains.target i = (intersection_chain x e).source)
  intersection_chain_target_attached_to_tube :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      ∃! i : tubeChains.pieceIndex,
        tubeChains.owner i = e.1 ∧
          (tubeChains.source i = (intersection_chain x e).target ∨
            tubeChains.target i = (intersection_chain x e).target)
  intersection_boundary_covered :
    ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e : G.edgeFinset⦄
      ⦃p : EuclideanSpace ℝ (Fin 2)⦄
      (hxe : x.1 ∈ D.edgeRelativeInterior e),
      p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
        p ∈ D.edgeCarrier e →
          (intersection_chain x ⟨e, hxe⟩).source = p ∨
            (intersection_chain x ⟨e, hxe⟩).target = p
  intersection_chain_carrier_subset_closedBall :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      (intersection_chain x e).carrier ⊆
        Metric.closedBall x.1 (controlDisks.intersectionRadius x)
  intersection_chain_relativeInterior_subset_ball :
    ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
      (intersection_chain x e).relativeInterior ⊆
        Metric.ball x.1 (controlDisks.intersectionRadius x)
  intersection_chains_no_shared_nondegenerate_subarc :
    ∀ x ⦃e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄,
      e ≠ f →
        ¬ ∃ m n : ℕ,
          ∃ (hm : m + 1 < (intersection_chain x e).vertices.length)
            (hn : n + 1 < (intersection_chain x f).vertices.length),
            ∃ p q : EuclideanSpace ℝ (Fin 2),
              p ≠ q ∧
                segment ℝ p q ⊆
                  segment ℝ (intersection_chain x e).vertices[m]
                      (intersection_chain x e).vertices[m + 1] ∩
                    segment ℝ (intersection_chain x f).vertices[n]
                      (intersection_chain x f).vertices[n + 1]
  intersection_chains_no_triple_intersections :
    ∀ x ⦃e f g : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄
      ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e ≠ f → e ≠ g → f ≠ g →
        p ∈ (intersection_chain x e).relativeInterior →
          p ∈ (intersection_chain x f).relativeInterior →
            p ∈ (intersection_chain x g).relativeInterior → False
  intersection_chains_transverse_intersections :
    ∀ x ⦃e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄
      ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e ≠ f →
        p ∈ (intersection_chain x e).relativeInterior →
          p ∈ (intersection_chain x f).relativeInterior →
            ∃ m n : ℕ,
              ∃ (hm : m + 1 < (intersection_chain x e).vertices.length)
                (hn : n + 1 < (intersection_chain x f).vertices.length),
                p ∈ segment ℝ (intersection_chain x e).vertices[m]
                    (intersection_chain x e).vertices[m + 1] ∧
                  p ∈ segment ℝ (intersection_chain x f).vertices[n]
                      (intersection_chain x f).vertices[n + 1] ∧
                    ¬ ∃ t : ℝ,
                      (intersection_chain x f).vertices[n + 1] -
                          (intersection_chain x f).vertices[n] =
                        t • ((intersection_chain x e).vertices[m + 1] -
                          (intersection_chain x e).vertices[m])
  intersection_chains_pairwise_at_most_one :
    ∀ x ⦃e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄
      ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
      e ≠ f →
        p ∈ (intersection_chain x e).relativeInterior →
          p ∈ (intersection_chain x f).relativeInterior →
            q ∈ (intersection_chain x e).relativeInterior →
              q ∈ (intersection_chain x f).relativeInterior →
                p = q
