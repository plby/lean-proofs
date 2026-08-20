import ErdosProblems.Erdos733.ST.PolygonalReplacementControlDiskData

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementBoundaryPointData]
structure PolygonalReplacementBoundaryPointData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D) where
-- BODY
  boundaryIndex : Type*
  boundaryIndex_fintype : Fintype boundaryIndex
  owner : boundaryIndex → G.edgeFinset
  point : boundaryIndex → EuclideanSpace ℝ (Fin 2)
  point_on_control_boundary :
    ∀ i,
      (∃ v : V,
        v ∈ (owner i).1 ∧
          point i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
            point i ∈ D.edgeCarrier (owner i)) ∨
        (∃ x : {p // p ∈ D.intersectionPoints},
          x.1 ∈ D.edgeRelativeInterior (owner i) ∧
            point i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              point i ∈ D.edgeCarrier (owner i))
  vertexBoundaryIndex :
    ∀ {v : V} {e : G.edgeFinset}, v ∈ e.1 → boundaryIndex
  vertexBoundaryIndex_owner :
    ∀ {v : V} {e : G.edgeFinset} (hv : v ∈ e.1),
      owner (vertexBoundaryIndex hv) = e
  vertexBoundaryIndex_boundary :
    ∀ {v : V} {e : G.edgeFinset} (hv : v ∈ e.1),
      point (vertexBoundaryIndex hv) ∈
          Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
        point (vertexBoundaryIndex hv) ∈ D.edgeCarrier e
  vertex_boundary_point_eq :
    ∀ {v : V} {e : G.edgeFinset} {p : EuclideanSpace ℝ (Fin 2)}
      (hv : v ∈ e.1),
      p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
        p ∈ D.edgeCarrier e → p = point (vertexBoundaryIndex hv)
  intersectionBoundaryIndexLeft :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
      x.1 ∈ D.edgeRelativeInterior e → boundaryIndex
  intersectionBoundaryIndexRight :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
      x.1 ∈ D.edgeRelativeInterior e → boundaryIndex
  intersectionBoundaryIndexLeft_owner :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
      (hx : x.1 ∈ D.edgeRelativeInterior e),
      owner (intersectionBoundaryIndexLeft hx) = e
  intersectionBoundaryIndexRight_owner :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
      (hx : x.1 ∈ D.edgeRelativeInterior e),
      owner (intersectionBoundaryIndexRight hx) = e
  intersectionBoundaryIndexLeft_boundary :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
      (hx : x.1 ∈ D.edgeRelativeInterior e),
      point (intersectionBoundaryIndexLeft hx) ∈
          Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
        point (intersectionBoundaryIndexLeft hx) ∈ D.edgeCarrier e
  intersectionBoundaryIndexRight_boundary :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
      (hx : x.1 ∈ D.edgeRelativeInterior e),
      point (intersectionBoundaryIndexRight hx) ∈
          Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
        point (intersectionBoundaryIndexRight hx) ∈ D.edgeCarrier e
  intersectionBoundaryIndex_ne :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
      (hx : x.1 ∈ D.edgeRelativeInterior e),
      point (intersectionBoundaryIndexLeft hx) ≠ point (intersectionBoundaryIndexRight hx)
  intersection_boundary_point_eq_left_or_right :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
      {p : EuclideanSpace ℝ (Fin 2)}
      (hx : x.1 ∈ D.edgeRelativeInterior e),
      p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
        p ∈ D.edgeCarrier e →
          p = point (intersectionBoundaryIndexLeft hx) ∨
            p = point (intersectionBoundaryIndexRight hx)
