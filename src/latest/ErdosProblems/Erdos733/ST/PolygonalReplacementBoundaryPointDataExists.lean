import ErdosProblems.Erdos733.ST.PolygonalReplacementBoundaryPointData

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementBoundaryPointDataExists]
lemma PolygonalReplacementBoundaryPointDataExists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D) :
    Nonempty (PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks) := by
-- BODY
  classical
  let vertexIndexType :=
    {ve : V × G.edgeFinset // ve.1 ∈ ve.2.1}
  let intersectionBase :=
    {xe : {p // p ∈ D.intersectionPoints} × G.edgeFinset //
      xe.1.1 ∈ D.edgeRelativeInterior xe.2}
  let intersectionIndexType := intersectionBase × Bool
  let boundaryIndex := vertexIndexType ⊕ intersectionIndexType
  let vertexPoint : vertexIndexType → EuclideanSpace ℝ (Fin 2) := fun i =>
    Classical.choose
      (ExistsUnique.exists
        (controlDisks.vertex_boundary_unique (v := i.1.1) (e := i.1.2) i.2))
  have vertexPoint_spec :
      ∀ i : vertexIndexType,
        vertexPoint i ∈
            Metric.sphere (D.vertexPlacement i.1.1)
              (controlDisks.vertexRadius i.1.1) ∧
          vertexPoint i ∈ D.edgeCarrier i.1.2 := by
    intro i
    dsimp [vertexPoint]
    exact
      Classical.choose_spec
        (ExistsUnique.exists
          (controlDisks.vertex_boundary_unique (v := i.1.1) (e := i.1.2) i.2))
  have vertexPoint_unique :
      ∀ (i : vertexIndexType) (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ Metric.sphere (D.vertexPlacement i.1.1)
            (controlDisks.vertexRadius i.1.1) →
          p ∈ D.edgeCarrier i.1.2 → p = vertexPoint i := by
    intro i p hpSphere hpCarrier
    dsimp [vertexPoint]
    exact
      ExistsUnique.unique
        (controlDisks.vertex_boundary_unique (v := i.1.1) (e := i.1.2) i.2)
        ⟨hpSphere, hpCarrier⟩
        (Classical.choose_spec
          (ExistsUnique.exists
            (controlDisks.vertex_boundary_unique (v := i.1.1) (e := i.1.2) i.2)))
  let intersectionLeftPoint : intersectionBase → EuclideanSpace ℝ (Fin 2) := fun i =>
    Classical.choose
      (controlDisks.intersection_boundary_two_points (x := i.1.1) (e := i.1.2) i.2)
  let intersectionRightPoint : intersectionBase → EuclideanSpace ℝ (Fin 2) := fun i =>
    Classical.choose
      (Classical.choose_spec
        (controlDisks.intersection_boundary_two_points (x := i.1.1) (e := i.1.2) i.2))
  have intersectionPoint_spec :
      ∀ i : intersectionBase,
        intersectionLeftPoint i ≠ intersectionRightPoint i ∧
          intersectionLeftPoint i ∈
              Metric.sphere i.1.1.1 (controlDisks.intersectionRadius i.1.1) ∧
            intersectionLeftPoint i ∈ D.edgeCarrier i.1.2 ∧
              intersectionRightPoint i ∈
                  Metric.sphere i.1.1.1 (controlDisks.intersectionRadius i.1.1) ∧
                intersectionRightPoint i ∈ D.edgeCarrier i.1.2 ∧
                  ∀ p,
                    p ∈ Metric.sphere i.1.1.1 (controlDisks.intersectionRadius i.1.1) →
                      p ∈ D.edgeCarrier i.1.2 →
                        p = intersectionLeftPoint i ∨ p = intersectionRightPoint i := by
    intro i
    dsimp [intersectionLeftPoint, intersectionRightPoint]
    exact
      Classical.choose_spec
        (Classical.choose_spec
          (controlDisks.intersection_boundary_two_points (x := i.1.1) (e := i.1.2) i.2))
  refine ⟨{
    boundaryIndex := boundaryIndex
    boundaryIndex_fintype := by
      dsimp [boundaryIndex, vertexIndexType, intersectionIndexType, intersectionBase]
      infer_instance
    owner := fun i =>
      match i with
      | Sum.inl i => i.1.2
      | Sum.inr i => i.1.1.2
    point := fun i =>
      match i with
      | Sum.inl i => vertexPoint i
      | Sum.inr i =>
          if i.2 then intersectionRightPoint i.1 else intersectionLeftPoint i.1
    point_on_control_boundary := by
      intro i
      rcases i with i | i
      · left
        exact ⟨i.1.1, i.2, vertexPoint_spec i⟩
      · right
        refine ⟨i.1.1.1, i.1.2, ?_⟩
        by_cases hb : i.2
        · have hspec := intersectionPoint_spec i.1
          simpa [hb] using ⟨hspec.2.2.2.1, hspec.2.2.2.2.1⟩
        · have hspec := intersectionPoint_spec i.1
          simpa [hb] using ⟨hspec.2.1, hspec.2.2.1⟩
    vertexBoundaryIndex := fun {v} {e} hv => Sum.inl ⟨(v, e), hv⟩
    vertexBoundaryIndex_owner := by
      intro v e hv
      rfl
    vertexBoundaryIndex_boundary := by
      intro v e hv
      exact vertexPoint_spec ⟨(v, e), hv⟩
    vertex_boundary_point_eq := by
      intro v e p hv hpSphere hpCarrier
      exact vertexPoint_unique ⟨(v, e), hv⟩ p hpSphere hpCarrier
    intersectionBoundaryIndexLeft := fun {x} {e} hx =>
      Sum.inr (⟨(x, e), hx⟩, false)
    intersectionBoundaryIndexRight := fun {x} {e} hx =>
      Sum.inr (⟨(x, e), hx⟩, true)
    intersectionBoundaryIndexLeft_owner := by
      intro x e hx
      rfl
    intersectionBoundaryIndexRight_owner := by
      intro x e hx
      rfl
    intersectionBoundaryIndexLeft_boundary := by
      intro x e hx
      exact ⟨(intersectionPoint_spec ⟨(x, e), hx⟩).2.1,
        (intersectionPoint_spec ⟨(x, e), hx⟩).2.2.1⟩
    intersectionBoundaryIndexRight_boundary := by
      intro x e hx
      exact ⟨(intersectionPoint_spec ⟨(x, e), hx⟩).2.2.2.1,
        (intersectionPoint_spec ⟨(x, e), hx⟩).2.2.2.2.1⟩
    intersectionBoundaryIndex_ne := by
      intro x e hx
      exact (intersectionPoint_spec ⟨(x, e), hx⟩).1
    intersection_boundary_point_eq_left_or_right := by
      intro x e p hx hpSphere hpCarrier
      exact (intersectionPoint_spec ⟨(x, e), hx⟩).2.2.2.2.2 p hpSphere hpCarrier }⟩
