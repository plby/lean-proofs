import Util.IncidenceGeometry.PolygonalReplacementCircularMiddleSubarcSafeInTube
import Mathlib.Analysis.Normed.Module.Convex

open Classical
noncomputable section

universe u

lemma PolygonalReplacementCircularMiddleSubarcFiniteSafeConvexCover {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (residualPieceData :
      PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints)
    (tube : residualPieceData.pieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
    (tube_open : ∀ i, IsOpen (tube i))
    (originalPiece_subset_tube :
      ∀ i, residualPieceData.originalPiece i ⊆ tube i)
    (i : residualPieceData.pieceIndex)
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (hcircular :
      0 < r ∧
        Continuous γ ∧ Function.Injective γ ∧
        (∀ t, dist (γ t) c = r) ∧
        γ ⟨0, by simp⟩ = D.edgeSource (residualPieceData.owner i) ∧
        γ ⟨1, by simp⟩ = D.edgeTarget (residualPieceData.owner i) ∧
        D.edgeCarrier (residualPieceData.owner i) = Set.range γ ∧
        D.edgeRelativeInterior (residualPieceData.owner i) =
          Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
            γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩))
    (us ut : Set.Icc (0 : ℝ) 1)
    (hsource_us : residualPieceData.sourceParam i < us)
    (hus_ut : us < ut)
    (hut_target : ut < residualPieceData.targetParam i) :
    let middleImage : Set (EuclideanSpace ℝ (Fin 2)) :=
      residualPieceData.edgeParam (residualPieceData.owner i) '' Set.Icc us ut
    ∃ centers : Finset middleImage,
      ∃ radius : middleImage → ℝ,
        middleImage ⊆ ⋃ z ∈ centers, Metric.ball z.1 (radius z) ∧
          (∀ z : middleImage, z ∈ centers → 0 < radius z) ∧
          (∀ z : middleImage, z ∈ centers →
            Convex ℝ (Metric.ball z.1 (radius z))) ∧
          (∀ z : middleImage, z ∈ centers →
            Metric.ball z.1 (radius z) ⊆ tube i) ∧
          (∀ z : middleImage, z ∈ centers → ∀ v : V,
            Disjoint (Metric.ball z.1 (radius z))
              (Metric.closedBall (D.vertexPlacement v)
                (controlDisks.vertexRadius v))) ∧
          (∀ z : middleImage, z ∈ centers →
            ∀ x : {p // p ∈ D.intersectionPoints},
              Disjoint (Metric.ball z.1 (radius z))
                (Metric.closedBall x.1
                  (controlDisks.intersectionRadius x))) := by
  classical
  let middleImage : Set (EuclideanSpace ℝ (Fin 2)) :=
    residualPieceData.edgeParam (residualPieceData.owner i) '' Set.Icc us ut
  rcases PolygonalReplacementCircularMiddleSubarcSafeInTube G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData tube tube_open
      originalPiece_subset_tube i hcircular us ut hsource_us hus_ut
      hut_target with
    ⟨middle_compact, middle_subset_tube, _source_mem, _target_mem,
      vertex_disjoint, intersection_disjoint⟩
  let safeSet : Set (EuclideanSpace ℝ (Fin 2)) :=
    tube i ∩
      (⋂ v : V,
        (Metric.closedBall (D.vertexPlacement v)
          (controlDisks.vertexRadius v))ᶜ) ∩
      (⋂ x : {p // p ∈ D.intersectionPoints},
        (Metric.closedBall x.1 (controlDisks.intersectionRadius x))ᶜ)
  have safe_open : IsOpen safeSet := by
    dsimp [safeSet]
    exact ((tube_open i).inter
      (isOpen_iInter_of_finite fun _ =>
        Metric.isClosed_closedBall.isOpen_compl)).inter
      (isOpen_iInter_of_finite fun _ =>
        Metric.isClosed_closedBall.isOpen_compl)
  have middle_subset_safe : middleImage ⊆ safeSet := by
    intro p hp
    dsimp [safeSet]
    refine ⟨⟨middle_subset_tube hp, ?_⟩, ?_⟩
    · exact Set.mem_iInter.mpr fun v =>
        fun hpClosed => (Set.disjoint_left.mp (vertex_disjoint v)) hp hpClosed
    · exact Set.mem_iInter.mpr fun x =>
        fun hpClosed =>
          (Set.disjoint_left.mp (intersection_disjoint x)) hp hpClosed
  have ball_exists :
      ∀ z : middleImage,
        ∃ ε : ℝ, 0 < ε ∧ Metric.ball z.1 ε ⊆ safeSet := by
    intro z
    exact Metric.isOpen_iff.mp safe_open z.1 (middle_subset_safe z.2)
  let radius : middleImage → ℝ := fun z => Classical.choose (ball_exists z)
  have radius_pos : ∀ z : middleImage, 0 < radius z := by
    intro z
    exact (Classical.choose_spec (ball_exists z)).1
  have radius_subset_safe :
      ∀ z : middleImage, Metric.ball z.1 (radius z) ⊆ safeSet := by
    intro z
    exact (Classical.choose_spec (ball_exists z)).2
  have cover_all :
      middleImage ⊆ ⋃ z : middleImage, Metric.ball z.1 (radius z) := by
    intro p hp
    exact Set.mem_iUnion.mpr
      ⟨⟨p, hp⟩, Metric.mem_ball_self (radius_pos ⟨p, hp⟩)⟩
  rcases middle_compact.elim_finite_subcover
      (fun z : middleImage => Metric.ball z.1 (radius z))
      (fun _ => Metric.isOpen_ball) cover_all with
    ⟨centers, finite_cover⟩
  refine ⟨centers, radius, finite_cover, ?_, ?_, ?_, ?_, ?_⟩
  · intro z _hz
    exact radius_pos z
  · intro z _hz
    exact convex_ball z.1 (radius z)
  · intro z _hz p hp
    exact (radius_subset_safe z hp).1.1
  · intro z _hz v
    rw [Set.disjoint_left]
    intro p hp hpClosed
    exact (Set.mem_iInter.mp (radius_subset_safe z hp).1.2 v) hpClosed
  · intro z _hz x
    rw [Set.disjoint_left]
    intro p hp hpClosed
    exact (Set.mem_iInter.mp (radius_subset_safe z hp).2 x) hpClosed
