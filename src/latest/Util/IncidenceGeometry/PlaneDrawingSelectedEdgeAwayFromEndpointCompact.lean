import Util.IncidenceGeometry.CrossingFreeEdgeInteriorDisjoint
import Util.IncidenceGeometry.OrdinaryDrawingImageCompact
import Util.IncidenceGeometry.OrdinaryDrawingImageWithoutEdge
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PolygonalArcCarrierCompact

open Classical
noncomputable section

lemma PlaneDrawingSelectedEdgeAwayFromEndpointCompact {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (e : G.edgeFinset) (γ : PolygonalArc) :
    D.edgeArc e = γ →
      ∀ r₀ r₁ : ℝ, 0 < r₀ → 0 < r₁ →
        let A : Set (EuclideanSpace ℝ (Fin 2)) :=
          OrdinaryDrawingImageWithoutEdge G D e \
            (Metric.ball γ.source r₀ ∪ Metric.ball γ.target r₁)
        IsCompact A ∧ Disjoint A γ.carrier := by
  intro hγ r₀ r₁ hr₀ hr₁
  have hWithoutCompact : IsCompact (OrdinaryDrawingImageWithoutEdge G D e) := by
    rw [OrdinaryDrawingImageWithoutEdge]
    exact IsCompact.union
      (Set.Finite.isCompact (Set.finite_range D.vertexPlacement))
      (isCompact_iUnion (fun f : {f : G.edgeFinset // f ≠ e} =>
        PolygonalArcCarrierCompact (D.edgeArc f.1)))
  have endpoint_of_not_rel :
      ∀ (δ : PolygonalArc) ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
        y ∈ δ.carrier → y ∉ δ.relativeInterior →
          y = δ.source ∨ y = δ.target := by
    intro δ y hy hnot
    have hyEnd : y ∈ ({δ.source, δ.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
      by_contra hnotEnd
      have hyRel : y ∈ δ.relativeInterior := by
        rw [δ.relativeInterior_eq]
        exact ⟨hy, hnotEnd⟩
      exact hnot hyRel
    simpa using hyEnd
  have common_endpoint :
      ∀ ⦃x : EuclideanSpace ℝ (Fin 2)⦄,
        x ∈ γ.carrier →
        x ∈ OrdinaryDrawingImageWithoutEdge G D e →
        x = γ.source ∨ x = γ.target := by
    intro x hxγ hximg
    rw [OrdinaryDrawingImageWithoutEdge] at hximg
    rcases hximg with hxv | hxe
    · rcases hxv with ⟨v, rfl⟩
      have hnot : D.vertexPlacement v ∉ γ.relativeInterior := by
        simpa [hγ] using D.no_vertex_in_edge_interior v e
      exact endpoint_of_not_rel γ hxγ hnot
    · rcases Set.mem_iUnion.1 hxe with ⟨f, hxf⟩
      by_cases hxγrel : x ∈ γ.relativeInterior
      · by_cases hxfrel : x ∈ (D.edgeArc f.1).relativeInterior
        · have hxeRel : x ∈ (D.edgeArc e).relativeInterior := by
            simpa [hγ] using hxγrel
          exact False.elim
            (CrossingFreeEdgeInteriorDisjoint G D hD (e₁ := e) (e₂ := f.1)
              (p := x) (Ne.symm f.2) hxeRel hxfrel)
        · have hxfEnd := endpoint_of_not_rel (D.edgeArc f.1) hxf hxfrel
          have hxVertex : ∃ v : V, x = D.vertexPlacement v := by
            rcases D.edgeArc_endpoints f.1 with ⟨u, v, _hadj, _heq, hends⟩
            rcases hxfEnd with hxsrc | hxtgt
            · rcases hends with hdir | hrev
              · exact ⟨u, by rw [hxsrc, hdir.1]⟩
              · exact ⟨v, by rw [hxsrc, hrev.1]⟩
            · rcases hends with hdir | hrev
              · exact ⟨v, by rw [hxtgt, hdir.2]⟩
              · exact ⟨u, by rw [hxtgt, hrev.2]⟩
          rcases hxVertex with ⟨v, hxv⟩
          have hnot : D.vertexPlacement v ∉ γ.relativeInterior := by
            simpa [hγ] using D.no_vertex_in_edge_interior v e
          exact False.elim (hnot (by simpa [hxv] using hxγrel))
      · exact endpoint_of_not_rel γ hxγ hxγrel
  constructor
  · have hOpenBalls :
        IsOpen (Metric.ball γ.source r₀ ∪ Metric.ball γ.target r₁) :=
      Metric.isOpen_ball.union Metric.isOpen_ball
    exact hWithoutCompact.diff hOpenBalls
  · rw [Set.disjoint_left]
    intro x hxA hxγ
    rcases common_endpoint hxγ hxA.1 with hxsrc | hxtgt
    · have hxBall : x ∈ Metric.ball γ.source r₀ := by
        simpa [hxsrc] using
          (Metric.mem_ball_self (x := γ.source) (ε := r₀) hr₀)
      exact hxA.2 (Or.inl hxBall)
    · have hxBall : x ∈ Metric.ball γ.target r₁ := by
        simpa [hxtgt] using
          (Metric.mem_ball_self (x := γ.target) (ε := r₁) hr₁)
      exact hxA.2 (Or.inr hxBall)
