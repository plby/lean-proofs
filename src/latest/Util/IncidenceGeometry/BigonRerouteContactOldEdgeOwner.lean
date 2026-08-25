import Util.IncidenceGeometry.BigonRerouteLocalSegmentDirection
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

lemma BigonRerouteContactOldEdgeOwner
    {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (alpha beta : G.edgeFinset) (u : V)
    (x y z : EuclideanSpace ℝ (Fin 2))
    (A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (K : FinitePolygonalSet)
    (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
    (radius : ℝ)
    (hDuA : D.vertexPlacement u ∈ A)
    (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    (hBplusClosed : IsClosed Bplus)
    (hRbeta :
      Rbeta = (D.edgeArc beta).carrier \ ((B ∪ Bplus) \ ({y} : Set _)))
    (hH :
      H =
        (⋃ edge : G.edgeFinset,
          if edge = alpha then
            (D.edgeArc edge).carrier \ (A \ ({D.vertexPlacement u, x} : Set _))
          else if edge = beta then
            (D.edgeArc edge).carrier \
              ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
                (Bplus \ ({x, y} : Set _)))
          else (D.edgeArc edge).carrier) ∪
        {p | ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v})
    (hK : K.carrier = H)
    (hvertices :
      ∀ v : V, v ≠ u → D.vertexPlacement v ∈ (K.points : Set _))
    (hznotpoints : z ∉ (K.points : Set _))
    (hzavoid : z ∉ A ∪ B ∪ Bplus)
    (hs : s ∈ K.segments)
    (hzs : z ∈ openSegment ℝ s.1 s.2)
    (hradius : 0 < radius)
    (hlocal :
      Metric.ball z radius ∩ H =
        Metric.ball z radius ∩ segment ℝ s.1 s.2) :
    ∃ edge : G.edgeFinset,
      z ∈ (D.edgeArc edge).relativeInterior ∧
        (∀ f : G.edgeFinset,
          z ∈ (D.edgeArc f).relativeInterior → f = edge) ∧
          (edge = alpha →
            z ∈ (D.edgeArc edge).carrier \
              (A \ ({D.vertexPlacement u, x} : Set _))) ∧
          (edge = beta → z ∈ Rbeta) ∧
          ∃ i : ℕ, ∃ hi : i + 1 < (D.edgeArc edge).vertices.length,
            z ∈ segment ℝ (D.edgeArc edge).vertices[i]
                (D.edgeArc edge).vertices[i + 1] ∧
              ∃ c : ℝ, c ≠ 0 ∧
                (D.edgeArc edge).vertices[i + 1] -
                    (D.edgeArc edge).vertices[i] =
                  c • (s.2 - s.1) := by
  have hz_not_u : z ≠ D.vertexPlacement u := by
    intro hzu
    apply hzavoid
    exact Or.inl (Or.inl (by simpa [hzu] using hDuA))
  have hz_not_vertex : ∀ v : V, z ≠ D.vertexPlacement v := by
    intro v hzv
    by_cases hv : v = u
    · subst v
      exact hz_not_u hzv
    · apply hznotpoints
      rw [hzv]
      exact hvertices v hv
  have hclosed : IsClosed (A ∪ B ∪ Bplus) :=
    (hAclosed.union hBclosed).union hBplusClosed
  have hopen : IsOpen (A ∪ B ∪ Bplus)ᶜ := hclosed.isOpen_compl
  have hzcomp : z ∈ (A ∪ B ∪ Bplus)ᶜ := hzavoid
  rcases Metric.isOpen_iff.mp hopen z hzcomp with
    ⟨avoidRadius, hAvoidPos, hAvoidBall⟩
  let localRadius : ℝ := min radius avoidRadius
  have hLocalPos : 0 < localRadius := lt_min hradius hAvoidPos
  have hsegment_direction :
      ∀ (edge : G.edgeFinset) (i : ℕ)
        (hi : i + 1 < (D.edgeArc edge).vertices.length),
        z ∈ segment ℝ (D.edgeArc edge).vertices[i]
            (D.edgeArc edge).vertices[i + 1] →
          ∃ c : ℝ, c ≠ 0 ∧
            (D.edgeArc edge).vertices[i + 1] -
                (D.edgeArc edge).vertices[i] =
              c • (s.2 - s.1) := by
    intro edge i hi hzseg
    have hedge_ne :
        (D.edgeArc edge).vertices[i] ≠
          (D.edgeArc edge).vertices[i + 1] := by
      intro heq
      have hidx := ((D.edgeArc edge).simple_vertices.getElem_inj_iff
        (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 heq
      omega
    apply BigonRerouteLocalSegmentDirection _ _ _ _ z hedge_ne
      hzseg (openSegment_subset_segment ℝ s.1 s.2 hzs)
      localRadius hLocalPos
    intro w hw
    have hwBallRadius : w ∈ Metric.ball z radius :=
      Metric.ball_subset_ball (min_le_left radius avoidRadius) hw.1
    have hwBallAvoid : w ∈ Metric.ball z avoidRadius :=
      Metric.ball_subset_ball (min_le_right radius avoidRadius) hw.1
    have hwAvoid : w ∉ A ∪ B ∪ Bplus := hAvoidBall hwBallAvoid
    have hwCarrier : w ∈ (D.edgeArc edge).carrier := by
      rw [(D.edgeArc edge).carrier_eq]
      exact ⟨i, hi, hw.2⟩
    have hwH : w ∈ H := by
      rw [hH]
      left
      apply Set.mem_iUnion.mpr
      refine ⟨edge, ?_⟩
      by_cases hedgeAlpha : edge = alpha
      · subst edge
        rw [if_pos rfl]
        exact ⟨hwCarrier, fun h => hwAvoid (Or.inl (Or.inl h.1))⟩
      · rw [if_neg hedgeAlpha]
        by_cases hedgeBeta : edge = beta
        · subst edge
          rw [if_pos rfl]
          refine ⟨hwCarrier, ?_⟩
          rintro (hB | hBp)
          · exact hwAvoid (Or.inl (Or.inr hB.1))
          · exact hwAvoid (Or.inr hBp.1)
        · simpa [if_neg hedgeBeta] using hwCarrier
    have hwLocal : w ∈ Metric.ball z radius ∩ H := ⟨hwBallRadius, hwH⟩
    rw [hlocal] at hwLocal
    exact hwLocal.2
  have hzK : z ∈ K.carrier := by
    rw [K.carrier_eq]
    right
    apply Set.mem_iUnion.mpr
    exact ⟨⟨s, hs⟩, openSegment_subset_segment ℝ s.1 s.2 hzs⟩
  have hzH : z ∈ H := by simpa [hK] using hzK
  rw [hH] at hzH
  rcases hzH with hzEdges | hzVertex
  · rcases Set.mem_iUnion.mp hzEdges with ⟨edge, hedgeRetained⟩
    have hedgeCarrier : z ∈ (D.edgeArc edge).carrier := by
      by_cases hedgeAlpha : edge = alpha
      · subst edge
        rw [if_pos rfl] at hedgeRetained
        exact hedgeRetained.1
      · rw [if_neg hedgeAlpha] at hedgeRetained
        by_cases hedgeBeta : edge = beta
        · subst edge
          rw [if_pos rfl] at hedgeRetained
          exact hedgeRetained.1
        · rw [if_neg hedgeBeta] at hedgeRetained
          exact hedgeRetained
    have hzRel : z ∈ (D.edgeArc edge).relativeInterior := by
      rw [(D.edgeArc edge).relativeInterior_eq]
      refine ⟨hedgeCarrier, ?_⟩
      rcases D.edgeArc_endpoints edge with
        ⟨v, w, _hvw, _hedge, hends⟩
      rcases hends with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rintro (hzsource | hztarget)
        · exact hz_not_vertex v (hzsource.trans hsource)
        · exact hz_not_vertex w (hztarget.trans htarget)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rintro (hzsource | hztarget)
        · exact hz_not_vertex w (hzsource.trans hsource)
        · exact hz_not_vertex v (hztarget.trans htarget)
    have hunique :
        ∀ f : G.edgeFinset,
          z ∈ (D.edgeArc f).relativeInterior → f = edge := by
      intro f hzf
      by_contra hfe
      have hef : edge ≠ f := Ne.symm hfe
      rcases D.transverse_intersections hef hzRel hzf with
        ⟨i, j, hi, hj, hz_i, hz_j, hnonparallel⟩
      rcases hsegment_direction edge i hi hz_i with
        ⟨ci, hci, hdir_i⟩
      rcases hsegment_direction f j hj hz_j with
        ⟨cj, _hcj, hdir_j⟩
      apply hnonparallel
      refine ⟨cj * ci⁻¹, ?_⟩
      rw [hdir_j, hdir_i, smul_smul]
      simp [hci]
    have hAlpha : edge = alpha →
        z ∈ (D.edgeArc edge).carrier \
          (A \ ({D.vertexPlacement u, x} : Set _)) := by
      intro hedgeAlpha
      subst edge
      simpa using hedgeRetained
    have hBeta : edge = beta → z ∈ Rbeta := by
      intro hedgeBeta
      subst edge
      rw [hRbeta]
      refine ⟨hedgeCarrier, ?_⟩
      intro hzRemoved
      rcases hzRemoved.1 with hzB | hzBplus
      · exact hzavoid (Or.inl (Or.inr hzB))
      · exact hzavoid (Or.inr hzBplus)
    rw [(D.edgeArc edge).carrier_eq] at hedgeCarrier
    rcases hedgeCarrier with ⟨i, hi, hzseg⟩
    rcases hsegment_direction edge i hi hzseg with ⟨c, hc, hdir⟩
    exact ⟨edge, hzRel, hunique, hAlpha, hBeta, i, hi, hzseg, c, hc, hdir⟩
  · rcases hzVertex with ⟨v, _hv, hzv⟩
    exact (hz_not_vertex v hzv).elim
