import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualPieceSkeletonParameterBounds
import ErdosProblems.Erdos733.ST.PolygonalReplacementEdgeBoundaryEndpointData
import ErdosProblems.Erdos733.ST.PolygonalReplacementEndpointDeletedIntervals

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementRetainedIntervalVertexDiskAvoidance]
lemma PolygonalReplacementRetainedIntervalVertexDiskAvoidance {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (edgeParam :
      (e : G.edgeFinset) → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (edgeParam_spec :
      ∀ e,
        Continuous (edgeParam e) ∧ Function.Injective (edgeParam e) ∧
          edgeParam e ⟨0, by simp⟩ = D.edgeSource e ∧
            edgeParam e ⟨1, by simp⟩ = D.edgeTarget e ∧
              D.edgeCarrier e = Set.range (edgeParam e) ∧
                D.edgeRelativeInterior e =
                  Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                    edgeParam e
                      ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩))
    (sourceBoundaryParam targetBoundaryParam :
      G.edgeFinset → Set.Icc (0 : ℝ) 1)
    {intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1}
    {intersectionLeftParam intersectionRightParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1}
    (S : PolygonalReplacementResidualPieceSkeletonData G D
      sourceBoundaryParam targetBoundaryParam intersectionCenterParam
      intersectionLeftParam intersectionRightParam)
    (middle_avoids_source_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)))
    (middle_avoids_target_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e))) :
    ∀ i (u : Set.Icc (0 : ℝ) 1), S.sourceParam i ≤ u → u ≤ S.targetParam i →
      ∀ v : V,
        edgeParam (S.owner i) u ∉
          Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v) := by
-- BODY
  classical
  have bounds :=
    PolygonalReplacementResidualPieceSkeletonParameterBounds G
      sourceBoundaryParam targetBoundaryParam S
  have incident_endpoint :
      ∀ (e : G.edgeFinset) (v : V), v ∈ e.1 →
        v = edgeEndpoints.edgeSourceVertex e ∨
          v = edgeEndpoints.edgeTargetVertex e := by
    intro e v hv
    rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hends⟩
    have hv_ab : v ∈ (Sym2.mk a b : Sym2 V) := by
      simpa [heq] using hv
    have hv_cases : v = a ∨ v = b := by
      simpa [Sym2.mem_iff'] using hv_ab
    rcases hends with hends | hends
    · rcases hends with ⟨hsource, htarget⟩
      have hsource_vertex_eq : edgeEndpoints.edgeSourceVertex e = a := by
        apply D.vertexPlacement_injective
        calc
          D.vertexPlacement (edgeEndpoints.edgeSourceVertex e) = D.edgeSource e :=
            (edgeEndpoints.edgeSource_eq_vertexPlacement e).symm
          _ = D.vertexPlacement a := hsource
      have htarget_vertex_eq : edgeEndpoints.edgeTargetVertex e = b := by
        apply D.vertexPlacement_injective
        calc
          D.vertexPlacement (edgeEndpoints.edgeTargetVertex e) = D.edgeTarget e :=
            (edgeEndpoints.edgeTarget_eq_vertexPlacement e).symm
          _ = D.vertexPlacement b := htarget
      rcases hv_cases with rfl | rfl
      · exact Or.inl hsource_vertex_eq.symm
      · exact Or.inr htarget_vertex_eq.symm
    · rcases hends with ⟨hsource, htarget⟩
      have hsource_vertex_eq : edgeEndpoints.edgeSourceVertex e = b := by
        apply D.vertexPlacement_injective
        calc
          D.vertexPlacement (edgeEndpoints.edgeSourceVertex e) = D.edgeSource e :=
            (edgeEndpoints.edgeSource_eq_vertexPlacement e).symm
          _ = D.vertexPlacement b := hsource
      have htarget_vertex_eq : edgeEndpoints.edgeTargetVertex e = a := by
        apply D.vertexPlacement_injective
        calc
          D.vertexPlacement (edgeEndpoints.edgeTargetVertex e) = D.edgeTarget e :=
            (edgeEndpoints.edgeTarget_eq_vertexPlacement e).symm
          _ = D.vertexPlacement a := htarget
      rcases hv_cases with rfl | rfl
      · exact Or.inr htarget_vertex_eq.symm
      · exact Or.inl hsource_vertex_eq.symm
  intro i u hsource_le_u hu_le_target v hball
  let e : G.edgeFinset := S.owner i
  have hs_middle : sourceBoundaryParam e ≤ u := by
    exact le_trans (bounds.1 i) hsource_le_u
  have ht_middle : u ≤ targetBoundaryParam e := by
    exact le_trans hu_le_target (bounds.2 i)
  have hp_closed :
      edgeParam e u ∈
        Metric.closedBall (D.vertexPlacement v) (controlDisks.vertexRadius v) :=
    Metric.ball_subset_closedBall hball
  have hp_carrier : edgeParam e u ∈ D.edgeCarrier e := by
    rcases edgeParam_spec e with
      ⟨_hcont, _hinj, _hsource, _htarget, hcarrier, _hrel⟩
    rw [hcarrier]
    exact ⟨u, rfl⟩
  have hv_incident : v ∈ e.1 :=
    controlDisks.vertex_disk_meets_only_incident_edges hp_closed hp_carrier
  rcases incident_endpoint e v hv_incident with hv_source | hv_target
  · subst hv_source
    exact middle_avoids_source_vertexDisk e u hs_middle ht_middle hball
  · subst hv_target
    exact middle_avoids_target_vertexDisk e u hs_middle ht_middle hball
