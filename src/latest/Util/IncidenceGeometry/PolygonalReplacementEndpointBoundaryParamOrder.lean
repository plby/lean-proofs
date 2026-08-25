import Util.IncidenceGeometry.PolygonalReplacementEdgeBoundaryEndpointData

open Classical
noncomputable section

universe u

lemma PolygonalReplacementEndpointBoundaryParamOrder {V : Type u} [Fintype V]
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
    (sourceBoundaryParam targetBoundaryParam : G.edgeFinset → Set.Icc (0 : ℝ) 1)
    (sourceBoundaryParam_eq :
      ∀ e, edgeParam e (sourceBoundaryParam e) =
        edgeEndpoints.sourceBoundaryPoint e)
    (targetBoundaryParam_eq :
      ∀ e, edgeParam e (targetBoundaryParam e) =
        edgeEndpoints.targetBoundaryPoint e) :
    ∀ e, sourceBoundaryParam e < targetBoundaryParam e := by
  classical
  intro e
  rcases edgeParam_spec e with
    ⟨hcont, hinj, hsource0, htarget1, hcarrier, _hrel⟩
  let s : Set.Icc (0 : ℝ) 1 := sourceBoundaryParam e
  let t : Set.Icc (0 : ℝ) 1 := targetBoundaryParam e
  let sv : V := edgeEndpoints.edgeSourceVertex e
  let tv : V := edgeEndpoints.edgeTargetVertex e
  have hzero :
      edgeParam e ⟨0, by simp⟩ = D.vertexPlacement sv := by
    simpa [sv] using hsource0.trans (edgeEndpoints.edgeSource_eq_vertexPlacement e)
  have hone :
      edgeParam e ⟨1, by simp⟩ = D.vertexPlacement tv := by
    simpa [tv] using htarget1.trans (edgeEndpoints.edgeTarget_eq_vertexPlacement e)
  have hzero_ne_one :
      (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) ≠ ⟨1, by simp⟩ := by
    intro h
    have := congrArg Subtype.val h
    norm_num at this
  have hvertex_points_ne :
      D.vertexPlacement sv ≠ D.vertexPlacement tv := by
    intro hsame
    apply hzero_ne_one
    apply hinj
    calc
      edgeParam e (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1)
          = D.vertexPlacement sv := hzero
      _ = D.vertexPlacement tv := hsame
      _ = edgeParam e (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) := hone.symm
  have hsv_ne_tv : sv ≠ tv := by
    intro hsame
    exact hvertex_points_ne (by simp [sv, tv, hsame])
  have hs_sphere :
      edgeParam e s ∈
        Metric.sphere (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
    simpa [s, sv, sourceBoundaryParam_eq e] using
      (edgeEndpoints.sourceBoundary_on_control_boundary e).1
  have ht_sphere :
      edgeParam e t ∈
        Metric.sphere (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
    simpa [t, tv, targetBoundaryParam_eq e] using
      (edgeEndpoints.targetBoundary_on_control_boundary e).1
  have hs_dist :
      dist (edgeParam e s) (D.vertexPlacement sv) =
        controlDisks.vertexRadius sv := by
    rw [dist_eq_norm]
    simpa only [Metric.mem_sphere, dist_eq_norm] using hs_sphere
  have source_prefix_closed :
      ∀ u : Set.Icc (0 : ℝ) 1, u ≤ s →
        edgeParam e u ∈
          Metric.closedBall (D.vertexPlacement sv)
            (controlDisks.vertexRadius sv) := by
    intro u hu
    by_contra hnot_closed
    have hdist_gt :
        controlDisks.vertexRadius sv <
          dist (edgeParam e u) (D.vertexPlacement sv) := by
      exact lt_of_not_ge (by
        intro hle
        exact hnot_closed (by simpa [Metric.mem_closedBall, dist_comm] using hle))
    have hu_ne_s : u ≠ s := by
      intro hus
      have : dist (edgeParam e u) (D.vertexPlacement sv) =
          controlDisks.vertexRadius sv := by
        simpa [hus] using hs_dist
      linarith
    have hu_lt_s : u < s := lt_of_le_of_ne hu hu_ne_s
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun z =>
      dist (edgeParam e z) (D.vertexPlacement sv)
    have hfcont : Continuous f := hcont.dist continuous_const
    have hzero_dist : f ⟨0, by simp⟩ = 0 := by
      dsimp [f]
      change
        dist (edgeParam e (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1))
            (D.vertexPlacement sv) = 0
      rw [hzero, dist_self]
    have hzero_lt_radius : f ⟨0, by simp⟩ < controlDisks.vertexRadius sv := by
      rw [hzero_dist]
      exact controlDisks.vertexRadius_pos sv
    have hr_mem :
        controlDisks.vertexRadius sv ∈
          Set.Icc (f (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1)) (f u) := by
      exact ⟨le_of_lt hzero_lt_radius, le_of_lt hdist_gt⟩
    have hzero_le_u :
        (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) ≤ u := by
      exact u.2.1
    obtain ⟨w, hw_interval, hw_eq⟩ :=
      (intermediate_value_Icc hzero_le_u hfcont.continuousOn hr_mem)
    have hw_sphere :
        edgeParam e w ∈
          Metric.sphere (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
      rw [Metric.mem_sphere, dist_eq_norm]
      simpa only [f, dist_eq_norm] using hw_eq
    have hw_carrier : edgeParam e w ∈ D.edgeCarrier e := by
      rw [hcarrier]
      exact ⟨w, rfl⟩
    have hw_eq_source :
        edgeParam e w = edgeEndpoints.sourceBoundaryPoint e := by
      exact edgeEndpoints.sourceBoundary_unique e (edgeParam e w) hw_sphere hw_carrier
    have hw_eq_s : w = s := by
      apply hinj
      simpa [s, sourceBoundaryParam_eq e] using hw_eq_source
    have hw_le_u : w ≤ u := hw_interval.2
    exact (not_lt_of_ge hw_le_u) (by simpa [hw_eq_s] using hu_lt_s)
  by_contra hnot
  have ht_le_s : t ≤ s := le_of_not_gt hnot
  have ht_in_source_closed :
      edgeParam e t ∈
        Metric.closedBall (D.vertexPlacement sv)
          (controlDisks.vertexRadius sv) :=
    source_prefix_closed t ht_le_s
  have ht_in_target_closed :
      edgeParam e t ∈
        Metric.closedBall (D.vertexPlacement tv)
          (controlDisks.vertexRadius tv) := by
    exact Metric.sphere_subset_closedBall ht_sphere
  exact (Set.disjoint_left.mp (controlDisks.vertex_vertex_disjoint hsv_ne_tv))
    ht_in_source_closed ht_in_target_closed
