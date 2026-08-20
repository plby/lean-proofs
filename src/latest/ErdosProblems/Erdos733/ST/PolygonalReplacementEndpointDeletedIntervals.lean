import ErdosProblems.Erdos733.ST.PolygonalReplacementEndpointBoundaryParamOrder

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementEndpointDeletedIntervals]
lemma PolygonalReplacementEndpointDeletedIntervals {V : Type u} [Fintype V]
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
    (∀ e, sourceBoundaryParam e < targetBoundaryParam e) ∧
      (∀ e (u : Set.Icc (0 : ℝ) 1), u ≤ sourceBoundaryParam e →
        edgeParam e u ∈
          Metric.closedBall
            (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
            (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e))) ∧
      (∀ e (u : Set.Icc (0 : ℝ) 1), targetBoundaryParam e ≤ u →
        edgeParam e u ∈
          Metric.closedBall
            (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
            (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e))) ∧
      (∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e))) ∧
      (∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e))) := by
-- BODY
  classical
  have endpoint_order :
      ∀ e, sourceBoundaryParam e < targetBoundaryParam e :=
    PolygonalReplacementEndpointBoundaryParamOrder G D controlDisks boundaryPoints
      edgeEndpoints edgeParam edgeParam_spec sourceBoundaryParam targetBoundaryParam
      sourceBoundaryParam_eq targetBoundaryParam_eq
  have source_prefix_closed :
      ∀ e (u : Set.Icc (0 : ℝ) 1), u ≤ sourceBoundaryParam e →
        edgeParam e u ∈
          Metric.closedBall
            (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
            (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) := by
    intro e u hu
    rcases edgeParam_spec e with
      ⟨hcont, hinj, hsource0, _htarget1, hcarrier, _hrel⟩
    let s : Set.Icc (0 : ℝ) 1 := sourceBoundaryParam e
    let sv : V := edgeEndpoints.edgeSourceVertex e
    have hzero :
        edgeParam e ⟨0, by simp⟩ = D.vertexPlacement sv := by
      simpa [sv] using hsource0.trans (edgeEndpoints.edgeSource_eq_vertexPlacement e)
    have hs_sphere :
        edgeParam e s ∈
          Metric.sphere (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
      simpa [s, sv, sourceBoundaryParam_eq e] using
        (edgeEndpoints.sourceBoundary_on_control_boundary e).1
    have hs_dist :
        dist (edgeParam e s) (D.vertexPlacement sv) =
          controlDisks.vertexRadius sv := by
      exact Metric.mem_sphere.mp hs_sphere
    by_contra hnot_closed
    have hdist_gt :
        controlDisks.vertexRadius sv <
          dist (edgeParam e u) (D.vertexPlacement sv) := by
      exact lt_of_not_ge (by
        intro hle
        exact hnot_closed (by
          simpa [Metric.mem_closedBall, dist_comm, sv] using hle))
    have hu_ne_s : u ≠ s := by
      intro hus
      have : dist (edgeParam e u) (D.vertexPlacement sv) =
          controlDisks.vertexRadius sv := by
        simpa [hus] using hs_dist
      linarith
    have hu_lt_s : u < s := lt_of_le_of_ne (by simpa [s] using hu) hu_ne_s
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
      apply Metric.mem_sphere.mpr
      simpa [f] using hw_eq
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
  have target_suffix_closed :
      ∀ e (u : Set.Icc (0 : ℝ) 1), targetBoundaryParam e ≤ u →
        edgeParam e u ∈
          Metric.closedBall
            (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
            (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) := by
    intro e u hu
    rcases edgeParam_spec e with
      ⟨hcont, hinj, _hsource0, htarget1, hcarrier, _hrel⟩
    let t : Set.Icc (0 : ℝ) 1 := targetBoundaryParam e
    let tv : V := edgeEndpoints.edgeTargetVertex e
    have hone :
        edgeParam e ⟨1, by simp⟩ = D.vertexPlacement tv := by
      simpa [tv] using htarget1.trans (edgeEndpoints.edgeTarget_eq_vertexPlacement e)
    have ht_sphere :
        edgeParam e t ∈
          Metric.sphere (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
      simpa [t, tv, targetBoundaryParam_eq e] using
        (edgeEndpoints.targetBoundary_on_control_boundary e).1
    have ht_dist :
        dist (edgeParam e t) (D.vertexPlacement tv) =
          controlDisks.vertexRadius tv := by
      exact Metric.mem_sphere.mp ht_sphere
    by_contra hnot_closed
    have hdist_gt :
        controlDisks.vertexRadius tv <
          dist (edgeParam e u) (D.vertexPlacement tv) := by
      exact lt_of_not_ge (by
        intro hle
        exact hnot_closed (by
          simpa [Metric.mem_closedBall, dist_comm, tv] using hle))
    have hu_ne_t : u ≠ t := by
      intro hut
      have : dist (edgeParam e u) (D.vertexPlacement tv) =
          controlDisks.vertexRadius tv := by
        simpa [hut] using ht_dist
      linarith
    have ht_lt_u : t < u := lt_of_le_of_ne (by simpa [t] using hu) (Ne.symm hu_ne_t)
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun z =>
      dist (edgeParam e z) (D.vertexPlacement tv)
    let g : Set.Icc (0 : ℝ) 1 → ℝ := fun z => -f z
    have hfcont : Continuous f := hcont.dist continuous_const
    have hgcont : Continuous g := hfcont.neg
    have hone_dist : f ⟨1, by simp⟩ = 0 := by
      dsimp [f]
      change
        dist (edgeParam e (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1))
            (D.vertexPlacement tv) = 0
      rw [hone, dist_self]
    have hneg_radius_mem :
        -controlDisks.vertexRadius tv ∈
          Set.Icc (g u) (g (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1)) := by
      constructor
      · dsimp [g, f]
        linarith
      · dsimp [g]
        change
          -controlDisks.vertexRadius tv ≤
            -(f (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1))
        rw [hone_dist]
        linarith [controlDisks.vertexRadius_pos tv]
    have hu_le_one :
        u ≤ (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
      exact u.2.2
    obtain ⟨w, hw_interval, hw_eq_neg⟩ :=
      (intermediate_value_Icc hu_le_one hgcont.continuousOn hneg_radius_mem)
    have hw_dist :
        f w = controlDisks.vertexRadius tv := by
      dsimp [g] at hw_eq_neg
      linarith
    have hw_sphere :
        edgeParam e w ∈
          Metric.sphere (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
      apply Metric.mem_sphere.mpr
      simpa [f] using hw_dist
    have hw_carrier : edgeParam e w ∈ D.edgeCarrier e := by
      rw [hcarrier]
      exact ⟨w, rfl⟩
    have hw_eq_target :
        edgeParam e w = edgeEndpoints.targetBoundaryPoint e := by
      exact edgeEndpoints.targetBoundary_unique e (edgeParam e w) hw_sphere hw_carrier
    have hw_eq_t : w = t := by
      apply hinj
      simpa [t, targetBoundaryParam_eq e] using hw_eq_target
    have hu_le_w : u ≤ w := hw_interval.1
    exact (not_lt_of_ge hu_le_w) (by simpa [hw_eq_t] using ht_lt_u)
  have middle_avoids_source_open :
      ∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) := by
    intro e u hs_le_u hu_le_t hball
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
      exact Metric.mem_sphere.mp hs_sphere
    have ht_not_source_closed :
        edgeParam e t ∉
          Metric.closedBall (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
      intro ht_source_closed
      have ht_target_closed :
          edgeParam e t ∈
            Metric.closedBall (D.vertexPlacement tv) (controlDisks.vertexRadius tv) :=
        Metric.sphere_subset_closedBall ht_sphere
      exact (Set.disjoint_left.mp (controlDisks.vertex_vertex_disjoint hsv_ne_tv))
        ht_source_closed ht_target_closed
    have hu_dist_lt :
        dist (edgeParam e u) (D.vertexPlacement sv) <
          controlDisks.vertexRadius sv := by
      simpa [Metric.mem_ball, dist_comm, sv] using hball
    have hu_ne_s : u ≠ s := by
      intro hus
      have hu_dist_lt_s :
          dist (edgeParam e s) (D.vertexPlacement sv) <
            controlDisks.vertexRadius sv := by
        simpa [s, hus, Metric.mem_ball, dist_comm, sv] using hball
      linarith
    have hs_lt_u : s < u :=
      lt_of_le_of_ne (by simpa [s] using hs_le_u) (Ne.symm hu_ne_s)
    have hu_le_t' : u ≤ t := by
      simpa [t] using hu_le_t
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun z =>
      dist (edgeParam e z) (D.vertexPlacement sv)
    have hfcont : Continuous f := hcont.dist continuous_const
    have ht_source_dist_gt :
        controlDisks.vertexRadius sv < f t := by
      dsimp [f]
      exact lt_of_not_ge (by
        intro hle
        exact ht_not_source_closed (by
          simpa [Metric.mem_closedBall, dist_comm, sv] using hle))
    have hr_mem :
        controlDisks.vertexRadius sv ∈ Set.Icc (f u) (f t) := by
      exact ⟨by simpa [f] using le_of_lt hu_dist_lt, le_of_lt ht_source_dist_gt⟩
    obtain ⟨w, hw_interval, hw_eq⟩ :=
      (intermediate_value_Icc hu_le_t' hfcont.continuousOn hr_mem)
    have hw_sphere :
        edgeParam e w ∈
          Metric.sphere (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
      apply Metric.mem_sphere.mpr
      simpa [f] using hw_eq
    have hw_carrier : edgeParam e w ∈ D.edgeCarrier e := by
      rw [hcarrier]
      exact ⟨w, rfl⟩
    have hw_eq_source :
        edgeParam e w = edgeEndpoints.sourceBoundaryPoint e := by
      exact edgeEndpoints.sourceBoundary_unique e (edgeParam e w) hw_sphere hw_carrier
    have hw_eq_s : w = s := by
      apply hinj
      simpa [s, sourceBoundaryParam_eq e] using hw_eq_source
    have hu_le_w : u ≤ w := hw_interval.1
    exact (not_lt_of_ge hu_le_w) (by simpa [hw_eq_s] using hs_lt_u)
  have middle_avoids_target_open :
      ∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) := by
    intro e u hs_le_u hu_le_t hball
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
    have ht_dist :
        dist (edgeParam e t) (D.vertexPlacement tv) =
          controlDisks.vertexRadius tv := by
      exact Metric.mem_sphere.mp ht_sphere
    have hs_not_target_closed :
        edgeParam e s ∉
          Metric.closedBall (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
      intro hs_target_closed
      have hs_source_closed :
          edgeParam e s ∈
            Metric.closedBall (D.vertexPlacement sv) (controlDisks.vertexRadius sv) :=
        Metric.sphere_subset_closedBall hs_sphere
      exact (Set.disjoint_left.mp (controlDisks.vertex_vertex_disjoint hsv_ne_tv))
        hs_source_closed hs_target_closed
    have hu_dist_lt :
        dist (edgeParam e u) (D.vertexPlacement tv) <
          controlDisks.vertexRadius tv := by
      simpa [Metric.mem_ball, dist_comm, tv] using hball
    have hu_ne_t : u ≠ t := by
      intro hut
      have hu_dist_lt_t :
          dist (edgeParam e t) (D.vertexPlacement tv) <
            controlDisks.vertexRadius tv := by
        simpa [t, hut, Metric.mem_ball, dist_comm, tv] using hball
      linarith
    have hs_le_u' : s ≤ u := by
      simpa [s] using hs_le_u
    have hu_lt_t : u < t :=
      lt_of_le_of_ne (by simpa [t] using hu_le_t) hu_ne_t
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun z =>
      dist (edgeParam e z) (D.vertexPlacement tv)
    have hfcont : Continuous f := hcont.dist continuous_const
    have hs_target_dist_gt :
        controlDisks.vertexRadius tv < f s := by
      dsimp [f]
      exact lt_of_not_ge (by
        intro hle
        exact hs_not_target_closed (by
          simpa [Metric.mem_closedBall, dist_comm, tv] using hle))
    have hr_mem :
        controlDisks.vertexRadius tv ∈ Set.Icc (f u) (f s) := by
      exact ⟨by simpa [f] using le_of_lt hu_dist_lt, le_of_lt hs_target_dist_gt⟩
    obtain ⟨w, hw_interval, hw_eq⟩ :=
      (intermediate_value_Icc' hs_le_u' hfcont.continuousOn hr_mem)
    have hw_sphere :
        edgeParam e w ∈
          Metric.sphere (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
      apply Metric.mem_sphere.mpr
      simpa [f] using hw_eq
    have hw_carrier : edgeParam e w ∈ D.edgeCarrier e := by
      rw [hcarrier]
      exact ⟨w, rfl⟩
    have hw_eq_target :
        edgeParam e w = edgeEndpoints.targetBoundaryPoint e := by
      exact edgeEndpoints.targetBoundary_unique e (edgeParam e w) hw_sphere hw_carrier
    have hw_eq_t : w = t := by
      apply hinj
      simpa [t, targetBoundaryParam_eq e] using hw_eq_target
    have ht_le_u : t ≤ u := by
      simpa [hw_eq_t] using hw_interval.2
    exact (not_lt_of_ge ht_le_u) hu_lt_t
  exact ⟨endpoint_order, source_prefix_closed, target_suffix_closed,
    middle_avoids_source_open, middle_avoids_target_open⟩
