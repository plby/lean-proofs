import Util.IncidenceGeometry.PolygonalReplacementEndpointBoundaryParamOrder

open Classical
noncomputable section

universe u

lemma PolygonalReplacementIntersectionCenterEndpointParamOrder {V : Type u} [Fintype V]
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
        edgeEndpoints.targetBoundaryPoint e)
    (intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersectionCenterParam_eq :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          edgeParam e (intersectionCenterParam hx) = x.1) :
    (∀ e, sourceBoundaryParam e < targetBoundaryParam e) ∧
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          sourceBoundaryParam e < intersectionCenterParam hx ∧
            intersectionCenterParam hx < targetBoundaryParam e := by
  classical
  constructor
  · exact
      PolygonalReplacementEndpointBoundaryParamOrder G D controlDisks boundaryPoints
        edgeEndpoints edgeParam edgeParam_spec sourceBoundaryParam
        targetBoundaryParam sourceBoundaryParam_eq targetBoundaryParam_eq
  · intro x e hx
    rcases edgeParam_spec e with
      ⟨hcont, hinj, hsource0, htarget1, hcarrier, _hrel⟩
    let s : Set.Icc (0 : ℝ) 1 := sourceBoundaryParam e
    let t : Set.Icc (0 : ℝ) 1 := targetBoundaryParam e
    let c : Set.Icc (0 : ℝ) 1 := intersectionCenterParam hx
    let sv : V := edgeEndpoints.edgeSourceVertex e
    let tv : V := edgeEndpoints.edgeTargetVertex e
    have hzero :
        edgeParam e ⟨0, by simp⟩ = D.vertexPlacement sv := by
      simpa [sv] using hsource0.trans (edgeEndpoints.edgeSource_eq_vertexPlacement e)
    have hone :
        edgeParam e ⟨1, by simp⟩ = D.vertexPlacement tv := by
      simpa [tv] using htarget1.trans (edgeEndpoints.edgeTarget_eq_vertexPlacement e)
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
    have ht_dist :
        dist (edgeParam e t) (D.vertexPlacement tv) =
          controlDisks.vertexRadius tv := by
      rw [dist_eq_norm]
      simpa only [Metric.mem_sphere, dist_eq_norm] using ht_sphere
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
    have target_suffix_closed :
        ∀ u : Set.Icc (0 : ℝ) 1, t ≤ u →
          edgeParam e u ∈
            Metric.closedBall (D.vertexPlacement tv)
              (controlDisks.vertexRadius tv) := by
      intro u hu
      by_contra hnot_closed
      have hdist_gt :
          controlDisks.vertexRadius tv <
            dist (edgeParam e u) (D.vertexPlacement tv) := by
        exact lt_of_not_ge (by
          intro hle
          exact hnot_closed (by simpa [Metric.mem_closedBall, dist_comm] using hle))
      have hu_ne_t : u ≠ t := by
        intro hut
        have : dist (edgeParam e u) (D.vertexPlacement tv) =
            controlDisks.vertexRadius tv := by
          simpa [hut] using ht_dist
        linarith
      have ht_lt_u : t < u := lt_of_le_of_ne hu (Ne.symm hu_ne_t)
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
        rw [Metric.mem_sphere, dist_eq_norm]
        simpa only [f, dist_eq_norm] using hw_dist
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
    have hc_intersection_closed :
        edgeParam e c ∈
          Metric.closedBall x.1 (controlDisks.intersectionRadius x) := by
      rw [show edgeParam e c = x.1 by
        simpa [c] using intersectionCenterParam_eq hx]
      exact Metric.mem_closedBall_self
        (le_of_lt (controlDisks.intersectionRadius_pos x))
    constructor
    · by_contra hnot
      have hc_le_s : c ≤ s := le_of_not_gt hnot
      have hc_source_closed := source_prefix_closed c hc_le_s
      exact (Set.disjoint_left.mp (controlDisks.vertex_intersection_disjoint sv x))
        hc_source_closed hc_intersection_closed
    · by_contra hnot
      have ht_le_c : t ≤ c := le_of_not_gt hnot
      have hc_target_closed := target_suffix_closed c ht_le_c
      exact (Set.disjoint_left.mp (controlDisks.vertex_intersection_disjoint tv x))
        hc_target_closed hc_intersection_closed
