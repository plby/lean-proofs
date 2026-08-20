import ErdosProblems.Erdos733.ST.PolygonalReplacementEdgeBoundaryEndpointData

open Classical
noncomputable section

universe u


-- [TABLET NODE: PolygonalReplacementIntersectionDiskCutOrder]
lemma PolygonalReplacementIntersectionDiskCutOrder {V : Type u} [Fintype V]
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
    (boundaryPoint_parameter_unique :
      ∀ i : boundaryPoints.boundaryIndex,
        ∃! t : Set.Icc (0 : ℝ) 1,
          edgeParam (boundaryPoints.owner i) t = boundaryPoints.point i)
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
          edgeParam e (intersectionCenterParam hx) = x.1)
    (intersectionCenterParam_between_endpoint_params :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          sourceBoundaryParam e < intersectionCenterParam hx ∧
            intersectionCenterParam hx < targetBoundaryParam e) :
    ∃ leftParam rightParam :
        (∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
          x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1),
      (∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e),
          leftParam hx < intersectionCenterParam hx ∧
            intersectionCenterParam hx < rightParam hx) ∧
      (∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e),
          edgeParam e (leftParam hx) ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
            edgeParam e (leftParam hx) ∈ D.edgeCarrier e ∧
              edgeParam e (rightParam hx) ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                edgeParam e (rightParam hx) ∈ D.edgeCarrier e ∧
                  edgeParam e (leftParam hx) ≠ edgeParam e (rightParam hx)) ∧
      (∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e)
          {p : EuclideanSpace ℝ (Fin 2)},
          p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
            p ∈ D.edgeCarrier e →
              p = edgeParam e (leftParam hx) ∨
                p = edgeParam e (rightParam hx)) ∧
      (∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e)
          {u : Set.Icc (0 : ℝ) 1},
          leftParam hx ≤ u →
            u ≤ rightParam hx →
              edgeParam e u ∈
                Metric.closedBall x.1 (controlDisks.intersectionRadius x)) ∧
      (∀ {x y : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e)
          (hy : y.1 ∈ D.edgeRelativeInterior e),
          x ≠ y →
            intersectionCenterParam hx < intersectionCenterParam hy →
              rightParam hx < leftParam hy) := by
-- BODY
  classical
  have leftRawParam_unique :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        ∃! t : Set.Icc (0 : ℝ) 1,
          edgeParam e t =
            boundaryPoints.point (boundaryPoints.intersectionBoundaryIndexLeft hx) := by
    intro x e hx
    have huniq :=
      boundaryPoint_parameter_unique (boundaryPoints.intersectionBoundaryIndexLeft hx)
    simpa [boundaryPoints.intersectionBoundaryIndexLeft_owner hx] using huniq
  have rightRawParam_unique :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        ∃! t : Set.Icc (0 : ℝ) 1,
          edgeParam e t =
            boundaryPoints.point (boundaryPoints.intersectionBoundaryIndexRight hx) := by
    intro x e hx
    have huniq :=
      boundaryPoint_parameter_unique (boundaryPoints.intersectionBoundaryIndexRight hx)
    simpa [boundaryPoints.intersectionBoundaryIndexRight_owner hx] using huniq
  let leftRawParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1 := fun {x} {e} hx =>
    Classical.choose (ExistsUnique.exists (leftRawParam_unique hx))
  let rightRawParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1 := fun {x} {e} hx =>
    Classical.choose (ExistsUnique.exists (rightRawParam_unique hx))
  have leftRawParam_eq :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        edgeParam e (leftRawParam hx) =
          boundaryPoints.point (boundaryPoints.intersectionBoundaryIndexLeft hx) := by
    intro x e hx
    exact Classical.choose_spec (ExistsUnique.exists (leftRawParam_unique hx))
  have rightRawParam_eq :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        edgeParam e (rightRawParam hx) =
          boundaryPoints.point (boundaryPoints.intersectionBoundaryIndexRight hx) := by
    intro x e hx
    exact Classical.choose_spec (ExistsUnique.exists (rightRawParam_unique hx))
  have leftRaw_sphere_carrier :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        edgeParam e (leftRawParam hx) ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
          edgeParam e (leftRawParam hx) ∈ D.edgeCarrier e := by
    intro x e hx
    simpa [leftRawParam_eq hx] using
      (boundaryPoints.intersectionBoundaryIndexLeft_boundary hx)
  have rightRaw_sphere_carrier :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        edgeParam e (rightRawParam hx) ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
          edgeParam e (rightRawParam hx) ∈ D.edgeCarrier e := by
    intro x e hx
    simpa [rightRawParam_eq hx] using
      (boundaryPoints.intersectionBoundaryIndexRight_boundary hx)
  have rawParam_ne :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        leftRawParam hx ≠ rightRawParam hx := by
    intro x e hx hparam
    have hpoint :
        boundaryPoints.point (boundaryPoints.intersectionBoundaryIndexLeft hx) =
          boundaryPoints.point (boundaryPoints.intersectionBoundaryIndexRight hx) := by
      calc
        boundaryPoints.point (boundaryPoints.intersectionBoundaryIndexLeft hx)
            = edgeParam e (leftRawParam hx) := (leftRawParam_eq hx).symm
        _ = edgeParam e (rightRawParam hx) := by rw [hparam]
        _ = boundaryPoints.point (boundaryPoints.intersectionBoundaryIndexRight hx) :=
            rightRawParam_eq hx
    exact (boundaryPoints.intersectionBoundaryIndex_ne hx) hpoint
  have sphere_point_eq_raw :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e)
        {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          p ∈ D.edgeCarrier e →
            p = edgeParam e (leftRawParam hx) ∨
              p = edgeParam e (rightRawParam hx) := by
    intro x e hx p hpSphere hpCarrier
    rcases boundaryPoints.intersection_boundary_point_eq_left_or_right hx hpSphere
        hpCarrier with hleft | hright
    · left
      simpa [leftRawParam_eq hx] using hleft
    · right
      simpa [rightRawParam_eq hx] using hright
  have raw_order_or :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        (leftRawParam hx < intersectionCenterParam hx ∧
          intersectionCenterParam hx < rightRawParam hx) ∨
        (rightRawParam hx < intersectionCenterParam hx ∧
          intersectionCenterParam hx < leftRawParam hx) := by
    intro x e hx
    rcases edgeParam_spec e with
      ⟨hcont, hinj, _hsource, _htarget, hcarrier, _hrel⟩
    let sourceParam : Set.Icc (0 : ℝ) 1 := sourceBoundaryParam e
    let targetParam : Set.Icc (0 : ℝ) 1 := targetBoundaryParam e
    let centerParam : Set.Icc (0 : ℝ) 1 := intersectionCenterParam hx
    let rho : ℝ := controlDisks.intersectionRadius x
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun u => dist (edgeParam e u) x.1
    have hfcont : Continuous f := hcont.dist continuous_const
    have hcenter_eq : edgeParam e centerParam = x.1 := by
      simpa [centerParam] using intersectionCenterParam_eq hx
    have hf_center : f centerParam = 0 := by
      dsimp [f]
      rw [hcenter_eq, dist_self]
    have hrho_pos : 0 < rho := controlDisks.intersectionRadius_pos x
    have hf_center_lt_rho : f centerParam < rho := by
      rw [hf_center]
      exact hrho_pos
    have hsource_lt_center : sourceParam < centerParam := by
      simpa [sourceParam, centerParam] using
        (intersectionCenterParam_between_endpoint_params hx).1
    have hcenter_lt_target : centerParam < targetParam := by
      simpa [targetParam, centerParam] using
        (intersectionCenterParam_between_endpoint_params hx).2
    let sv : V := edgeEndpoints.edgeSourceVertex e
    let tv : V := edgeEndpoints.edgeTargetVertex e
    have hsource_vertex_closed :
        edgeParam e sourceParam ∈
          Metric.closedBall (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
      have hsphere :
          edgeParam e sourceParam ∈
            Metric.sphere (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
        simpa [sourceParam, sv, sourceBoundaryParam_eq e] using
          (edgeEndpoints.sourceBoundary_on_control_boundary e).1
      exact Metric.sphere_subset_closedBall hsphere
    have hsource_not_intersection_closed :
        edgeParam e sourceParam ∉ Metric.closedBall x.1 rho := by
      intro hmem
      exact
        (Set.disjoint_left.mp (controlDisks.vertex_intersection_disjoint sv x))
          hsource_vertex_closed hmem
    have hf_source_gt_rho : rho < f sourceParam := by
      dsimp [f, rho] at *
      exact lt_of_not_ge (by
        intro hle
        exact hsource_not_intersection_closed
          (by simpa [Metric.mem_closedBall] using hle))
    have htarget_vertex_closed :
        edgeParam e targetParam ∈
          Metric.closedBall (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
      have hsphere :
          edgeParam e targetParam ∈
            Metric.sphere (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
        simpa [targetParam, tv, targetBoundaryParam_eq e] using
          (edgeEndpoints.targetBoundary_on_control_boundary e).1
      exact Metric.sphere_subset_closedBall hsphere
    have htarget_not_intersection_closed :
        edgeParam e targetParam ∉ Metric.closedBall x.1 rho := by
      intro hmem
      exact
        (Set.disjoint_left.mp (controlDisks.vertex_intersection_disjoint tv x))
          htarget_vertex_closed hmem
    have hf_target_gt_rho : rho < f targetParam := by
      dsimp [f, rho] at *
      exact lt_of_not_ge (by
        intro hle
        exact htarget_not_intersection_closed
          (by simpa [Metric.mem_closedBall] using hle))
    have hleft_mem : rho ∈ Set.Icc (f centerParam) (f sourceParam) :=
      ⟨le_of_lt hf_center_lt_rho, le_of_lt hf_source_gt_rho⟩
    obtain ⟨leftWitness, hleftWitness_interval, hleftWitness_eq⟩ :=
      (intermediate_value_Icc' hsource_lt_center.le hfcont.continuousOn) hleft_mem
    have hleftWitness_sphere :
        edgeParam e leftWitness ∈ Metric.sphere x.1 rho := by
      rw [Metric.mem_sphere]
      simpa [f] using hleftWitness_eq
    have hleftWitness_carrier : edgeParam e leftWitness ∈ D.edgeCarrier e := by
      rw [hcarrier]
      exact ⟨leftWitness, rfl⟩
    have hleftWitness_lt_center : leftWitness < centerParam := by
      have hne : leftWitness ≠ centerParam := by
        intro hsame
        have hzero : rho = 0 := by
          have hleftWitness_eq' := hleftWitness_eq
          rw [hsame] at hleftWitness_eq'
          simpa [f, hf_center] using hleftWitness_eq'.symm
        linarith
      exact lt_of_le_of_ne hleftWitness_interval.2 hne
    have hleft_side_raw :
        leftRawParam hx < centerParam ∨ rightRawParam hx < centerParam := by
      rcases sphere_point_eq_raw hx hleftWitness_sphere hleftWitness_carrier with
        hleft | hright
      · left
        have hparam : leftWitness = leftRawParam hx := hinj hleft
        simpa [centerParam, hparam] using hleftWitness_lt_center
      · right
        have hparam : leftWitness = rightRawParam hx := hinj hright
        simpa [centerParam, hparam] using hleftWitness_lt_center
    have hright_mem : rho ∈ Set.Icc (f centerParam) (f targetParam) :=
      ⟨le_of_lt hf_center_lt_rho, le_of_lt hf_target_gt_rho⟩
    obtain ⟨rightWitness, hrightWitness_interval, hrightWitness_eq⟩ :=
      (intermediate_value_Icc hcenter_lt_target.le hfcont.continuousOn) hright_mem
    have hrightWitness_sphere :
        edgeParam e rightWitness ∈ Metric.sphere x.1 rho := by
      rw [Metric.mem_sphere]
      simpa [f] using hrightWitness_eq
    have hrightWitness_carrier : edgeParam e rightWitness ∈ D.edgeCarrier e := by
      rw [hcarrier]
      exact ⟨rightWitness, rfl⟩
    have hcenter_lt_rightWitness : centerParam < rightWitness := by
      have hne : rightWitness ≠ centerParam := by
        intro hsame
        have hzero : rho = 0 := by
          have hrightWitness_eq' := hrightWitness_eq
          rw [hsame] at hrightWitness_eq'
          simpa [f, hf_center] using hrightWitness_eq'.symm
        linarith
      exact lt_of_le_of_ne hrightWitness_interval.1 (Ne.symm hne)
    have hright_side_raw :
        centerParam < leftRawParam hx ∨ centerParam < rightRawParam hx := by
      rcases sphere_point_eq_raw hx hrightWitness_sphere hrightWitness_carrier with
        hleft | hright
      · left
        have hparam : rightWitness = leftRawParam hx := hinj hleft
        simpa [centerParam, hparam] using hcenter_lt_rightWitness
      · right
        have hparam : rightWitness = rightRawParam hx := hinj hright
        simpa [centerParam, hparam] using hcenter_lt_rightWitness
    rcases hleft_side_raw with hleftLeft | hleftRight
    · rcases hright_side_raw with hrightLeft | hrightRight
      · exact False.elim ((not_lt_of_ge hleftLeft.le) hrightLeft)
      · exact Or.inl ⟨by simpa [centerParam] using hleftLeft,
          by simpa [centerParam] using hrightRight⟩
    · rcases hright_side_raw with hrightLeft | hrightRight
      · exact Or.inr ⟨by simpa [centerParam] using hleftRight,
          by simpa [centerParam] using hrightLeft⟩
      · exact False.elim ((not_lt_of_ge hleftRight.le) hrightRight)
  let leftParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1 := fun {x} {e} hx =>
    if leftRawParam hx < intersectionCenterParam hx then leftRawParam hx
    else rightRawParam hx
  let rightParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1 := fun {x} {e} hx =>
    if leftRawParam hx < intersectionCenterParam hx then rightRawParam hx
    else leftRawParam hx
  have ordered_params :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        leftParam hx < intersectionCenterParam hx ∧
          intersectionCenterParam hx < rightParam hx := by
    intro x e hx
    dsimp [leftParam, rightParam]
    by_cases hleft : leftRawParam hx < intersectionCenterParam hx
    · have hright : intersectionCenterParam hx < rightRawParam hx := by
        rcases raw_order_or hx with hcase | hcase
        · exact hcase.2
        · exact False.elim ((not_lt_of_ge hleft.le) hcase.2)
      constructor
      · simp [hleft]
      · simpa [hleft] using hright
    · have hcase :
          rightRawParam hx < intersectionCenterParam hx ∧
            intersectionCenterParam hx < leftRawParam hx := by
        rcases raw_order_or hx with hcase | hcase
        · exact False.elim (hleft hcase.1)
        · exact hcase
      constructor
      · simpa [hleft] using hcase.1
      · simpa [hleft] using hcase.2
  have ordered_sphere_carrier :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
        edgeParam e (leftParam hx) ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
          edgeParam e (leftParam hx) ∈ D.edgeCarrier e ∧
            edgeParam e (rightParam hx) ∈
                Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              edgeParam e (rightParam hx) ∈ D.edgeCarrier e ∧
                edgeParam e (leftParam hx) ≠ edgeParam e (rightParam hx) := by
    intro x e hx
    rcases edgeParam_spec e with ⟨_hcont, hinj, _hsource, _htarget, _hcarrier, _hrel⟩
    have hpoint_ne :
        edgeParam e (leftRawParam hx) ≠ edgeParam e (rightRawParam hx) := by
      intro h
      exact rawParam_ne hx (hinj h)
    dsimp [leftParam, rightParam]
    by_cases hleft : leftRawParam hx < intersectionCenterParam hx
    · have hleftFacts := leftRaw_sphere_carrier hx
      have hrightFacts := rightRaw_sphere_carrier hx
      simpa [hleft] using
        ⟨hleftFacts.1, hleftFacts.2, hrightFacts.1, hrightFacts.2, hpoint_ne⟩
    · have hleftFacts := leftRaw_sphere_carrier hx
      have hrightFacts := rightRaw_sphere_carrier hx
      have hpoint_ne' :
          edgeParam e (rightRawParam hx) ≠ edgeParam e (leftRawParam hx) :=
        Ne.symm hpoint_ne
      simpa [hleft] using
        ⟨hrightFacts.1, hrightFacts.2, hleftFacts.1, hleftFacts.2, hpoint_ne'⟩
  have ordered_sphere_point_eq :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e)
        {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          p ∈ D.edgeCarrier e →
            p = edgeParam e (leftParam hx) ∨
              p = edgeParam e (rightParam hx) := by
    intro x e hx p hpSphere hpCarrier
    dsimp [leftParam, rightParam]
    by_cases hleft : leftRawParam hx < intersectionCenterParam hx
    · simpa [hleft] using sphere_point_eq_raw hx hpSphere hpCarrier
    · rcases sphere_point_eq_raw hx hpSphere hpCarrier with hrawLeft | hrawRight
      · right
        simpa [hleft] using hrawLeft
      · left
        simpa [hleft] using hrawRight
  have interval_closed :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e)
        {u : Set.Icc (0 : ℝ) 1},
        leftParam hx ≤ u →
          u ≤ rightParam hx →
            edgeParam e u ∈
              Metric.closedBall x.1 (controlDisks.intersectionRadius x) := by
    intro x e hx u hleft_le_u hu_le_right
    by_contra hnot_closed
    rcases edgeParam_spec e with
      ⟨hcont, hinj, _hsource, _htarget, hcarrier, _hrel⟩
    let l : Set.Icc (0 : ℝ) 1 := leftParam hx
    let c : Set.Icc (0 : ℝ) 1 := intersectionCenterParam hx
    let r : Set.Icc (0 : ℝ) 1 := rightParam hx
    let rho : ℝ := controlDisks.intersectionRadius x
    let f : Set.Icc (0 : ℝ) 1 → ℝ := fun z => dist (edgeParam e z) x.1
    have hfcont : Continuous f := hcont.dist continuous_const
    have hcenter_eq : edgeParam e c = x.1 := by
      simpa [c] using intersectionCenterParam_eq hx
    have hf_center : f c = 0 := by
      dsimp [f]
      rw [hcenter_eq, dist_self]
    have hrho_pos : 0 < rho := controlDisks.intersectionRadius_pos x
    have hf_center_lt_rho : f c < rho := by
      rw [hf_center]
      exact hrho_pos
    have hdist_gt : rho < f u := by
      dsimp [f, rho] at *
      exact lt_of_not_ge (by
        intro hle
        exact hnot_closed (by simpa [Metric.mem_closedBall] using hle))
    have hordered : l < c ∧ c < r := by
      simpa [l, c, r] using ordered_params hx
    have hleft_sphere :
        edgeParam e l ∈ Metric.sphere x.1 rho := by
      simpa [l, rho] using (ordered_sphere_carrier hx).1
    have hright_sphere :
        edgeParam e r ∈ Metric.sphere x.1 rho := by
      simpa [r, rho] using (ordered_sphere_carrier hx).2.2.1
    have hleft_le_u' : l ≤ u := by simpa [l] using hleft_le_u
    have hu_le_right' : u ≤ r := by simpa [r] using hu_le_right
    by_cases hu_le_c : u ≤ c
    · have hu_ne_l : u ≠ l := by
        intro hu_eq_l
        exact hnot_closed (by
          simpa [l, hu_eq_l] using Metric.sphere_subset_closedBall hleft_sphere)
      have hl_lt_u : l < u :=
        lt_of_le_of_ne hleft_le_u' (by intro h; exact hu_ne_l h.symm)
      have hmem : rho ∈ Set.Icc (f c) (f u) :=
        ⟨le_of_lt hf_center_lt_rho, le_of_lt hdist_gt⟩
      obtain ⟨w, hw_interval, hw_eq⟩ :=
        (intermediate_value_Icc' hu_le_c hfcont.continuousOn) hmem
      have hw_sphere : edgeParam e w ∈ Metric.sphere x.1 rho := by
        rw [Metric.mem_sphere]
        simpa [f] using hw_eq
      have hw_carrier : edgeParam e w ∈ D.edgeCarrier e := by
        rw [hcarrier]
        exact ⟨w, rfl⟩
      have hw_ne_l : w ≠ l := by
        intro hw_eq_l
        have hu_le_l : u ≤ l := by simpa [hw_eq_l] using hw_interval.1
        exact (not_lt_of_ge hu_le_l) hl_lt_u
      have hw_ne_r : w ≠ r := by
        intro hw_eq_r
        have hr_le_c : r ≤ c := by simpa [hw_eq_r] using hw_interval.2
        exact (not_lt_of_ge hr_le_c) hordered.2
      rcases ordered_sphere_point_eq hx hw_sphere hw_carrier with hw_left | hw_right
      · exact hw_ne_l (hinj hw_left)
      · exact hw_ne_r (hinj hw_right)
    · have hc_le_u : c ≤ u := le_of_not_ge hu_le_c
      have hu_ne_r : u ≠ r := by
        intro hu_eq_r
        exact hnot_closed (by
          simpa [r, hu_eq_r] using Metric.sphere_subset_closedBall hright_sphere)
      have hu_lt_r : u < r :=
        lt_of_le_of_ne hu_le_right' hu_ne_r
      have hmem : rho ∈ Set.Icc (f c) (f u) :=
        ⟨le_of_lt hf_center_lt_rho, le_of_lt hdist_gt⟩
      obtain ⟨w, hw_interval, hw_eq⟩ :=
        (intermediate_value_Icc hc_le_u hfcont.continuousOn) hmem
      have hw_sphere : edgeParam e w ∈ Metric.sphere x.1 rho := by
        rw [Metric.mem_sphere]
        simpa [f] using hw_eq
      have hw_carrier : edgeParam e w ∈ D.edgeCarrier e := by
        rw [hcarrier]
        exact ⟨w, rfl⟩
      have hw_ne_l : w ≠ l := by
        intro hw_eq_l
        have hc_le_l : c ≤ l := by simpa [hw_eq_l] using hw_interval.1
        exact (not_lt_of_ge hc_le_l) hordered.1
      have hw_ne_r : w ≠ r := by
        intro hw_eq_r
        have hr_le_u : r ≤ u := by simpa [hw_eq_r] using hw_interval.2
        exact (not_lt_of_ge hr_le_u) hu_lt_r
      rcases ordered_sphere_point_eq hx hw_sphere hw_carrier with hw_left | hw_right
      · exact hw_ne_l (hinj hw_left)
      · exact hw_ne_r (hinj hw_right)
  have centers_ordered_disjoint :
      ∀ {x y : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e)
        (hy : y.1 ∈ D.edgeRelativeInterior e),
        x ≠ y →
          intersectionCenterParam hx < intersectionCenterParam hy →
            rightParam hx < leftParam hy := by
    intro x y e hx hy hxy hcenter_lt
    by_contra hnot
    let sx : Set.Icc (0 : ℝ) 1 := rightParam hx
    let ly : Set.Icc (0 : ℝ) 1 := leftParam hy
    let cx : Set.Icc (0 : ℝ) 1 := intersectionCenterParam hx
    let cy : Set.Icc (0 : ℝ) 1 := intersectionCenterParam hy
    let w : Set.Icc (0 : ℝ) 1 := max ly cx
    have hly_le_sx : ly ≤ sx := le_of_not_gt hnot
    have hx_order : leftParam hx < cx ∧ cx < sx := by
      simpa [cx, sx] using ordered_params hx
    have hy_order : ly < cy ∧ cy < rightParam hy := by
      simpa [ly, cy] using ordered_params hy
    have hx_left_le_w : leftParam hx ≤ w := by
      exact hx_order.1.le.trans (le_max_right ly cx)
    have hw_le_sx : w ≤ sx := by
      exact max_le hly_le_sx hx_order.2.le
    have hy_left_le_w : leftParam hy ≤ w := by
      simp [ly, w]
    have hw_le_yright : w ≤ rightParam hy := by
      have hcx_lt_yright : cx < rightParam hy := hcenter_lt.trans hy_order.2
      exact max_le (hy_order.1.le.trans hy_order.2.le) hcx_lt_yright.le
    have hw_x_closed :
        edgeParam e w ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) :=
      interval_closed hx hx_left_le_w hw_le_sx
    have hw_y_closed :
        edgeParam e w ∈ Metric.closedBall y.1 (controlDisks.intersectionRadius y) :=
      interval_closed hy hy_left_le_w hw_le_yright
    exact
      (Set.disjoint_left.mp (controlDisks.intersection_intersection_disjoint hxy))
        hw_x_closed hw_y_closed
  exact ⟨leftParam, rightParam, ordered_params, ordered_sphere_carrier,
    ordered_sphere_point_eq, interval_closed, centers_ordered_disjoint⟩
