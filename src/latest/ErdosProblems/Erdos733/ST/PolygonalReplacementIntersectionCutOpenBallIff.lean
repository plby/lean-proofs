import ErdosProblems.Erdos733.ST.PolygonalReplacementIntersectionDiskCutOrder

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementIntersectionCutOpenBallIff]
lemma PolygonalReplacementIntersectionCutOpenBallIff {V : Type u} [Fintype V]
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
    (intersectionLeftParam intersectionRightParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersection_cut_order :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e),
          intersectionLeftParam hx < intersectionCenterParam hx ∧
            intersectionCenterParam hx < intersectionRightParam hx)
    (intersection_cut_boundary :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e),
          edgeParam e (intersectionLeftParam hx) ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
            edgeParam e (intersectionLeftParam hx) ∈ D.edgeCarrier e ∧
              edgeParam e (intersectionRightParam hx) ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                edgeParam e (intersectionRightParam hx) ∈ D.edgeCarrier e ∧
                  edgeParam e (intersectionLeftParam hx) ≠
                    edgeParam e (intersectionRightParam hx))
    (intersection_cut_boundary_exhaustive :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e)
          {p : EuclideanSpace ℝ (Fin 2)},
          p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
            p ∈ D.edgeCarrier e →
              p = edgeParam e (intersectionLeftParam hx) ∨
                p = edgeParam e (intersectionRightParam hx))
    (intersection_cut_closedDisk :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e)
          {u : Set.Icc (0 : ℝ) 1},
          intersectionLeftParam hx ≤ u →
            u ≤ intersectionRightParam hx →
              edgeParam e u ∈
                Metric.closedBall x.1 (controlDisks.intersectionRadius x))
    (source_lt_intersectionLeft :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          sourceBoundaryParam e < intersectionLeftParam hx)
    (intersectionRight_lt_target :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          intersectionRightParam hx < targetBoundaryParam e) :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
      (hx : x.1 ∈ D.edgeRelativeInterior e)
      (u : Set.Icc (0 : ℝ) 1),
        sourceBoundaryParam e ≤ u →
          u ≤ targetBoundaryParam e →
            (edgeParam e u ∈
                Metric.ball x.1 (controlDisks.intersectionRadius x) ↔
              intersectionLeftParam hx < u ∧
                u < intersectionRightParam hx) := by
-- BODY
  classical
  intro x e hx u hs_le_u hu_le_t
  rcases edgeParam_spec e with
    ⟨hcont, hinj, _hsource0, _htarget1, hcarrier, _hrel⟩
  let s : Set.Icc (0 : ℝ) 1 := sourceBoundaryParam e
  let t : Set.Icc (0 : ℝ) 1 := targetBoundaryParam e
  let l : Set.Icc (0 : ℝ) 1 := intersectionLeftParam hx
  let c : Set.Icc (0 : ℝ) 1 := intersectionCenterParam hx
  let r : Set.Icc (0 : ℝ) 1 := intersectionRightParam hx
  let rho : ℝ := controlDisks.intersectionRadius x
  let f : Set.Icc (0 : ℝ) 1 → ℝ := fun z => dist (edgeParam e z) x.1
  have hfcont : Continuous f := hcont.dist continuous_const
  have hsource_lt_l : s < l := by
    simpa [s, l] using source_lt_intersectionLeft hx
  have hr_lt_target : r < t := by
    simpa [r, t] using intersectionRight_lt_target hx
  have hcut_order : l < c ∧ c < r := by
    simpa [l, c, r] using intersection_cut_order hx
  have hl_lt_r : l < r := hcut_order.1.trans hcut_order.2
  have hleft_sphere :
      edgeParam e l ∈ Metric.sphere x.1 rho := by
    simpa [l, rho] using (intersection_cut_boundary hx).1
  have hright_sphere :
      edgeParam e r ∈ Metric.sphere x.1 rho := by
    simpa [r, rho] using (intersection_cut_boundary hx).2.2.1
  have hsource_not_intersection_closed :
      edgeParam e s ∉ Metric.closedBall x.1 rho := by
    intro hsource_intersection_closed
    let sv : V := edgeEndpoints.edgeSourceVertex e
    have hsource_vertex_closed :
        edgeParam e s ∈
          Metric.closedBall (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
      have hsphere :
          edgeParam e s ∈
            Metric.sphere (D.vertexPlacement sv) (controlDisks.vertexRadius sv) := by
        simpa [s, sv, sourceBoundaryParam_eq e] using
          (edgeEndpoints.sourceBoundary_on_control_boundary e).1
      exact Metric.sphere_subset_closedBall hsphere
    exact
      (Set.disjoint_left.mp (controlDisks.vertex_intersection_disjoint sv x))
        hsource_vertex_closed hsource_intersection_closed
  have htarget_not_intersection_closed :
      edgeParam e t ∉ Metric.closedBall x.1 rho := by
    intro htarget_intersection_closed
    let tv : V := edgeEndpoints.edgeTargetVertex e
    have htarget_vertex_closed :
        edgeParam e t ∈
          Metric.closedBall (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
      have hsphere :
          edgeParam e t ∈
            Metric.sphere (D.vertexPlacement tv) (controlDisks.vertexRadius tv) := by
        simpa [t, tv, targetBoundaryParam_eq e] using
          (edgeEndpoints.targetBoundary_on_control_boundary e).1
      exact Metric.sphere_subset_closedBall hsphere
    exact
      (Set.disjoint_left.mp (controlDisks.vertex_intersection_disjoint tv x))
        htarget_vertex_closed htarget_intersection_closed
  constructor
  · intro hball
    have hdist_lt : f u < rho := by
      simpa [f, rho, Metric.mem_ball] using hball
    constructor
    · by_contra hnot_lt
      have hu_le_l : u ≤ l := le_of_not_gt hnot_lt
      have hu_ne_l : u ≠ l := by
        intro hu_eq_l
        have hleft_ball : edgeParam e l ∈ Metric.ball x.1 rho := by
          simpa [hu_eq_l] using hball
        have hleft_dist : f l = rho := by
          change dist (edgeParam e l) x.1 = rho
          rw [dist_eq_norm]
          simpa only [Metric.mem_sphere, dist_eq_norm] using hleft_sphere
        have hleft_dist_lt : f l < rho := by
          simpa [f, rho, Metric.mem_ball] using hleft_ball
        linarith
      have hu_lt_l : u < l := lt_of_le_of_ne hu_le_l hu_ne_l
      have hs_le_u' : s ≤ u := by simpa [s] using hs_le_u
      have hsource_dist_gt : rho < f s := by
        exact lt_of_not_ge (by
          intro hle
          exact hsource_not_intersection_closed
            (by simpa [f, rho, Metric.mem_closedBall] using hle))
      have hmem : rho ∈ Set.Icc (f u) (f s) :=
        ⟨le_of_lt hdist_lt, le_of_lt hsource_dist_gt⟩
      obtain ⟨w, hw_interval, hw_eq⟩ :=
        (intermediate_value_Icc' hs_le_u' hfcont.continuousOn) hmem
      have hw_sphere : edgeParam e w ∈ Metric.sphere x.1 rho := by
        rw [Metric.mem_sphere]
        simpa [f] using hw_eq
      have hw_carrier : edgeParam e w ∈ D.edgeCarrier e := by
        rw [hcarrier]
        exact ⟨w, rfl⟩
      have hw_lt_l : w < l := lt_of_le_of_lt hw_interval.2 hu_lt_l
      rcases intersection_cut_boundary_exhaustive hx hw_sphere hw_carrier with
        hw_left | hw_right
      · have hw_eq_l : w = l := hinj hw_left
        rw [hw_eq_l] at hw_lt_l
        exact (lt_irrefl l) hw_lt_l
      · have hw_eq_r : w = r := hinj hw_right
        exact (not_lt_of_ge hl_lt_r.le) (by simpa [hw_eq_r] using hw_lt_l)
    · by_contra hnot_lt
      have hr_le_u : r ≤ u := le_of_not_gt hnot_lt
      have hu_ne_r : u ≠ r := by
        intro hu_eq_r
        have hright_ball : edgeParam e r ∈ Metric.ball x.1 rho := by
          simpa [hu_eq_r] using hball
        have hright_dist : f r = rho := by
          change dist (edgeParam e r) x.1 = rho
          rw [dist_eq_norm]
          simpa only [Metric.mem_sphere, dist_eq_norm] using hright_sphere
        have hright_dist_lt : f r < rho := by
          simpa [f, rho, Metric.mem_ball] using hright_ball
        linarith
      have hr_lt_u : r < u := lt_of_le_of_ne hr_le_u (Ne.symm hu_ne_r)
      have hu_le_t' : u ≤ t := by simpa [t] using hu_le_t
      have htarget_dist_gt : rho < f t := by
        exact lt_of_not_ge (by
          intro hle
          exact htarget_not_intersection_closed
            (by simpa [f, rho, Metric.mem_closedBall] using hle))
      have hmem : rho ∈ Set.Icc (f u) (f t) :=
        ⟨le_of_lt hdist_lt, le_of_lt htarget_dist_gt⟩
      obtain ⟨w, hw_interval, hw_eq⟩ :=
        (intermediate_value_Icc hu_le_t' hfcont.continuousOn) hmem
      have hw_sphere : edgeParam e w ∈ Metric.sphere x.1 rho := by
        rw [Metric.mem_sphere]
        simpa [f] using hw_eq
      have hw_carrier : edgeParam e w ∈ D.edgeCarrier e := by
        rw [hcarrier]
        exact ⟨w, rfl⟩
      have hr_lt_w : r < w := lt_of_lt_of_le hr_lt_u hw_interval.1
      rcases intersection_cut_boundary_exhaustive hx hw_sphere hw_carrier with
        hw_left | hw_right
      · have hw_eq_l : w = l := hinj hw_left
        exact (not_lt_of_ge hl_lt_r.le) (by simpa [hw_eq_l] using hr_lt_w)
      · have hw_eq_r : w = r := hinj hw_right
        rw [hw_eq_r] at hr_lt_w
        exact (lt_irrefl r) hr_lt_w
  · rintro ⟨hl_lt_u, hu_lt_r⟩
    have hclosed :
        edgeParam e u ∈ Metric.closedBall x.1 rho :=
      intersection_cut_closedDisk hx hl_lt_u.le hu_lt_r.le
    by_contra hnot_ball
    have hdist_le : f u ≤ rho := by
      simpa [f, rho, Metric.mem_closedBall] using hclosed
    have hrho_le : rho ≤ f u := by
      exact le_of_not_gt (by
        intro hlt
        exact hnot_ball (by simpa [f, rho, Metric.mem_ball] using hlt))
    have hdist_eq : f u = rho := le_antisymm hdist_le hrho_le
    have hu_sphere : edgeParam e u ∈ Metric.sphere x.1 rho := by
      rw [Metric.mem_sphere]
      simpa [f, rho] using hdist_eq
    have hu_carrier : edgeParam e u ∈ D.edgeCarrier e := by
      rw [hcarrier]
      exact ⟨u, rfl⟩
    rcases intersection_cut_boundary_exhaustive hx hu_sphere hu_carrier with
      hu_left | hu_right
    · have hu_eq_l : u = l := hinj hu_left
      rw [hu_eq_l] at hl_lt_u
      change l < l at hl_lt_u
      exact (lt_irrefl l) hl_lt_u
    · have hu_eq_r : u = r := hinj hu_right
      rw [hu_eq_r] at hu_lt_r
      change r < r at hu_lt_r
      exact (lt_irrefl r) hu_lt_r
