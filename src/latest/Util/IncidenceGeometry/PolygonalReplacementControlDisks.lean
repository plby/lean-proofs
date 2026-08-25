import Util.IncidenceGeometry.PolygonalReplacementControlDiskData
import Util.IncidenceGeometry.PolygonalReplacementControlCenterDisks
import Util.IncidenceGeometry.GeometricArcCarrierEndpointOrInterior
import Util.IncidenceGeometry.GeometricArcCarrierCompact
import Util.IncidenceGeometry.StraightSegmentEndpointSphereBranch
import Util.IncidenceGeometry.StraightSegmentInteriorSphereBranch
import Util.IncidenceGeometry.CircularArcInteriorSphereBranch
import Util.IncidenceGeometry.CircularArcEndpointSphereBranch

open Classical
noncomputable section

lemma PolygonalReplacementControlDisks {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G) :
    Nonempty (PolygonalReplacementControlDiskData G D) := by
  obtain ⟨centerVertexRadius, centerIntersectionRadius, hcenterVertex_pos,
      hcenterIntersection_pos, hcenter_vertex_vertex, hcenter_vertex_intersection,
      hcenter_intersection_intersection⟩ :=
    PolygonalReplacementControlCenterDisks G D
  have vertex_center_on_carrier_incident :
      ∀ ⦃v : V⦄ ⦃e : G.edgeFinset⦄,
        D.vertexPlacement v ∈ D.edgeCarrier e → v ∈ e.1 := by
    intro v e hp
    have hsource_mem :
        D.vertexPlacement v = D.edgeSource e → v ∈ e.1 := by
      intro hsrc
      rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
      rcases hend with hend | hend
      · have hva : v = a := by
          apply D.vertexPlacement_injective
          exact hsrc.trans hend.1
        have : a ∈ (Sym2.mk a b : Sym2 V) := by simp
        simpa [heq, hva] using this
      · have hvb : v = b := by
          apply D.vertexPlacement_injective
          exact hsrc.trans hend.1
        have : b ∈ (Sym2.mk a b : Sym2 V) := by simp
        simpa [heq, hvb] using this
    have htarget_mem :
        D.vertexPlacement v = D.edgeTarget e → v ∈ e.1 := by
      intro htgt
      rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
      rcases hend with hend | hend
      · have hvb : v = b := by
          apply D.vertexPlacement_injective
          exact htgt.trans hend.2
        have : b ∈ (Sym2.mk a b : Sym2 V) := by simp
        simpa [heq, hvb] using this
      · have hva : v = a := by
          apply D.vertexPlacement_injective
          exact htgt.trans hend.2
        have : a ∈ (Sym2.mk a b : Sym2 V) := by simp
        simpa [heq, hva] using this
    rcases GeometricArcCarrierEndpointOrInterior D e hp with hsrc | htgt | hint
    · exact hsource_mem hsrc
    · exact htarget_mem htgt
    · exact False.elim ((D.no_vertex_in_edge_interior v e) hint)
  have intersection_center_on_carrier_passing :
      ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e : G.edgeFinset⦄,
        x.1 ∈ D.edgeCarrier e → x.1 ∈ D.edgeRelativeInterior e := by
    intro x e hp
    have hx_spec := (D.intersectionPoints_spec x.1).mp x.2
    rcases hx_spec with ⟨e₁, _e₂, _hne, hx₁, _hx₂⟩
    have hnot_vertex : ∀ v : V, x.1 ≠ D.vertexPlacement v := by
      intro v hv
      have hmem : D.vertexPlacement v ∈ D.edgeRelativeInterior e₁ := by
        simpa [hv] using hx₁
      exact (D.no_vertex_in_edge_interior v e₁ hmem).elim
    have hsource_not : x.1 ≠ D.edgeSource e := by
      intro hsrc
      rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, _heq, hend⟩
      rcases hend with hend | hend
      · exact hnot_vertex a (hsrc.trans hend.1)
      · exact hnot_vertex b (hsrc.trans hend.1)
    have htarget_not : x.1 ≠ D.edgeTarget e := by
      intro htgt
      rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, _heq, hend⟩
      rcases hend with hend | hend
      · exact hnot_vertex b (htgt.trans hend.2)
      · exact hnot_vertex a (htgt.trans hend.2)
    rcases GeometricArcCarrierEndpointOrInterior D e hp with hsrc | htgt | hint
    · exact False.elim (hsource_not hsrc)
    · exact False.elim (htarget_not htgt)
    · exact hint
  let vertexAvoidInf : V → ℝ := fun v =>
    Finset.univ.inf'
      (show (Finset.univ : Finset (Option G.edgeFinset)).Nonempty from
        ⟨none, Finset.mem_univ none⟩)
      (fun oe : Option G.edgeFinset =>
        match oe with
        | none => (1 : ℝ)
        | some e =>
            if v ∈ e.1 then (1 : ℝ)
            else Metric.infDist (D.vertexPlacement v) (D.edgeCarrier e))
  have vertexAvoidInf_pos : ∀ v, 0 < vertexAvoidInf v := by
    intro v
    dsimp [vertexAvoidInf]
    exact (Finset.lt_inf'_iff _).2 (by
      intro oe _hoe
      cases oe with
      | none =>
          simp
      | some e =>
          by_cases hve : v ∈ e.1
          · simp [hve]
          · have hnot : D.vertexPlacement v ∉ D.edgeCarrier e := by
              intro hp
              exact hve (vertex_center_on_carrier_incident hp)
            have hcompact := GeometricArcCarrierCompact D e
            have hpos :
                0 < Metric.infDist (D.vertexPlacement v) (D.edgeCarrier e) :=
              (hcompact.1.isClosed.notMem_iff_infDist_pos hcompact.2).mp hnot
            simpa [hve] using hpos)
  let vertexAvoidRadius : V → ℝ := fun v => vertexAvoidInf v / 2
  have vertexAvoidRadius_pos : ∀ v, 0 < vertexAvoidRadius v := by
    intro v
    dsimp [vertexAvoidRadius]
    exact half_pos (vertexAvoidInf_pos v)
  have vertexAvoidRadius_lt :
      ∀ ⦃v : V⦄ ⦃e : G.edgeFinset⦄,
        v ∉ e.1 →
          vertexAvoidRadius v <
            Metric.infDist (D.vertexPlacement v) (D.edgeCarrier e) := by
    intro v e hve
    have hhalf : vertexAvoidRadius v < vertexAvoidInf v := by
      dsimp [vertexAvoidRadius]
      exact half_lt_self (vertexAvoidInf_pos v)
    have hle :
        vertexAvoidInf v ≤
          Metric.infDist (D.vertexPlacement v) (D.edgeCarrier e) := by
      let f : Option G.edgeFinset → ℝ := fun oe =>
        match oe with
        | none => (1 : ℝ)
        | some e =>
            if v ∈ e.1 then (1 : ℝ)
            else Metric.infDist (D.vertexPlacement v) (D.edgeCarrier e)
      have hentry : vertexAvoidInf v ≤ f (some e) := by
        dsimp [vertexAvoidInf, f]
        exact Finset.inf'_le f (Finset.mem_univ (some e))
      simpa [f, hve] using hentry
    exact hhalf.trans_le hle
  let intersectionAvoidInf : {p // p ∈ D.intersectionPoints} → ℝ := fun x =>
    Finset.univ.inf'
      (show (Finset.univ : Finset (Option G.edgeFinset)).Nonempty from
        ⟨none, Finset.mem_univ none⟩)
      (fun oe : Option G.edgeFinset =>
        match oe with
        | none => (1 : ℝ)
        | some e =>
            if x.1 ∈ D.edgeRelativeInterior e then (1 : ℝ)
            else Metric.infDist x.1 (D.edgeCarrier e))
  have intersectionAvoidInf_pos :
      ∀ x : {p // p ∈ D.intersectionPoints}, 0 < intersectionAvoidInf x := by
    intro x
    dsimp [intersectionAvoidInf]
    exact (Finset.lt_inf'_iff _).2 (by
      intro oe _hoe
      cases oe with
      | none =>
          simp
      | some e =>
          by_cases hxe : x.1 ∈ D.edgeRelativeInterior e
          · simp [hxe]
          · have hnot : x.1 ∉ D.edgeCarrier e := by
              intro hp
              exact hxe (intersection_center_on_carrier_passing hp)
            have hcompact := GeometricArcCarrierCompact D e
            have hpos : 0 < Metric.infDist x.1 (D.edgeCarrier e) :=
              (hcompact.1.isClosed.notMem_iff_infDist_pos hcompact.2).mp hnot
            simpa [hxe] using hpos)
  let intersectionAvoidRadius : {p // p ∈ D.intersectionPoints} → ℝ :=
    fun x => intersectionAvoidInf x / 2
  have intersectionAvoidRadius_pos :
      ∀ x : {p // p ∈ D.intersectionPoints}, 0 < intersectionAvoidRadius x := by
    intro x
    dsimp [intersectionAvoidRadius]
    exact half_pos (intersectionAvoidInf_pos x)
  have intersectionAvoidRadius_lt :
      ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e : G.edgeFinset⦄,
        x.1 ∉ D.edgeRelativeInterior e →
          intersectionAvoidRadius x < Metric.infDist x.1 (D.edgeCarrier e) := by
    intro x e hxe
    have hhalf : intersectionAvoidRadius x < intersectionAvoidInf x := by
      dsimp [intersectionAvoidRadius]
      exact half_lt_self (intersectionAvoidInf_pos x)
    have hle :
        intersectionAvoidInf x ≤ Metric.infDist x.1 (D.edgeCarrier e) := by
      let f : Option G.edgeFinset → ℝ := fun oe =>
        match oe with
        | none => (1 : ℝ)
        | some e =>
            if x.1 ∈ D.edgeRelativeInterior e then (1 : ℝ)
            else Metric.infDist x.1 (D.edgeCarrier e)
      have hentry : intersectionAvoidInf x ≤ f (some e) := by
        dsimp [intersectionAvoidInf, f]
        exact Finset.inf'_le f (Finset.mem_univ (some e))
      simpa [f, hxe] using hentry
    exact hhalf.trans_le hle
  let circularArcData : G.edgeFinset → Prop := fun e =>
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
        (γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)),
      0 < r ∧
        Continuous γ ∧ Function.Injective γ ∧
          (∀ t, dist (γ t) c = r) ∧
            γ ⟨0, by simp⟩ = D.edgeSource e ∧
              γ ⟨1, by simp⟩ = D.edgeTarget e ∧
                D.edgeCarrier e = Set.range γ ∧
                  D.edgeRelativeInterior e =
                    Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                      γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)
  let edgeEndpointBranchBound : G.edgeFinset → ℝ := fun e =>
    if h : circularArcData e then
      let c := Classical.choose h
      let hc := Classical.choose_spec h
      let r := Classical.choose hc
      let hr := Classical.choose_spec hc
      let γ := Classical.choose hr
      let hγ := Classical.choose_spec hr
      let endpointData := CircularArcEndpointSphereBranch (c := c) (r := r)
        (γ := γ) hγ.1 hγ.2.1 hγ.2.2.1 hγ.2.2.2.1
      let ε₀ := Classical.choose endpointData
      let endpointData₀ := Classical.choose_spec endpointData
      let ε₁ := Classical.choose endpointData₀
      min ε₀ ε₁
    else
      (1 : ℝ)
  have edgeEndpointBranchBound_pos :
      ∀ e : G.edgeFinset, 0 < edgeEndpointBranchBound e := by
    intro e
    dsimp [edgeEndpointBranchBound]
    by_cases h : circularArcData e
    · rw [dif_pos h]
      let c := Classical.choose h
      let hc := Classical.choose_spec h
      let r := Classical.choose hc
      let hr := Classical.choose_spec hc
      let γ := Classical.choose hr
      let hγ := Classical.choose_spec hr
      let endpointData := CircularArcEndpointSphereBranch (c := c) (r := r)
        (γ := γ) hγ.1 hγ.2.1 hγ.2.2.1 hγ.2.2.2.1
      let ε₀ := Classical.choose endpointData
      let endpointData₀ := Classical.choose_spec endpointData
      let ε₁ := Classical.choose endpointData₀
      have endpointSpec := Classical.choose_spec endpointData₀
      exact lt_min endpointSpec.1 endpointSpec.2.1
    · rw [dif_neg h]
      norm_num
  let vertexBranchInf : V → ℝ := fun v =>
    Finset.univ.inf'
      (show (Finset.univ : Finset (Option G.edgeFinset)).Nonempty from
        ⟨none, Finset.mem_univ none⟩)
      (fun oe : Option G.edgeFinset =>
        match oe with
        | none => (1 : ℝ)
        | some e => if v ∈ e.1 then edgeEndpointBranchBound e else (1 : ℝ))
  have vertexBranchInf_pos : ∀ v, 0 < vertexBranchInf v := by
    intro v
    dsimp [vertexBranchInf]
    exact (Finset.lt_inf'_iff _).2 (by
      intro oe _hoe
      cases oe with
      | none =>
          norm_num
      | some e =>
          by_cases hve : v ∈ e.1
          · simpa [hve] using edgeEndpointBranchBound_pos e
          · simp [hve])
  let vertexBranchRadius : V → ℝ := fun v => vertexBranchInf v / 2
  have vertexBranchRadius_pos : ∀ v, 0 < vertexBranchRadius v := by
    intro v
    dsimp [vertexBranchRadius]
    exact half_pos (vertexBranchInf_pos v)
  have vertexBranchRadius_lt :
      ∀ ⦃v : V⦄ ⦃e : G.edgeFinset⦄,
        v ∈ e.1 → vertexBranchRadius v < edgeEndpointBranchBound e := by
    intro v e hve
    have hhalf : vertexBranchRadius v < vertexBranchInf v := by
      dsimp [vertexBranchRadius]
      exact half_lt_self (vertexBranchInf_pos v)
    have hle : vertexBranchInf v ≤ edgeEndpointBranchBound e := by
      let f : Option G.edgeFinset → ℝ := fun oe =>
        match oe with
        | none => (1 : ℝ)
        | some e => if v ∈ e.1 then edgeEndpointBranchBound e else (1 : ℝ)
      have hentry : vertexBranchInf v ≤ f (some e) := by
        dsimp [vertexBranchInf, f]
        exact Finset.inf'_le f (Finset.mem_univ (some e))
      simpa [f, hve] using hentry
    exact hhalf.trans_le hle
  let vertexRadius : V → ℝ := fun v =>
    min (min (centerVertexRadius v) (vertexAvoidRadius v)) (vertexBranchRadius v)
  let intersectionRadius : {p // p ∈ D.intersectionPoints} → ℝ :=
    fun x => min (centerIntersectionRadius x) (intersectionAvoidRadius x)
  have hvertex_pos : ∀ v, 0 < vertexRadius v := by
    intro v
    dsimp [vertexRadius]
    exact lt_min (lt_min (hcenterVertex_pos v) (vertexAvoidRadius_pos v))
      (vertexBranchRadius_pos v)
  have hintersection_pos : ∀ x, 0 < intersectionRadius x := by
    intro x
    dsimp [intersectionRadius]
    exact lt_min (hcenterIntersection_pos x) (intersectionAvoidRadius_pos x)
  have hvertex_le_center : ∀ v, vertexRadius v ≤ centerVertexRadius v := by
    intro v
    dsimp [vertexRadius]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hvertex_le_avoid : ∀ v, vertexRadius v ≤ vertexAvoidRadius v := by
    intro v
    dsimp [vertexRadius]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hvertex_le_branch : ∀ v, vertexRadius v ≤ vertexBranchRadius v := by
    intro v
    dsimp [vertexRadius]
    exact min_le_right _ _
  have vertexRadius_lt_endpointBranchBound :
      ∀ ⦃v : V⦄ ⦃e : G.edgeFinset⦄,
        v ∈ e.1 → vertexRadius v < edgeEndpointBranchBound e := by
    intro v e hve
    exact (hvertex_le_branch v).trans_lt (vertexBranchRadius_lt hve)
  have hintersection_le_center :
      ∀ x, intersectionRadius x ≤ centerIntersectionRadius x := by
    intro x
    dsimp [intersectionRadius]
    exact min_le_left _ _
  have hintersection_le_avoid :
      ∀ x, intersectionRadius x ≤ intersectionAvoidRadius x := by
    intro x
    dsimp [intersectionRadius]
    exact min_le_right _ _
  have edgeSource_vertex :
      ∀ e : G.edgeFinset, ∃ v : V, v ∈ e.1 ∧ D.edgeSource e = D.vertexPlacement v := by
    intro e
    rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
    rcases hend with hend | hend
    · exact ⟨a, by simpa [heq], hend.1⟩
    · exact ⟨b, by simpa [heq], hend.1⟩
  have edgeTarget_vertex :
      ∀ e : G.edgeFinset, ∃ v : V, v ∈ e.1 ∧ D.edgeTarget e = D.vertexPlacement v := by
    intro e
    rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
    rcases hend with hend | hend
    · exact ⟨b, by simpa [heq], hend.2⟩
    · exact ⟨a, by simpa [heq], hend.2⟩
  have final_vertex_vertex_disjoint :
      ∀ ⦃v w⦄, v ≠ w →
        Disjoint (Metric.closedBall (D.vertexPlacement v) (vertexRadius v))
          (Metric.closedBall (D.vertexPlacement w) (vertexRadius w)) := by
    intro v w hvw
    exact Disjoint.mono
      (Metric.closedBall_subset_closedBall (hvertex_le_center v))
      (Metric.closedBall_subset_closedBall (hvertex_le_center w))
      (hcenter_vertex_vertex hvw)
  have final_vertex_intersection_disjoint :
      ∀ v x,
        Disjoint (Metric.closedBall (D.vertexPlacement v) (vertexRadius v))
          (Metric.closedBall x.1 (intersectionRadius x)) := by
    intro v x
    exact Disjoint.mono
      (Metric.closedBall_subset_closedBall (hvertex_le_center v))
      (Metric.closedBall_subset_closedBall (hintersection_le_center x))
      (hcenter_vertex_intersection v x)
  have final_intersection_intersection_disjoint :
      ∀ ⦃x y⦄, x ≠ y →
        Disjoint (Metric.closedBall x.1 (intersectionRadius x))
          (Metric.closedBall y.1 (intersectionRadius y)) := by
    intro x y hxy
    exact Disjoint.mono
      (Metric.closedBall_subset_closedBall (hintersection_le_center x))
      (Metric.closedBall_subset_closedBall (hintersection_le_center y))
      (hcenter_intersection_intersection hxy)
  have vertexRadius_lt_vertex_dist :
      ∀ ⦃v w : V⦄, v ≠ w →
        vertexRadius v < dist (D.vertexPlacement v) (D.vertexPlacement w) := by
    intro v w hvw
    have hw_ball :
        D.vertexPlacement w ∈ Metric.closedBall (D.vertexPlacement w) (vertexRadius w) := by
      simpa [Metric.mem_closedBall] using (le_of_lt (hvertex_pos w))
    have hw_not_ball :
        D.vertexPlacement w ∉ Metric.closedBall (D.vertexPlacement v) (vertexRadius v) := by
      intro hwv_ball
      exact (Set.disjoint_left.mp (final_vertex_vertex_disjoint hvw)) hwv_ball hw_ball
    have hnot_le :
        ¬ dist (D.vertexPlacement w) (D.vertexPlacement v) ≤ vertexRadius v := by
      simpa [Metric.mem_closedBall] using hw_not_ball
    have hlt : vertexRadius v < dist (D.vertexPlacement w) (D.vertexPlacement v) :=
      lt_of_not_ge hnot_le
    simpa [dist_comm] using hlt
  have intersectionRadius_lt_vertex_dist :
      ∀ (x : {p // p ∈ D.intersectionPoints}) (v : V),
        intersectionRadius x < dist x.1 (D.vertexPlacement v) := by
    intro x v
    have hv_ball :
        D.vertexPlacement v ∈ Metric.closedBall (D.vertexPlacement v) (vertexRadius v) := by
      simpa [Metric.mem_closedBall] using (le_of_lt (hvertex_pos v))
    have hv_not_ball :
        D.vertexPlacement v ∉ Metric.closedBall x.1 (intersectionRadius x) := by
      intro hvx_ball
      have hdis := final_vertex_intersection_disjoint v x
      exact (Set.disjoint_left.mp hdis) hv_ball hvx_ball
    have hnot_le :
        ¬ dist (D.vertexPlacement v) x.1 ≤ intersectionRadius x := by
      simpa [Metric.mem_closedBall] using hv_not_ball
    have hlt : intersectionRadius x < dist (D.vertexPlacement v) x.1 :=
      lt_of_not_ge hnot_le
    simpa [dist_comm] using hlt
  have vertex_boundary_carrier_relativeInterior :
      ∀ ⦃v : V⦄ ⦃e : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ Metric.sphere (D.vertexPlacement v) (vertexRadius v) →
          p ∈ D.edgeCarrier e → p ∈ D.edgeRelativeInterior e := by
    intro v e p hpSphere hpCarrier
    have hpVertexBall :
        p ∈ Metric.closedBall (D.vertexPlacement v) (vertexRadius v) :=
      Metric.sphere_subset_closedBall hpSphere
    have hp_ne_center : p ≠ D.vertexPlacement v := by
      intro hp_eq
      have hdist := Metric.mem_sphere.mp hpSphere
      rw [hp_eq, dist_self] at hdist
      linarith [hvertex_pos v]
    rcases GeometricArcCarrierEndpointOrInterior D e hpCarrier with hsource | htarget | hinterior
    · rcases edgeSource_vertex e with ⟨u, _hu_mem, hsource_u⟩
      have hp_u : p = D.vertexPlacement u := hsource.trans hsource_u
      by_cases huv : u = v
      · exact False.elim (hp_ne_center (by simpa [huv] using hp_u))
      · have hp_u_ball :
            p ∈ Metric.closedBall (D.vertexPlacement u) (vertexRadius u) := by
          rw [hp_u]
          simpa [Metric.mem_closedBall] using (le_of_lt (hvertex_pos u))
        have hdis := final_vertex_vertex_disjoint huv
        exact False.elim ((Set.disjoint_left.mp hdis) hp_u_ball hpVertexBall)
    · rcases edgeTarget_vertex e with ⟨u, _hu_mem, htarget_u⟩
      have hp_u : p = D.vertexPlacement u := htarget.trans htarget_u
      by_cases huv : u = v
      · exact False.elim (hp_ne_center (by simpa [huv] using hp_u))
      · have hp_u_ball :
            p ∈ Metric.closedBall (D.vertexPlacement u) (vertexRadius u) := by
          rw [hp_u]
          simpa [Metric.mem_closedBall] using (le_of_lt (hvertex_pos u))
        have hdis := final_vertex_vertex_disjoint huv
        exact False.elim ((Set.disjoint_left.mp hdis) hp_u_ball hpVertexBall)
    · exact hinterior
  have intersection_boundary_carrier_relativeInterior :
      ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e : G.edgeFinset⦄
          ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ Metric.sphere x.1 (intersectionRadius x) →
          p ∈ D.edgeCarrier e → p ∈ D.edgeRelativeInterior e := by
    intro x e p hpSphere hpCarrier
    have hpIntersectionBall :
        p ∈ Metric.closedBall x.1 (intersectionRadius x) :=
      Metric.sphere_subset_closedBall hpSphere
    have hp_ne_center : p ≠ x.1 := by
      intro hp_eq
      have hdist := Metric.mem_sphere.mp hpSphere
      rw [hp_eq, dist_self] at hdist
      linarith [hintersection_pos x]
    rcases GeometricArcCarrierEndpointOrInterior D e hpCarrier with hsource | htarget | hinterior
    · rcases edgeSource_vertex e with ⟨u, _hu_mem, hsource_u⟩
      have hp_u : p = D.vertexPlacement u := hsource.trans hsource_u
      have hp_u_ball :
          p ∈ Metric.closedBall (D.vertexPlacement u) (vertexRadius u) := by
        rw [hp_u]
        simpa [Metric.mem_closedBall] using (le_of_lt (hvertex_pos u))
      have hdis := final_vertex_intersection_disjoint u x
      exact False.elim ((Set.disjoint_left.mp hdis) hp_u_ball hpIntersectionBall)
    · rcases edgeTarget_vertex e with ⟨u, _hu_mem, htarget_u⟩
      have hp_u : p = D.vertexPlacement u := htarget.trans htarget_u
      have hp_u_ball :
          p ∈ Metric.closedBall (D.vertexPlacement u) (vertexRadius u) := by
        rw [hp_u]
        simpa [Metric.mem_closedBall] using (le_of_lt (hvertex_pos u))
      have hdis := final_vertex_intersection_disjoint u x
      exact False.elim ((Set.disjoint_left.mp hdis) hp_u_ball hpIntersectionBall)
    · exact hinterior
  refine ⟨{
    vertexRadius := vertexRadius
    vertexRadius_pos := hvertex_pos
    intersectionRadius := intersectionRadius
    intersectionRadius_pos := hintersection_pos
    vertex_vertex_disjoint := ?_
    vertex_intersection_disjoint := ?_
    intersection_intersection_disjoint := ?_
    vertex_disk_meets_only_incident_edges := ?_
    vertex_boundary_unique := ?_
    vertex_boundary_point_edge_unique := ?_
    intersection_disk_meets_only_passing_edges := ?_
    intersection_boundary_two_points := ?_
    intersection_boundary_point_edge_unique := ?_ }⟩
  · intro v w hvw
    exact final_vertex_vertex_disjoint hvw
  · intro v x
    exact final_vertex_intersection_disjoint v x
  · intro x y hxy
    exact final_intersection_intersection_disjoint hxy
  · intro v e p hpball hpcarrier
    by_cases hve : v ∈ e.1
    · exact hve
    · exfalso
      have hpavoid :
          p ∈ Metric.closedBall (D.vertexPlacement v) (vertexAvoidRadius v) :=
        Metric.closedBall_subset_closedBall (hvertex_le_avoid v) hpball
      have hdis :
          Disjoint (Metric.closedBall (D.vertexPlacement v) (vertexAvoidRadius v))
            (D.edgeCarrier e) :=
        Metric.disjoint_closedBall_of_lt_infDist (vertexAvoidRadius_lt hve)
      exact (Set.disjoint_left.mp hdis) hpavoid hpcarrier
  · intro v e hve
    rcases hshape : D.edge_is_simple_lineSegment_or_circularArc e with hline | harc
    · rcases hline with ⟨_hne, hcarrier, _hrel⟩
      rcases D.edgeArc_endpoints e with ⟨a, b, hadj, heq, hend⟩
      have hv_ab : v = a ∨ v = b := by
        simpa [heq] using hve
      have hab : a ≠ b := G.ne_of_adj hadj
      have hpoint_ne_ab : D.vertexPlacement a ≠ D.vertexPlacement b := by
        intro h
        exact hab (D.vertexPlacement_injective h)
      have hpoint_ne_ba : D.vertexPlacement b ≠ D.vertexPlacement a := by
        exact Ne.symm hpoint_ne_ab
      rcases hend with hend | hend
      · rcases hv_ab with hva | hvb
        · have hvb_ne : v ≠ b := by
            intro h
            exact hab (hva.symm.trans h)
          have hpoint_ne : D.vertexPlacement v ≠ D.vertexPlacement b := by
            intro h
            exact hvb_ne (D.vertexPlacement_injective h)
          have hρlt :
              vertexRadius v < dist (D.vertexPlacement v) (D.vertexPlacement b) :=
            vertexRadius_lt_vertex_dist hvb_ne
          simpa [hcarrier, hend.1, hend.2, hva] using
            (StraightSegmentEndpointSphereBranch (a := D.vertexPlacement v)
              (b := D.vertexPlacement b) hpoint_ne (hvertex_pos v) hρlt)
        · have hva_ne : v ≠ a := by
            intro h
            exact hab (h.symm.trans hvb)
          have hpoint_ne : D.vertexPlacement v ≠ D.vertexPlacement a := by
            intro h
            exact hva_ne (D.vertexPlacement_injective h)
          have hρlt :
              vertexRadius v < dist (D.vertexPlacement v) (D.vertexPlacement a) :=
            vertexRadius_lt_vertex_dist hva_ne
          simpa [hcarrier, hend.1, hend.2, hvb, segment_symm] using
            (StraightSegmentEndpointSphereBranch (a := D.vertexPlacement v)
              (b := D.vertexPlacement a) hpoint_ne (hvertex_pos v) hρlt)
      · rcases hv_ab with hva | hvb
        · have hvb_ne : v ≠ b := by
            intro h
            exact hab (hva.symm.trans h)
          have hpoint_ne : D.vertexPlacement v ≠ D.vertexPlacement b := by
            intro h
            exact hvb_ne (D.vertexPlacement_injective h)
          have hρlt :
              vertexRadius v < dist (D.vertexPlacement v) (D.vertexPlacement b) :=
            vertexRadius_lt_vertex_dist hvb_ne
          simpa [hcarrier, hend.1, hend.2, hva, segment_symm] using
            (StraightSegmentEndpointSphereBranch (a := D.vertexPlacement v)
              (b := D.vertexPlacement b) hpoint_ne (hvertex_pos v) hρlt)
        · have hva_ne : v ≠ a := by
            intro h
            exact hab (h.symm.trans hvb)
          have hpoint_ne : D.vertexPlacement v ≠ D.vertexPlacement a := by
            intro h
            exact hva_ne (D.vertexPlacement_injective h)
          have hρlt :
              vertexRadius v < dist (D.vertexPlacement v) (D.vertexPlacement a) :=
            vertexRadius_lt_vertex_dist hva_ne
          simpa [hcarrier, hend.1, hend.2, hvb] using
            (StraightSegmentEndpointSphereBranch (a := D.vertexPlacement v)
              (b := D.vertexPlacement a) hpoint_ne (hvertex_pos v) hρlt)
    · let hcir : circularArcData e := harc
      let c := Classical.choose hcir
      let hc := Classical.choose_spec hcir
      let r := Classical.choose hc
      let hrData := Classical.choose_spec hc
      let γ := Classical.choose hrData
      let hγData := Classical.choose_spec hrData
      rcases hγData with
        ⟨hr, hγcont, hγinj, hcircle, hsource, htarget, hcarrier, hrel⟩
      let endpointData := CircularArcEndpointSphereBranch (c := c) (r := r)
        (γ := γ) hr hγcont hγinj hcircle
      let ε₀ := Classical.choose endpointData
      let endpointData₀ := Classical.choose_spec endpointData
      let ε₁ := Classical.choose endpointData₀
      have endpointSpec := Classical.choose_spec endpointData₀
      have hstart :
          ∀ {ρ : ℝ}, 0 < ρ → ρ < ε₀ →
            ∃! p : EuclideanSpace ℝ (Fin 2),
              p ∈ Metric.sphere (γ ⟨0, by simp⟩) ρ ∧ p ∈ Set.range γ :=
        endpointSpec.2.2.1
      have hendpoint :
          ∀ {ρ : ℝ}, 0 < ρ → ρ < ε₁ →
            ∃! p : EuclideanSpace ℝ (Fin 2),
              p ∈ Metric.sphere (γ ⟨1, by simp⟩) ρ ∧ p ∈ Set.range γ :=
        endpointSpec.2.2.2
      have hρlt_endpoint :
          vertexRadius v < min ε₀ ε₁ := by
        have hlt := vertexRadius_lt_endpointBranchBound hve
        dsimp [edgeEndpointBranchBound] at hlt
        rw [dif_pos hcir] at hlt
        simpa only [hcir, c, hc, r, hrData, γ, endpointData, ε₀, endpointData₀, ε₁] using hlt
      have hρlt_start : vertexRadius v < ε₀ :=
        hρlt_endpoint.trans_le (min_le_left _ _)
      have hρlt_end : vertexRadius v < ε₁ :=
        hρlt_endpoint.trans_le (min_le_right _ _)
      rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hends⟩
      have hv_ab : v = a ∨ v = b := by
        simpa [heq] using hve
      rcases hends with hends | hends
      · rcases hv_ab with hva | hvb
        · have hcenter : D.vertexPlacement v = γ ⟨0, by simp⟩ := by
            calc
              D.vertexPlacement v = D.vertexPlacement a := by rw [hva]
              _ = D.edgeSource e := hends.1.symm
              _ = γ ⟨0, by simp⟩ := hsource.symm
          rw [hcenter, hcarrier]
          exact hstart (hvertex_pos v) hρlt_start
        · have hcenter : D.vertexPlacement v = γ ⟨1, by simp⟩ := by
            calc
              D.vertexPlacement v = D.vertexPlacement b := by rw [hvb]
              _ = D.edgeTarget e := hends.2.symm
              _ = γ ⟨1, by simp⟩ := htarget.symm
          rw [hcenter, hcarrier]
          exact hendpoint (hvertex_pos v) hρlt_end
      · rcases hv_ab with hva | hvb
        · have hcenter : D.vertexPlacement v = γ ⟨1, by simp⟩ := by
            calc
              D.vertexPlacement v = D.vertexPlacement a := by rw [hva]
              _ = D.edgeTarget e := hends.2.symm
              _ = γ ⟨1, by simp⟩ := htarget.symm
          rw [hcenter, hcarrier]
          exact hendpoint (hvertex_pos v) hρlt_end
        · have hcenter : D.vertexPlacement v = γ ⟨0, by simp⟩ := by
            calc
              D.vertexPlacement v = D.vertexPlacement b := by rw [hvb]
              _ = D.edgeSource e := hends.1.symm
              _ = γ ⟨0, by simp⟩ := hsource.symm
          rw [hcenter, hcarrier]
          exact hstart (hvertex_pos v) hρlt_start
  · intro v e₁ e₂ p _hve₁ _hve₂ hpSphere hpCarrier₁ hpCarrier₂
    by_cases heq : e₁ = e₂
    · exact heq
    · exfalso
      have hpInterior₁ :
          p ∈ D.edgeRelativeInterior e₁ :=
        vertex_boundary_carrier_relativeInterior hpSphere hpCarrier₁
      have hpInterior₂ :
          p ∈ D.edgeRelativeInterior e₂ :=
        vertex_boundary_carrier_relativeInterior hpSphere hpCarrier₂
      have hpIntersection : p ∈ D.intersectionPoints :=
        (D.intersectionPoints_spec p).mpr
          ⟨e₁, e₂, heq, hpInterior₁, hpInterior₂⟩
      let y : {p // p ∈ D.intersectionPoints} := ⟨p, hpIntersection⟩
      have hpVertexBall :
          p ∈ Metric.closedBall (D.vertexPlacement v) (vertexRadius v) :=
        Metric.sphere_subset_closedBall hpSphere
      have hpIntersectionBall :
          p ∈ Metric.closedBall y.1 (intersectionRadius y) := by
        dsimp [y]
        simpa [Metric.mem_closedBall] using (le_of_lt (hintersection_pos y))
      have hdis := final_vertex_intersection_disjoint v y
      exact (Set.disjoint_left.mp hdis) hpVertexBall hpIntersectionBall
  · intro x e p hpball hpcarrier
    by_cases hxe : x.1 ∈ D.edgeRelativeInterior e
    · exact hxe
    · exfalso
      have hpavoid : p ∈ Metric.closedBall x.1 (intersectionAvoidRadius x) :=
        Metric.closedBall_subset_closedBall (hintersection_le_avoid x) hpball
      have hdis :
          Disjoint (Metric.closedBall x.1 (intersectionAvoidRadius x))
            (D.edgeCarrier e) :=
        Metric.disjoint_closedBall_of_lt_infDist (intersectionAvoidRadius_lt hxe)
      exact (Set.disjoint_left.mp hdis) hpavoid hpcarrier
  · intro x e hxe
    rcases D.edge_is_simple_lineSegment_or_circularArc e with hline | harc
    · rcases hline with ⟨_hne, hcarrier, hrel⟩
      have hx_open :
          x.1 ∈ openSegment ℝ (D.edgeSource e) (D.edgeTarget e) := by
        simpa [hrel] using hxe
      rcases edgeSource_vertex e with ⟨u, _hu_mem, hsource_u⟩
      rcases edgeTarget_vertex e with ⟨v, _hv_mem, htarget_v⟩
      have hρlt_source :
          intersectionRadius x < dist x.1 (D.edgeSource e) := by
        simpa [hsource_u] using intersectionRadius_lt_vertex_dist x u
      have hρlt_target :
          intersectionRadius x < dist x.1 (D.edgeTarget e) := by
        simpa [htarget_v] using intersectionRadius_lt_vertex_dist x v
      simpa [hcarrier] using
          (StraightSegmentInteriorSphereBranch
            (a := D.edgeSource e) (b := D.edgeTarget e) (x := x.1)
            hx_open (hintersection_pos x) hρlt_source hρlt_target)
    · rcases harc with
        ⟨c, r, γ, hr, hγcont, hγinj, hcircle, hsource, htarget, hcarrier, hrel⟩
      have hxe_range :
          x.1 ∈ Set.range
            (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
              γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩) := by
        simpa [hrel] using hxe
      rcases hxe_range with ⟨t, ht⟩
      let τ : Set.Icc (0 : ℝ) 1 :=
        ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩
      have hτx : γ τ = x.1 := by
        simpa [τ] using ht
      rcases edgeSource_vertex e with ⟨u, _hu_mem, hsource_u⟩
      rcases edgeTarget_vertex e with ⟨v, _hv_mem, htarget_v⟩
      have hρlt_source :
          intersectionRadius x < dist (γ τ) (γ ⟨0, by simp⟩) := by
        have hlt :
            intersectionRadius x < dist x.1 (D.vertexPlacement u) :=
          intersectionRadius_lt_vertex_dist x u
        have hsource_vertex : γ ⟨0, by simp⟩ = D.vertexPlacement u :=
          hsource.trans hsource_u
        rw [hτx, hsource_vertex]
        exact hlt
      have hρlt_target :
          intersectionRadius x < dist (γ τ) (γ ⟨1, by simp⟩) := by
        have hlt :
            intersectionRadius x < dist x.1 (D.vertexPlacement v) :=
          intersectionRadius_lt_vertex_dist x v
        have htarget_vertex : γ ⟨1, by simp⟩ = D.vertexPlacement v :=
          htarget.trans htarget_v
        rw [hτx, htarget_vertex]
        exact hlt
      simpa [hcarrier, hτx] using
        (CircularArcInteriorSphereBranch (c := c) (r := r) (γ := γ)
          hr hγcont hγinj hcircle τ t.2.1 t.2.2
          (hintersection_pos x) hρlt_source hρlt_target)
  · intro x e₁ e₂ p _hx₁ _hx₂ hpSphere hpCarrier₁ hpCarrier₂
    by_cases heq : e₁ = e₂
    · exact heq
    · exfalso
      have hp_ne_center : p ≠ x.1 := by
        intro hp_eq
        have hdist := Metric.mem_sphere.mp hpSphere
        rw [hp_eq, dist_self] at hdist
        linarith [hintersection_pos x]
      have hpInterior₁ :
          p ∈ D.edgeRelativeInterior e₁ :=
        intersection_boundary_carrier_relativeInterior hpSphere hpCarrier₁
      have hpInterior₂ :
          p ∈ D.edgeRelativeInterior e₂ :=
        intersection_boundary_carrier_relativeInterior hpSphere hpCarrier₂
      have hpIntersection : p ∈ D.intersectionPoints :=
        (D.intersectionPoints_spec p).mpr
          ⟨e₁, e₂, heq, hpInterior₁, hpInterior₂⟩
      let y : {p // p ∈ D.intersectionPoints} := ⟨p, hpIntersection⟩
      have hxy : x ≠ y := by
        intro hxy
        have hxval := congrArg Subtype.val hxy
        exact hp_ne_center (by simpa [y] using hxval.symm)
      have hpIntersectionBallX :
          p ∈ Metric.closedBall x.1 (intersectionRadius x) :=
        Metric.sphere_subset_closedBall hpSphere
      have hpIntersectionBallY :
          p ∈ Metric.closedBall y.1 (intersectionRadius y) := by
        dsimp [y]
        simpa [Metric.mem_closedBall] using (le_of_lt (hintersection_pos y))
      have hdis := final_intersection_intersection_disjoint hxy
      exact (Set.disjoint_left.mp hdis) hpIntersectionBallX hpIntersectionBallY
