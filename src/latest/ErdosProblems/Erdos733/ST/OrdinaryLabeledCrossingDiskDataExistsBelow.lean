import ErdosProblems.Erdos733.ST.OrdinaryLabeledCrossingDiskData
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchDataExistsBelow
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryLabeledCrossingDiskDataExistsBelow]
lemma OrdinaryLabeledCrossingDiskDataExistsBelow
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (x : {p // p ∈ D.crossingSet})
    (upper : ℝ) (hupper : 0 < upper) :
    ∃ data : OrdinaryLabeledCrossingDiskData G D x,
      data.radius < upper := by
-- BODY
  let E := EuclideanSpace ℝ (Fin 2)
  rcases (D.crossingSet_spec x.1).mp x.2 with
    ⟨firstEdge, secondEdge, hedges_ne, hx_first, hx_second⟩
  have hcenter_not_vertex : ∀ v : V, x.1 ≠ D.vertexPlacement v := by
    intro v h
    exact D.no_vertex_in_edge_interior v firstEdge (h ▸ hx_first)
  have howner : ∀ e : G.edgeFinset,
      x.1 ∈ (D.edgeArc e).relativeInterior →
        e = firstEdge ∨ e = secondEdge := by
    intro e hxe
    by_contra h
    push Not at h
    exact D.no_three_edge_interiors_meet hedges_ne h.1.symm h.2.symm
      hx_first hx_second hxe
  have hcenter_not_other_carrier : ∀ e : G.edgeFinset,
      e ≠ firstEdge → e ≠ secondEdge → x.1 ∉ (D.edgeArc e).carrier := by
    intro e he_first he_second hcarrier
    have he_owner := howner e ?_
    · exact he_owner.elim he_first he_second
    rw [(D.edgeArc e).relativeInterior_eq]
    refine ⟨hcarrier, ?_⟩
    rcases D.edgeArc_endpoints e with ⟨u, v, _huv, _he, hends⟩
    rcases hends with hends | hends
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hcenter_not_vertex u (h.trans hends.1),
        fun h => hcenter_not_vertex v (h.trans hends.2)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hcenter_not_vertex v (h.trans hends.1),
        fun h => hcenter_not_vertex u (h.trans hends.2)⟩
  let forbiddenEdges : Set E :=
    ⋃ e : G.edgeFinset,
      if e = firstEdge ∨ e = secondEdge then (∅ : Set E)
      else ⋃ j : Fin ((D.edgeArc e).vertices.length - 1),
        segment ℝ (D.edgeArc e).vertices[j.1]
          (D.edgeArc e).vertices[j.1 + 1]
  let forbiddenVertices : Set E := ⋃ v : V, {D.vertexPlacement v}
  let forbiddenCenters : Set E :=
    ⋃ y : {p // p ∈ D.crossingSet},
      if y = x then (∅ : Set E) else {y.1}
  let forbidden := forbiddenEdges ∪ forbiddenVertices ∪ forbiddenCenters
  have hforbidden_closed : IsClosed forbidden := by
    apply IsClosed.union
    · apply IsClosed.union
      · exact isClosed_iUnion_of_finite fun e => by
          split_ifs
          · exact isClosed_empty
          · exact isClosed_iUnion_of_finite fun j => by
              rw [← convexHull_pair]
              exact (by simp : ({(D.edgeArc e).vertices[j.1],
                (D.edgeArc e).vertices[j.1 + 1]} : Set E).Finite).isClosed_convexHull ℝ
      · exact isClosed_iUnion_of_finite fun v => isClosed_singleton
    · exact isClosed_iUnion_of_finite fun y => by
        split_ifs
        · exact isClosed_empty
        · exact isClosed_singleton
  have hx_not_forbidden : x.1 ∉ forbidden := by
    intro hx
    rcases hx with (hx_edges | hx_vertices) | hx_centers
    · rcases Set.mem_iUnion.mp hx_edges with ⟨e, hxe⟩
      by_cases he : e = firstEdge ∨ e = secondEdge
      · simp [he] at hxe
      · rw [if_neg he] at hxe
        rcases Set.mem_iUnion.mp hxe with ⟨j, hxj⟩
        apply hcenter_not_other_carrier e (fun h => he (Or.inl h))
          (fun h => he (Or.inr h))
        rw [(D.edgeArc e).carrier_eq]
        exact ⟨j.1, by omega, hxj⟩
    · rcases Set.mem_iUnion.mp hx_vertices with ⟨v, hxv⟩
      exact hcenter_not_vertex v (by simpa using hxv)
    · rcases Set.mem_iUnion.mp hx_centers with ⟨y, hxy⟩
      by_cases hy : y = x
      · simp [hy] at hxy
      · rw [if_neg hy] at hxy
        have : x.1 = y.1 := by simpa using hxy
        exact hy (Subtype.ext this.symm)
  have hopen : IsOpen forbiddenᶜ := hforbidden_closed.isOpen_compl
  rcases Metric.isOpen_iff.mp hopen x.1 hx_not_forbidden with
    ⟨delta, hdelta, hball_forbidden⟩
  rcases OrdinaryCrossingLocalBranchDataExistsBelow
      (D.edgeArc firstEdge) x.1 hx_first with
    ⟨epsilonFirst, hepsilonFirst, hfirst⟩
  rcases OrdinaryCrossingLocalBranchDataExistsBelow
      (D.edgeArc secondEdge) x.1 hx_second with
    ⟨epsilonSecond, hepsilonSecond, hsecond⟩
  let cap := min upper (min delta (min epsilonFirst epsilonSecond))
  let radius := cap / 2
  have hcap : 0 < cap := by
    dsimp [cap]
    exact lt_min hupper (lt_min hdelta (lt_min hepsilonFirst hepsilonSecond))
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hr_upper : radius < upper := by
    dsimp [radius, cap]
    have := min_le_left upper (min delta (min epsilonFirst epsilonSecond))
    linarith
  have hr_delta : radius < delta := by
    dsimp [radius, cap]
    have := (min_le_right upper (min delta (min epsilonFirst epsilonSecond))).trans
      (min_le_left delta (min epsilonFirst epsilonSecond))
    linarith
  have hr_first : radius < epsilonFirst := by
    dsimp [radius, cap]
    have := (min_le_right upper (min delta (min epsilonFirst epsilonSecond))).trans
      ((min_le_right delta (min epsilonFirst epsilonSecond)).trans
        (min_le_left epsilonFirst epsilonSecond))
    linarith
  have hr_second : radius < epsilonSecond := by
    dsimp [radius, cap]
    have := (min_le_right upper (min delta (min epsilonFirst epsilonSecond))).trans
      ((min_le_right delta (min epsilonFirst epsilonSecond)).trans
        (min_le_right epsilonFirst epsilonSecond))
    linarith
  rcases hfirst radius hradius hr_first with ⟨firstBranch⟩
  rcases hsecond radius hradius hr_second with ⟨secondBranch⟩
  have hclosed_avoids_forbidden : ∀ ⦃q : E⦄,
      q ∈ Metric.closedBall x.1 radius → q ∉ forbidden := by
    intro q hqclosed hqforbidden
    have hq_ball : q ∈ Metric.ball x.1 delta := by
      rw [Metric.mem_ball]
      have hqdist : dist q x.1 ≤ radius := by
        simpa [Metric.mem_closedBall] using hqclosed
      exact hqdist.trans_lt hr_delta
    exact hball_forbidden hq_ball hqforbidden
  have hno_vertex :
      ∀ v : V, D.vertexPlacement v ∉ Metric.closedBall x.1 radius := by
    intro v hv
    have hv_forbidden : D.vertexPlacement v ∈ forbidden := by
      apply Or.inl
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨v, by simp⟩
    exact hclosed_avoids_forbidden hv hv_forbidden
  have hno_center :
      ∀ y : {p // p ∈ D.crossingSet},
        y ≠ x → y.1 ∉ Metric.closedBall x.1 radius := by
    intro y hy hyball
    have hy_forbidden : y.1 ∈ forbidden := by
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨y, by simp [hy]⟩
    exact hclosed_avoids_forbidden hyball hy_forbidden
  have hexact_carrier :
      Metric.closedBall x.1 radius ∩
          (⋃ e : G.edgeFinset, (D.edgeArc e).carrier) =
        Metric.closedBall x.1 radius ∩
          ((D.edgeArc firstEdge).carrier ∪ (D.edgeArc secondEdge).carrier) := by
    ext q
    constructor
    · rintro ⟨hqball, hqcarrier⟩
      rcases Set.mem_iUnion.mp hqcarrier with ⟨e, hqe⟩
      by_cases he_first : e = firstEdge
      · exact ⟨hqball, Or.inl (by simpa [he_first] using hqe)⟩
      · by_cases he_second : e = secondEdge
        · exact ⟨hqball, Or.inr (by simpa [he_second] using hqe)⟩
        · have hq_forbidden : q ∈ forbidden := by
            apply Or.inl
            apply Or.inl
            apply Set.mem_iUnion.mpr
            refine ⟨e, ?_⟩
            rw [if_neg (by exact fun h => h.elim he_first he_second)]
            rw [(D.edgeArc e).carrier_eq] at hqe
            rcases hqe with ⟨j, hj, hqj⟩
            exact Set.mem_iUnion.mpr ⟨⟨j, by omega⟩, hqj⟩
          exact (hclosed_avoids_forbidden hqball hq_forbidden).elim
    · rintro ⟨hqball, hqfirst | hqsecond⟩
      · exact ⟨hqball, Set.mem_iUnion.mpr ⟨firstEdge, hqfirst⟩⟩
      · exact ⟨hqball, Set.mem_iUnion.mpr ⟨secondEdge, hqsecond⟩⟩
  have hpair : ∀ ⦃q : E⦄,
      q ∈ Metric.closedBall x.1 radius →
        q ∈ (D.edgeArc firstEdge).relativeInterior →
          q ∈ (D.edgeArc secondEdge).relativeInterior → q = x.1 := by
    intro q hqball hqfirst hqsecond
    have hqcross : q ∈ D.crossingSet :=
      (D.crossingSet_spec q).2
        ⟨firstEdge, secondEdge, hedges_ne, hqfirst, hqsecond⟩
    let y : {p // p ∈ D.crossingSet} := ⟨q, hqcross⟩
    by_contra hqx
    have hy_ne : y ≠ x := by
      intro h
      exact hqx (congrArg Subtype.val h)
    exact hno_center y hy_ne hqball
  have hlocal_index : ∀ (gamma : PolygonalArc) (branch :
      OrdinaryCrossingLocalBranchData gamma x.1 radius)
      (i : ℕ) (hi : i + 1 < gamma.vertices.length),
      x.1 ∈ segment ℝ gamma.vertices[i] gamma.vertices[i + 1] →
        i = branch.beforeIndex ∨ i = branch.afterIndex := by
    intro gamma branch i hi hxi
    rcases branch.center_case with hcenter | hcenter
    · rcases hcenter with ⟨hafter, hxopen⟩
      let beforeVertex := gamma.vertices[branch.beforeIndex]'
        (Nat.lt_of_succ_lt branch.beforeIndex_valid)
      let afterVertex := gamma.vertices[branch.beforeIndex + 1]'
        branch.beforeIndex_valid
      change x.1 ∈ openSegment ℝ beforeVertex afterVertex at hxopen
      have hvertices_ne : beforeVertex ≠ afterVertex := by
        intro h
        have hidx := (gamma.simple_vertices.getElem_inj_iff
          (i := branch.beforeIndex) (j := branch.beforeIndex + 1)
          (hi := Nat.lt_of_succ_lt branch.beforeIndex_valid)
          (hj := branch.beforeIndex_valid)).1 h
        omega
      have hxrecorded := openSegment_subset_segment ℝ _ _ hxopen
      by_cases hieq : i = branch.beforeIndex
      · exact Or.inl hieq
      have hxinter := Set.mem_inter hxrecorded hxi
      rcases lt_or_gt_of_ne (Ne.symm hieq) with hlt | hgt
      · have hinter := gamma.segment_intersections branch.beforeIndex_valid hi hlt
        rw [hinter] at hxinter
        by_cases hadj : i = branch.beforeIndex + 1
        · rw [if_pos hadj] at hxinter
          have hxendpoint : x.1 = afterVertex := by
            simpa [hadj] using hxinter
          have hright : afterVertex ∈ openSegment ℝ beforeVertex afterVertex := by
            simpa [hxendpoint] using hxopen
          rw [right_mem_openSegment_iff] at hright
          exact (hvertices_ne hright).elim
        · rw [if_neg hadj] at hxinter
          exact hxinter.elim
      · have hinter := gamma.segment_intersections hi branch.beforeIndex_valid hgt
        have hxinter' := Set.mem_inter hxi hxrecorded
        rw [hinter] at hxinter'
        by_cases hadj : branch.beforeIndex = i + 1
        · rw [if_pos hadj] at hxinter'
          have hxendpoint : x.1 = beforeVertex := by
            simpa [beforeVertex, hadj] using hxinter'
          have hleft : beforeVertex ∈ openSegment ℝ beforeVertex afterVertex := by
            simpa [hxendpoint] using hxopen
          rw [left_mem_openSegment_iff] at hleft
          exact (hvertices_ne hleft).elim
        · rw [if_neg hadj] at hxinter'
          exact hxinter'.elim
    · rcases hcenter with ⟨hafter, hxvertex⟩
      by_cases hi_before : i = branch.beforeIndex
      · exact Or.inl hi_before
      by_cases hi_after : i = branch.afterIndex
      · exact Or.inr hi_after
      have hk : branch.afterIndex < gamma.vertices.length :=
        Nat.lt_trans (Nat.lt_succ_self _) branch.afterIndex_valid
      have havoid := PolygonalArcVertexAvoidsNonincidentSegment gamma
        hk hi (by exact Ne.symm hi_after) (by
          intro heq
          apply hi_before
          apply Nat.succ.inj
          exact heq.symm.trans hafter)
      exact (havoid (by simpa [← hxvertex] using hxi)).elim
  rcases D.transverse_intersections hedges_ne hx_first hx_second with
    ⟨firstTransverseIndex, secondTransverseIndex,
      hfirstTransverse, hsecondTransverse, hxfirstSegment,
      hxsecondSegment, htransverse⟩
  have hfirst_local := hlocal_index (D.edgeArc firstEdge) firstBranch
    firstTransverseIndex hfirstTransverse hxfirstSegment
  have hsecond_local := hlocal_index (D.edgeArc secondEdge) secondBranch
    secondTransverseIndex hsecondTransverse hxsecondSegment
  have hno_shared :
      ¬ ∃ i j : ℕ,
        ∃ (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
          (hj : j + 1 < (D.edgeArc secondEdge).vertices.length),
            (i = firstBranch.beforeIndex ∨ i = firstBranch.afterIndex) ∧
              (j = secondBranch.beforeIndex ∨ j = secondBranch.afterIndex) ∧
                ∃ p q : E, p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (D.edgeArc firstEdge).vertices[i]
                        (D.edgeArc firstEdge).vertices[i + 1] ∩
                      segment ℝ (D.edgeArc secondEdge).vertices[j]
                        (D.edgeArc secondEdge).vertices[j + 1] := by
    intro h
    apply D.no_shared_nondegenerate_subarc hedges_ne
    rcases h with ⟨i, j, hi, hj, _hilocal, _hjlocal, p, q, hpq, hsub⟩
    exact ⟨i, j, hi, hj, p, q, hpq, hsub⟩
  have hgate_relative : ∀ (e : G.edgeFinset)
      (branch : OrdinaryCrossingLocalBranchData (D.edgeArc e) x.1 radius)
      (gate : E),
      (gate = branch.beforeGate ∨ gate = branch.afterGate) →
        gate ∈ (D.edgeArc e).relativeInterior := by
    intro e branch gate hgate
    have hgate_sphere : gate ∈ Metric.sphere x.1 radius := by
      rcases hgate with rfl | rfl
      · exact branch.beforeGate_on_sphere
      · exact branch.afterGate_on_sphere
    have hgate_carrier : gate ∈ (D.edgeArc e).carrier := by
      have hmem : gate ∈ Metric.sphere x.1 radius ∩ (D.edgeArc e).carrier := by
        rw [branch.sphere_carrier_eq]
        rcases hgate with rfl | rfl <;> simp
      exact hmem.2
    rw [(D.edgeArc e).relativeInterior_eq]
    refine ⟨hgate_carrier, ?_⟩
    rcases D.edgeArc_endpoints e with ⟨u, v, _huv, _he, hends⟩
    have hgate_closed : gate ∈ Metric.closedBall x.1 radius :=
      Metric.sphere_subset_closedBall hgate_sphere
    rcases hends with hends | hends
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hno_vertex u (by rw [← hends.1, ← h]; exact hgate_closed),
        fun h => hno_vertex v (by rw [← hends.2, ← h]; exact hgate_closed)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hno_vertex v (by rw [← hends.1, ← h]; exact hgate_closed),
        fun h => hno_vertex u (by rw [← hends.2, ← h]; exact hgate_closed)⟩
  have hcross_gate : ∀
      (firstGate secondGate : E),
      (firstGate = firstBranch.beforeGate ∨
        firstGate = firstBranch.afterGate) →
      (secondGate = secondBranch.beforeGate ∨
        secondGate = secondBranch.afterGate) →
      firstGate ≠ secondGate := by
    intro firstGate secondGate hfirstGate hsecondGate heq
    have hfirstSphere : firstGate ∈ Metric.sphere x.1 radius := by
      rcases hfirstGate with rfl | rfl
      · exact firstBranch.beforeGate_on_sphere
      · exact firstBranch.afterGate_on_sphere
    have hclosed : firstGate ∈ Metric.closedBall x.1 radius :=
      Metric.sphere_subset_closedBall hfirstSphere
    have hfirstRel := hgate_relative firstEdge firstBranch firstGate hfirstGate
    have hsecondRel := hgate_relative secondEdge secondBranch secondGate hsecondGate
    have hcenter : firstGate = x.1 :=
      hpair hclosed hfirstRel (heq ▸ hsecondRel)
    have hsphere_dist : dist firstGate x.1 = radius := by
      simpa [Metric.mem_sphere] using hfirstSphere
    rw [hcenter, dist_self] at hsphere_dist
    linarith
  refine ⟨{
    firstEdge := firstEdge
    secondEdge := secondEdge
    edges_ne := hedges_ne
    center_first := hx_first
    center_second := hx_second
    owner_labels := howner
    radius := radius
    firstBranch := firstBranch
    secondBranch := secondBranch
    no_vertex_in_closedBall := hno_vertex
    no_other_crossing_in_closedBall := hno_center
    exact_local_drawing_carrier := hexact_carrier
    pair_meets_only_at_center := hpair
    firstTransverseIndex := firstTransverseIndex
    secondTransverseIndex := secondTransverseIndex
    firstTransverseIndex_valid := hfirstTransverse
    secondTransverseIndex_valid := hsecondTransverse
    firstTransverseIndex_local := hfirst_local
    secondTransverseIndex_local := hsecond_local
    some_germs_transverse := htransverse
    local_germs_share_no_nondegenerate_subarc := hno_shared
    first_before_ne_second_before := hcross_gate _ _ (Or.inl rfl) (Or.inl rfl)
    first_before_ne_second_after := hcross_gate _ _ (Or.inl rfl) (Or.inr rfl)
    first_after_ne_second_before := hcross_gate _ _ (Or.inr rfl) (Or.inl rfl)
    first_after_ne_second_after := hcross_gate _ _ (Or.inr rfl) (Or.inr rfl) },
    hr_upper⟩
