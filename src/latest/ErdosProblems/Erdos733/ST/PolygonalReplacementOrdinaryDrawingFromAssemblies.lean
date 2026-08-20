import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalReplacementEdgeAssemblyData


open Classical
noncomputable section

private lemma nonparallel_of_endpoint_orientations
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a₀ a₁ b₀ b₁ A₀ A₁ B₀ B₁ : E}
    (ha : (a₀ = A₀ ∧ a₁ = A₁) ∨ (a₀ = A₁ ∧ a₁ = A₀))
    (hb : (b₀ = B₀ ∧ b₁ = B₁) ∨ (b₀ = B₁ ∧ b₁ = B₀))
    (hAB : ¬ ∃ c : ℝ, B₁ - B₀ = c • (A₁ - A₀)) :
    ¬ ∃ c : ℝ, b₁ - b₀ = c • (a₁ - a₀) := by
  rintro ⟨c, hc⟩
  rcases ha with ⟨ha₀, ha₁⟩ | ⟨ha₀, ha₁⟩ <;>
    rcases hb with ⟨hb₀, hb₁⟩ | ⟨hb₀, hb₁⟩
  · rw [ha₀, ha₁, hb₀, hb₁] at hc
    exact hAB ⟨c, hc⟩
  · rw [ha₀, ha₁, hb₀, hb₁] at hc
    apply hAB
    refine ⟨-c, ?_⟩
    calc
      B₁ - B₀ = -(B₀ - B₁) := by module
      _ = -(c • (A₁ - A₀)) := congrArg Neg.neg hc
      _ = (-c) • (A₁ - A₀) := by module
  · rw [ha₀, ha₁, hb₀, hb₁] at hc
    apply hAB
    refine ⟨-c, ?_⟩
    calc
      B₁ - B₀ = c • (A₀ - A₁) := hc
      _ = (-c) • (A₁ - A₀) := by module
  · rw [ha₀, ha₁, hb₀, hb₁] at hc
    apply hAB
    refine ⟨c, ?_⟩
    calc
      B₁ - B₀ = -(B₀ - B₁) := by module
      _ = -(c • (A₀ - A₁)) := congrArg Neg.neg hc
      _ = c • (A₁ - A₀) := by module

-- [TABLET NODE: PolygonalReplacementOrdinaryDrawingFromAssemblies]
lemma PolygonalReplacementOrdinaryDrawingFromAssemblies {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks)
    (localDiskFillings :
      PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains)
    (edgeAssemblies :
      PolygonalReplacementEdgeAssemblyData G D controlDisks tubeChains
        localDiskFillings) :
    ∃ D' : OrdinaryPolygonalDrawing G,
      D'.vertexPlacement = D.vertexPlacement ∧
        D'.edgeArc = edgeAssemblies.edgeArc ∧
          ∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            p ∈ D'.crossingSet →
              ∃ (x : {q // q ∈ D.intersectionPoints})
                (e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
                e ≠ f ∧
                  p ∈ (localDiskFillings.intersection_chain x e).relativeInterior ∧
                    p ∈ (localDiskFillings.intersection_chain x f).relativeInterior := by
-- BODY
  classical
  let localizedPairSet
      (x : {q // q ∈ D.intersectionPoints})
      (e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}) :
      Set (EuclideanSpace ℝ (Fin 2)) :=
    (localDiskFillings.intersection_chain x e).relativeInterior ∩
      (localDiskFillings.intersection_chain x f).relativeInterior
  have localizedPairSet_finite :
      ∀ (x : {q // q ∈ D.intersectionPoints})
        (e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        e ≠ f → (localizedPairSet x e f).Finite := by
    intro x e f hef
    have hsub : (localizedPairSet x e f).Subsingleton := by
      intro p hp q hq
      exact
        localDiskFillings.intersection_chains_pairwise_at_most_one x
          hef hp.1 hp.2 hq.1 hq.2
    exact hsub.finite
  let localizedPairFinset
      (x : {q // q ∈ D.intersectionPoints})
      (e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}) :
      Finset (EuclideanSpace ℝ (Fin 2)) :=
    if hef : e = f then ∅ else (localizedPairSet_finite x e f hef).toFinset
  let crossingSet : Finset (EuclideanSpace ℝ (Fin 2)) :=
    D.intersectionPoints.attach.biUnion (fun x =>
      (Finset.univ :
        Finset {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}).biUnion
          (fun e =>
            (Finset.univ :
              Finset {f : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior f}).biUnion
                (fun f => localizedPairFinset x e f)))
  have crossingSet_mem_iff :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ crossingSet ↔
          ∃ e₁ e₂ : G.edgeFinset,
            e₁ ≠ e₂ ∧
              p ∈ (edgeAssemblies.edgeArc e₁).relativeInterior ∧
                p ∈ (edgeAssemblies.edgeArc e₂).relativeInterior := by
    intro p
    constructor
    · intro hp
      simp only [crossingSet, Finset.mem_biUnion, Finset.mem_attach,
        true_and, Finset.mem_univ] at hp
      rcases hp with ⟨x, e, f, hpair⟩
      by_cases hef : e = f
      · simp [localizedPairFinset, hef] at hpair
      · have hpSet : p ∈ localizedPairSet x e f := by
          exact (Set.Finite.mem_toFinset
            (localizedPairSet_finite x e f hef)).mp
              (by simpa [localizedPairFinset, hef] using hpair)
        refine ⟨e.1, f.1, ?_, ?_, ?_⟩
        · intro hval
          exact hef (Subtype.ext hval)
        · exact edgeAssemblies.intersection_chain_relativeInterior_subset_edgeArc x e hpSet.1
        · exact edgeAssemblies.intersection_chain_relativeInterior_subset_edgeArc x f hpSet.2
    · intro hp
      rcases hp with ⟨e₁, e₂, he₁₂, hp₁, hp₂⟩
      rcases edgeAssemblies.distinct_edge_relativeInteriors_localized
          he₁₂ hp₁ hp₂ with ⟨x, hxe₁, hxe₂, hp₁x, hp₂x⟩
      simp only [crossingSet, Finset.mem_biUnion, Finset.mem_attach,
        true_and, Finset.mem_univ]
      refine ⟨x, ⟨e₁, hxe₁⟩, ⟨e₂, hxe₂⟩, ?_⟩
      have hsub_ne : (⟨e₁, hxe₁⟩ :
          {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}) ≠
          ⟨e₂, hxe₂⟩ := by
        intro h
        exact he₁₂ (congrArg Subtype.val h)
      have hpSet :
          p ∈ localizedPairSet x ⟨e₁, hxe₁⟩ ⟨e₂, hxe₂⟩ :=
        ⟨hp₁x, hp₂x⟩
      have hpFin :
          p ∈ (localizedPairSet_finite x ⟨e₁, hxe₁⟩ ⟨e₂, hxe₂⟩
            hsub_ne).toFinset :=
          (Set.Finite.mem_toFinset
            (localizedPairSet_finite x ⟨e₁, hxe₁⟩ ⟨e₂, hxe₂⟩
              hsub_ne)).mpr hpSet
      simpa [localizedPairFinset, hsub_ne] using hpFin
  refine ⟨
    { vertexPlacement := D.vertexPlacement
      vertexPlacement_injective := D.vertexPlacement_injective
      edgeArc := edgeAssemblies.edgeArc
      edgeArc_endpoints := ?_
      crossingSet := crossingSet
      no_vertex_in_edge_interior := ?_
      no_three_edge_interiors_meet := ?_
      transverse_intersections := ?_
      no_shared_nondegenerate_subarc := ?_
      crossingSet_spec := ?_
      adjacentEdgeCrossingCount :=
        (crossingSet.filter (fun p =>
          ∃ e₁ e₂ : G.edgeFinset,
            e₁ ≠ e₂ ∧
              (∃ v : V, v ∈ e₁.1 ∧ v ∈ e₂.1) ∧
                p ∈ (edgeAssemblies.edgeArc e₁).relativeInterior ∧
                  p ∈ (edgeAssemblies.edgeArc e₂).relativeInterior)).card
      adjacentEdgeCrossingCount_eq := rfl }, ?_⟩
  · intro e
    rcases D.edgeArc_endpoints e with ⟨u, v, huv, heq, hend⟩
    refine ⟨u, v, huv, heq, ?_⟩
    rcases hend with h | h
    · exact Or.inl ⟨by simpa [h.1] using edgeAssemblies.edgeArc_source e,
        by simpa [h.2] using edgeAssemblies.edgeArc_target e⟩
    · exact Or.inr ⟨by simpa [h.1] using edgeAssemblies.edgeArc_source e,
        by simpa [h.2] using edgeAssemblies.edgeArc_target e⟩
  · intro v e hp
    rcases edgeAssemblies.edgeArc_relativeInterior_localized hp with
      hvertex | htube | hintersection
    · rcases hvertex with ⟨w, hwe, hpCarrier⟩
      have hpClosedW :
          D.vertexPlacement v ∈
            Metric.closedBall (D.vertexPlacement w)
              (controlDisks.vertexRadius w) :=
        localDiskFillings.vertex_spoke_carrier_subset_closedBall
          w ⟨e, hwe⟩ hpCarrier
      by_cases hvw : v = w
      · subst w
        have hpEdge := hp
        rw [edgeAssemblies.edgeArc_relativeInterior_eq e] at hpEdge
        have hv_endpoint :
            D.vertexPlacement v = D.edgeSource e ∨
              D.vertexPlacement v = D.edgeTarget e := by
          rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hend⟩
          have hvab : v = a ∨ v = b := by
            have hv_mem : v ∈ (Sym2.mk a b : Sym2 V) := by
              simpa [heq] using hwe
            simpa using hv_mem
          rcases hend with hend | hend
          · rcases hvab with rfl | rfl
            · exact Or.inl hend.1.symm
            · exact Or.inr hend.2.symm
          · rcases hvab with rfl | rfl
            · exact Or.inr hend.2.symm
            · exact Or.inl hend.1.symm
        rcases hv_endpoint with hsrc | htgt
        · exact hpEdge.2.1 hsrc
        · exact hpEdge.2.2 htgt
      · have hpClosedV :
            D.vertexPlacement v ∈
              Metric.closedBall (D.vertexPlacement v)
                (controlDisks.vertexRadius v) := by
          simp [Metric.mem_closedBall, le_of_lt (controlDisks.vertexRadius_pos v)]
        exact
          (Set.disjoint_left.mp
            (controlDisks.vertex_vertex_disjoint hvw)
            hpClosedV) hpClosedW
    · rcases htube with ⟨i, _hiowner, hpCarrier⟩
      have hpClosedV :
          D.vertexPlacement v ∈
            Metric.closedBall (D.vertexPlacement v)
              (controlDisks.vertexRadius v) := by
        simp [Metric.mem_closedBall, le_of_lt (controlDisks.vertexRadius_pos v)]
      rcases tubeChains.chain_carrier_meets_vertex_closedBall_only_endpoint
          i v (D.vertexPlacement v) hpCarrier hpClosedV with
        hsrc | htgt
      · have hcenterSphere :
            D.vertexPlacement v ∈
              Metric.sphere (D.vertexPlacement v)
                (controlDisks.vertexRadius v) := by
          simpa [hsrc.1] using hsrc.2
        have hzero : (0 : ℝ) = controlDisks.vertexRadius v := by
          simpa [Metric.mem_sphere] using hcenterSphere
        exact (ne_of_gt (controlDisks.vertexRadius_pos v)) hzero.symm
      · have hcenterSphere :
            D.vertexPlacement v ∈
              Metric.sphere (D.vertexPlacement v)
                (controlDisks.vertexRadius v) := by
          simpa [htgt.1] using htgt.2
        have hzero : (0 : ℝ) = controlDisks.vertexRadius v := by
          simpa [Metric.mem_sphere] using hcenterSphere
        exact (ne_of_gt (controlDisks.vertexRadius_pos v)) hzero.symm
    · rcases hintersection with ⟨x, hxe, hpCarrier⟩
      have hpClosedV :
          D.vertexPlacement v ∈
            Metric.closedBall (D.vertexPlacement v)
              (controlDisks.vertexRadius v) := by
        simp [Metric.mem_closedBall, le_of_lt (controlDisks.vertexRadius_pos v)]
      have hpClosedX :
          D.vertexPlacement v ∈
            Metric.closedBall x.1 (controlDisks.intersectionRadius x) :=
        localDiskFillings.intersection_chain_carrier_subset_closedBall
          x ⟨e, hxe⟩ hpCarrier
      exact
        (Set.disjoint_left.mp
          (controlDisks.vertex_intersection_disjoint v x)
          hpClosedV) hpClosedX
  · intro e₁ e₂ e₃ p he₁₂ he₁₃ he₂₃ hp₁ hp₂ hp₃
    rcases edgeAssemblies.distinct_edge_relativeInteriors_localized
        he₁₂ hp₁ hp₂ with ⟨x, hx₁, hx₂, hpx₁, hpx₂⟩
    rcases edgeAssemblies.distinct_edge_relativeInteriors_localized
        he₁₃ hp₁ hp₃ with ⟨y, hy₁, hy₃, hpy₁, hpy₃⟩
    have hxy : x = y := by
      by_contra hxy
      have hpxClosed :
          p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) :=
        Metric.ball_subset_closedBall
          (localDiskFillings.intersection_chain_relativeInterior_subset_ball
            x ⟨e₁, hx₁⟩ hpx₁)
      have hpyClosed :
          p ∈ Metric.closedBall y.1 (controlDisks.intersectionRadius y) :=
        Metric.ball_subset_closedBall
          (localDiskFillings.intersection_chain_relativeInterior_subset_ball
            y ⟨e₁, hy₁⟩ hpy₁)
      exact
        (Set.disjoint_left.mp
          (controlDisks.intersection_intersection_disjoint hxy)
          hpxClosed) hpyClosed
    subst y
    have hb₁₂ :
        (⟨e₁, hx₁⟩ :
          {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}) ≠
          ⟨e₂, hx₂⟩ := by
      intro h
      exact he₁₂ (congrArg Subtype.val h)
    have hb₁₃ :
        (⟨e₁, hx₁⟩ :
          {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}) ≠
          ⟨e₃, hy₃⟩ := by
      intro h
      exact he₁₃ (congrArg Subtype.val h)
    have hb₂₃ :
        (⟨e₂, hx₂⟩ :
          {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}) ≠
          ⟨e₃, hy₃⟩ := by
      intro h
      exact he₂₃ (congrArg Subtype.val h)
    exact
      localDiskFillings.intersection_chains_no_triple_intersections x
        hb₁₂ hb₁₃ hb₂₃ hpx₁ hpx₂ hpy₃
  · intro e₁ e₂ p he₁₂ hp₁ hp₂
    rcases edgeAssemblies.distinct_edge_relativeInteriors_localized
        he₁₂ hp₁ hp₂ with ⟨x, hx₁, hx₂, hpx₁, hpx₂⟩
    let b₁ : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} :=
      ⟨e₁, hx₁⟩
    let b₂ : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} :=
      ⟨e₂, hx₂⟩
    have hb₁₂ : b₁ ≠ b₂ := by
      intro h
      exact he₁₂ (congrArg Subtype.val h)
    rcases localDiskFillings.intersection_chains_transverse_intersections x
        hb₁₂ hpx₁ hpx₂ with
      ⟨m, n, hm, hn, hpm, hpn, hnonparallel⟩
    rcases edgeAssemblies.intersection_chain_segment_lift x b₁ m hm with
      ⟨i, hi, hiorient⟩
    rcases edgeAssemblies.intersection_chain_segment_lift x b₂ n hn with
      ⟨j, hj, hjorient⟩
    refine ⟨i, j, hi, hj, ?_, ?_, ?_⟩
    · rcases hiorient with ⟨hi₀, hi₁⟩ | ⟨hi₀, hi₁⟩
      · simpa [b₁, hi₀, hi₁] using hpm
      · simpa [b₁, hi₀, hi₁, segment_symm] using hpm
    · rcases hjorient with ⟨hj₀, hj₁⟩ | ⟨hj₀, hj₁⟩
      · simpa [b₂, hj₀, hj₁] using hpn
      · simpa [b₂, hj₀, hj₁, segment_symm] using hpn
    · exact
        nonparallel_of_endpoint_orientations hiorient hjorient hnonparallel
  · intro e₁ e₂ he₁₂ hcommon
    rcases hcommon with ⟨i, j, hi, hj, p, q, hpq, hseg_subset⟩
    have hpointAvoidFinset :
        ∀ {p q : EuclideanSpace ℝ (Fin 2)}, p ≠ q →
          ∀ F : Finset (EuclideanSpace ℝ (Fin 2)),
            ∃ x : EuclideanSpace ℝ (Fin 2),
              x ∈ openSegment ℝ p q ∧ x ∉ F := by
      intro p q hpq F
      let f : ℝ → EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap p q
      have hf : Function.Injective f := by
        exact AffineMap.lineMap_injective (k := ℝ) hpq
      let bad : Set ℝ := f ⁻¹' (F : Set (EuclideanSpace ℝ (Fin 2)))
      have hbad_finite : bad.Finite := by
        exact F.finite_toSet.preimage (fun a _ b _ hab => hf hab)
      have hIinf : (Set.Ioo (0 : ℝ) 1).Infinite :=
        Set.Ioo_infinite zero_lt_one
      have hgood : (Set.Ioo (0 : ℝ) 1 \ bad).Infinite :=
        hIinf.diff hbad_finite
      rcases hgood.nonempty with ⟨t, ht⟩
      refine ⟨f t, ?_, ?_⟩
      · exact lineMap_mem_openSegment ℝ p q ht.1
      · intro hxF
        exact ht.2 hxF
    let forbidden : Finset (EuclideanSpace ℝ (Fin 2)) :=
      crossingSet ∪
        {(edgeAssemblies.edgeArc e₁).source,
          (edgeAssemblies.edgeArc e₁).target,
          (edgeAssemblies.edgeArc e₂).source,
          (edgeAssemblies.edgeArc e₂).target}
    rcases hpointAvoidFinset hpq forbidden with
      ⟨x, hx_open, hx_not_forbidden⟩
    have hx_not_crossing : x ∉ crossingSet := by
      intro hxcrossing
      exact hx_not_forbidden (by simp [forbidden, hxcrossing])
    have hx_not_source₁ : x ≠ (edgeAssemblies.edgeArc e₁).source := by
      intro hx
      exact hx_not_forbidden (by simp [forbidden, hx])
    have hx_not_target₁ : x ≠ (edgeAssemblies.edgeArc e₁).target := by
      intro hx
      exact hx_not_forbidden (by simp [forbidden, hx])
    have hx_not_source₂ : x ≠ (edgeAssemblies.edgeArc e₂).source := by
      intro hx
      exact hx_not_forbidden (by simp [forbidden, hx])
    have hx_not_target₂ : x ≠ (edgeAssemblies.edgeArc e₂).target := by
      intro hx
      exact hx_not_forbidden (by simp [forbidden, hx])
    have hx_seg_pq : x ∈ segment ℝ p q :=
      openSegment_subset_segment ℝ p q hx_open
    have hx_edges := hseg_subset hx_seg_pq
    have hx_carrier₁ : x ∈ (edgeAssemblies.edgeArc e₁).carrier := by
      rw [(edgeAssemblies.edgeArc e₁).carrier_eq]
      exact ⟨i, hi, hx_edges.1⟩
    have hx_carrier₂ : x ∈ (edgeAssemblies.edgeArc e₂).carrier := by
      rw [(edgeAssemblies.edgeArc e₂).carrier_eq]
      exact ⟨j, hj, hx_edges.2⟩
    have hx_not_end₁ :
        x ∉ ({(edgeAssemblies.edgeArc e₁).source,
            (edgeAssemblies.edgeArc e₁).target} :
          Set (EuclideanSpace ℝ (Fin 2))) := by
      simp [hx_not_source₁, hx_not_target₁]
    have hx_not_end₂ :
        x ∉ ({(edgeAssemblies.edgeArc e₂).source,
            (edgeAssemblies.edgeArc e₂).target} :
          Set (EuclideanSpace ℝ (Fin 2))) := by
      simp [hx_not_source₂, hx_not_target₂]
    have hx_rel₁ : x ∈ (edgeAssemblies.edgeArc e₁).relativeInterior := by
      rw [(edgeAssemblies.edgeArc e₁).relativeInterior_eq]
      exact ⟨hx_carrier₁, hx_not_end₁⟩
    have hx_rel₂ : x ∈ (edgeAssemblies.edgeArc e₂).relativeInterior := by
      rw [(edgeAssemblies.edgeArc e₂).relativeInterior_eq]
      exact ⟨hx_carrier₂, hx_not_end₂⟩
    have hx_crossing : x ∈ crossingSet :=
      (crossingSet_mem_iff x).mpr ⟨e₁, e₂, he₁₂, hx_rel₁, hx_rel₂⟩
    exact hx_not_crossing hx_crossing
  · exact crossingSet_mem_iff
  · constructor
    · rfl
    · constructor
      · rfl
      · intro p hp
        have hp' := (crossingSet_mem_iff p).mp hp
        rcases hp' with ⟨e₁, e₂, he₁₂, hp₁, hp₂⟩
        rcases edgeAssemblies.distinct_edge_relativeInteriors_localized
            he₁₂ hp₁ hp₂ with ⟨x, hxe₁, hxe₂, hp₁x, hp₂x⟩
        refine ⟨x, ⟨e₁, hxe₁⟩, ⟨e₂, hxe₂⟩, ?_, hp₁x, hp₂x⟩
        intro hsub
        exact he₁₂ (congrArg Subtype.val hsub)
