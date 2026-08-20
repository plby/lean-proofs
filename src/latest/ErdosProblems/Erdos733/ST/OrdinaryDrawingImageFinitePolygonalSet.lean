import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcFinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryDrawingImageFinitePolygonalSet]
lemma OrdinaryDrawingImageFinitePolygonalSet {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) :
    ∃ K : FinitePolygonalSet, K.carrier = OrdinaryDrawingImage G D := by
-- BODY
  classical
  have edge_arc_finite :
      ∀ e : G.edgeFinset,
        ∃ K : FinitePolygonalSet, K.carrier = (D.edgeArc e).carrier := by
    intro e
    exact PolygonalArcFinitePolygonalSet (D.edgeArc e)
  let edgeSetPresentation : G.edgeFinset → FinitePolygonalSet :=
    fun e => Classical.choose (edge_arc_finite e)
  have edgeSetPresentation_carrier :
      ∀ e : G.edgeFinset,
        (edgeSetPresentation e).carrier = (D.edgeArc e).carrier := by
    intro e
    exact Classical.choose_spec (edge_arc_finite e)
  have arc_source_mem_carrier :
      ∀ Γ : PolygonalArc, Γ.source ∈ Γ.carrier := by
    intro Γ
    rw [Γ.carrier_eq]
    have hseg : 0 + 1 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    refine ⟨0, hseg, ?_⟩
    have h0 : 0 < Γ.vertices.length := by omega
    have hsource : Γ.vertices[0]'h0 = Γ.source := by
      have hhead := Γ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem h0] at hhead
      exact Option.some.inj hhead
    rw [← hsource]
    exact left_mem_segment ℝ (Γ.vertices[0]'h0) (Γ.vertices[0 + 1]'hseg)
  have arc_target_mem_carrier :
      ∀ Γ : PolygonalArc, Γ.target ∈ Γ.carrier := by
    intro Γ
    rw [Γ.carrier_eq]
    let i : ℕ := Γ.vertices.length - 2
    have hi : i + 1 < Γ.vertices.length := by
      dsimp [i]
      have hlen := Γ.length_ge_two
      omega
    refine ⟨i, hi, ?_⟩
    have hlast_lt : Γ.vertices.length - 1 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    have htarget : Γ.vertices[Γ.vertices.length - 1]'hlast_lt = Γ.target := by
      have hlast := Γ.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlast
      rw [List.getElem?_eq_getElem hlast_lt] at hlast
      exact Option.some.inj hlast
    have hi_eq : i + 1 = Γ.vertices.length - 1 := by
      dsimp [i]
      have hlen := Γ.length_ge_two
      omega
    rw [← htarget]
    have hright :
        Γ.vertices[i + 1]'hi ∈
          segment ℝ (Γ.vertices[i]'(Nat.lt_of_succ_lt hi))
            (Γ.vertices[i + 1]'hi) :=
      right_mem_segment ℝ (Γ.vertices[i]'(Nat.lt_of_succ_lt hi))
        (Γ.vertices[i + 1]'hi)
    simpa [hi_eq] using hright
  let edgePts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset G.edgeFinset).biUnion
      (fun e =>
        (edgeSetPresentation e).points ∪
          {(D.edgeArc e).source, (D.edgeArc e).target})
  let vertexPts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset V).image D.vertexPlacement
  let pts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    edgePts ∪ vertexPts ∪ D.crossingSet
  let segs : Finset
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset G.edgeFinset).biUnion
      (fun e => (edgeSetPresentation e).segments)
  have point_mem_pts_of_presentation_point :
      ∀ {e : G.edgeFinset} {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ (edgeSetPresentation e).points → p ∈ pts := by
    intro e p hp
    dsimp [pts, edgePts]
    rw [Finset.mem_union, Finset.mem_union]
    left
    left
    rw [Finset.mem_biUnion]
    refine ⟨e, by simp, ?_⟩
    exact Finset.mem_union.mpr (Or.inl hp)
  have source_mem_pts :
      ∀ e : G.edgeFinset, (D.edgeArc e).source ∈ pts := by
    intro e
    dsimp [pts, edgePts]
    rw [Finset.mem_union, Finset.mem_union]
    left
    left
    rw [Finset.mem_biUnion]
    refine ⟨e, by simp, ?_⟩
    exact Finset.mem_union.mpr (Or.inr (by simp))
  have target_mem_pts :
      ∀ e : G.edgeFinset, (D.edgeArc e).target ∈ pts := by
    intro e
    dsimp [pts, edgePts]
    rw [Finset.mem_union, Finset.mem_union]
    left
    left
    rw [Finset.mem_biUnion]
    refine ⟨e, by simp, ?_⟩
    exact Finset.mem_union.mpr (Or.inr (by simp))
  have vertex_mem_pts :
      ∀ v : V, D.vertexPlacement v ∈ pts := by
    intro v
    dsimp [pts, vertexPts]
    rw [Finset.mem_union, Finset.mem_union]
    left
    right
    exact Finset.mem_image.mpr ⟨v, by simp, rfl⟩
  have crossing_mem_pts :
      ∀ {p : EuclideanSpace ℝ (Fin 2)}, p ∈ D.crossingSet → p ∈ pts := by
    intro p hp
    dsimp [pts]
    rw [Finset.mem_union]
    exact Or.inr hp
  have seg_mem_segs_of_presentation :
      ∀ {e : G.edgeFinset}
        {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)},
        s ∈ (edgeSetPresentation e).segments → s ∈ segs := by
    intro e s hs
    dsimp [segs]
    rw [Finset.mem_biUnion]
    exact ⟨e, by simp, hs⟩
  have presentation_of_seg_mem_segs :
      ∀ {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)},
        s ∈ segs →
          ∃ e : G.edgeFinset, s ∈ (edgeSetPresentation e).segments := by
    intro s hs
    dsimp [segs] at hs
    rw [Finset.mem_biUnion] at hs
    rcases hs with ⟨e, _he, hsK⟩
    exact ⟨e, hsK⟩
  have presentation_point_mem_arc :
      ∀ {e : G.edgeFinset} {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ (edgeSetPresentation e).points → p ∈ (D.edgeArc e).carrier := by
    intro e p hp
    have hpK : p ∈ (edgeSetPresentation e).carrier := by
      rw [(edgeSetPresentation e).carrier_eq]
      exact Or.inl hp
    simpa [edgeSetPresentation_carrier e] using hpK
  have presentation_segment_point_mem_arc :
      ∀ {e : G.edgeFinset}
        {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
        {p : EuclideanSpace ℝ (Fin 2)},
        s ∈ (edgeSetPresentation e).segments →
          p ∈ segment ℝ s.1 s.2 → p ∈ (D.edgeArc e).carrier := by
    intro e s p hs hpseg
    have hpK : p ∈ (edgeSetPresentation e).carrier := by
      rw [(edgeSetPresentation e).carrier_eq]
      right
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hpseg⟩
    simpa [edgeSetPresentation_carrier e] using hpK
  have rel_of_carrier_not_endpoint :
      ∀ {Γ : PolygonalArc} {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ Γ.carrier → ¬ (p = Γ.source ∨ p = Γ.target) →
          p ∈ Γ.relativeInterior := by
    intro Γ p hp hnot
    rw [Γ.relativeInterior_eq]
    refine ⟨hp, ?_⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hnot
  have arc_point_mem_image :
      ∀ {e : G.edgeFinset} {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ (D.edgeArc e).carrier → p ∈ OrdinaryDrawingImage G D := by
    intro e p hp
    rw [OrdinaryDrawingImage]
    right
    exact Set.mem_iUnion.mpr ⟨e, hp⟩
  refine ⟨
    { carrier := OrdinaryDrawingImage G D
      points := pts
      segments := segs
      segment_nondegenerate := ?_
      segment_endpoints_listed := ?_
      segment_intersections_listed := ?_
      carrier_eq := ?_ },
    rfl⟩
  · intro s hs
    rcases presentation_of_seg_mem_segs hs with ⟨e, hsK⟩
    exact (edgeSetPresentation e).segment_nondegenerate s hsK
  · intro s hs
    rcases presentation_of_seg_mem_segs hs with ⟨e, hsK⟩
    have hendpoints := (edgeSetPresentation e).segment_endpoints_listed s hsK
    exact ⟨point_mem_pts_of_presentation_point hendpoints.1,
      point_mem_pts_of_presentation_point hendpoints.2⟩
  · intro s t hs ht hst p hps hpt
    rcases presentation_of_seg_mem_segs hs with ⟨e, hsK⟩
    rcases presentation_of_seg_mem_segs ht with ⟨f, htK⟩
    by_cases hef : e = f
    · subst f
      exact point_mem_pts_of_presentation_point
        ((edgeSetPresentation e).segment_intersections_listed
          s t hsK htK hst p hps hpt)
    · have hp_e_carrier : p ∈ (D.edgeArc e).carrier :=
        presentation_segment_point_mem_arc hsK hps
      have hp_f_carrier : p ∈ (D.edgeArc f).carrier :=
        presentation_segment_point_mem_arc htK hpt
      by_cases hpe :
          p = (D.edgeArc e).source ∨ p = (D.edgeArc e).target
      · rcases hpe with hsource | htarget
        · simpa [hsource] using source_mem_pts e
        · simpa [htarget] using target_mem_pts e
      · by_cases hpf :
          p = (D.edgeArc f).source ∨ p = (D.edgeArc f).target
        · rcases hpf with hsource | htarget
          · simpa [hsource] using source_mem_pts f
          · simpa [htarget] using target_mem_pts f
        · have hp_e_rel : p ∈ (D.edgeArc e).relativeInterior :=
            rel_of_carrier_not_endpoint hp_e_carrier hpe
          have hp_f_rel : p ∈ (D.edgeArc f).relativeInterior :=
            rel_of_carrier_not_endpoint hp_f_carrier hpf
          exact crossing_mem_pts
            ((D.crossingSet_spec p).2 ⟨e, f, hef, hp_e_rel, hp_f_rel⟩)
  · ext p
    constructor
    · intro hp
      rw [OrdinaryDrawingImage] at hp
      rcases hp with hp_vertex | hp_edge
      · rcases hp_vertex with ⟨v, rfl⟩
        exact Or.inl (vertex_mem_pts v)
      · rw [Set.mem_iUnion] at hp_edge
        rcases hp_edge with ⟨e, hp_arc⟩
        have hpK : p ∈ (edgeSetPresentation e).carrier := by
          simpa [edgeSetPresentation_carrier e] using hp_arc
        have hpK_parts :
            p ∈ ((edgeSetPresentation e).points :
                Set (EuclideanSpace ℝ (Fin 2))) ∪
              ⋃ s : {s // s ∈ (edgeSetPresentation e).segments},
                segment ℝ s.1.1 s.1.2 := by
          simpa [(edgeSetPresentation e).carrier_eq] using hpK
        rcases hpK_parts with hp_point | hp_segment
        · exact Or.inl (point_mem_pts_of_presentation_point hp_point)
        · right
          rcases Set.mem_iUnion.mp hp_segment with ⟨s, hps⟩
          exact Set.mem_iUnion.mpr
            ⟨⟨s.1, seg_mem_segs_of_presentation s.2⟩, by simpa using hps⟩
    · intro hp
      rcases hp with hp_point | hp_segment
      · have hp_point_fin : p ∈ pts := by
          simpa using hp_point
        dsimp [pts, edgePts, vertexPts] at hp_point_fin
        rw [Finset.mem_union, Finset.mem_union] at hp_point_fin
        rcases hp_point_fin with hp_edge_or_vertex | hp_crossing
        · rcases hp_edge_or_vertex with hp_edge | hp_vertex
          · rw [Finset.mem_biUnion] at hp_edge
            rcases hp_edge with ⟨e, _he, hp_edge_piece⟩
            rcases Finset.mem_union.mp hp_edge_piece with hpK_point | hp_endpoint
            · exact arc_point_mem_image (presentation_point_mem_arc hpK_point)
            · have hp_endpoint' :
                  p = (D.edgeArc e).source ∨ p = (D.edgeArc e).target := by
                simpa using hp_endpoint
              rcases hp_endpoint' with hsource | htarget
              · exact arc_point_mem_image
                  (e := e) (by simpa [hsource] using arc_source_mem_carrier (D.edgeArc e))
              · exact arc_point_mem_image
                  (e := e) (by simpa [htarget] using arc_target_mem_carrier (D.edgeArc e))
          · rcases Finset.mem_image.mp hp_vertex with ⟨v, _hv, rfl⟩
            rw [OrdinaryDrawingImage]
            exact Or.inl ⟨v, rfl⟩
        · have hp_crossing_spec := (D.crossingSet_spec p).1 hp_crossing
          rcases hp_crossing_spec with ⟨e, _f, _hef, hp_e_rel, _hp_f_rel⟩
          have hp_e_carrier : p ∈ (D.edgeArc e).carrier := by
            rw [(D.edgeArc e).relativeInterior_eq] at hp_e_rel
            exact hp_e_rel.1
          exact arc_point_mem_image hp_e_carrier
      · rcases Set.mem_iUnion.mp hp_segment with ⟨s, hps⟩
        rcases presentation_of_seg_mem_segs s.2 with ⟨e, hsK⟩
        exact arc_point_mem_image
          (presentation_segment_point_mem_arc hsK (by simpa using hps))
