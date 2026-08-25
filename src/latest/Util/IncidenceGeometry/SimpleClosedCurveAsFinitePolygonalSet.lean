import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.PolygonalArcFinitePolygonalSet

open Classical
noncomputable section

lemma SimpleClosedCurveAsFinitePolygonalSet
    (J : SimpleClosedPolygonalCurve) :
    ∃ K : FinitePolygonalSet, K.carrier = J.carrier := by
  classical
  have edge_arc_finite :
      ∀ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs},
        ∃ K : FinitePolygonalSet, K.carrier = γ.1.carrier := by
    intro γ
    exact PolygonalArcFinitePolygonalSet γ.1
  let edgeSetPresentation :
      {γ : PolygonalArc // γ ∈ J.edgeArcs} → FinitePolygonalSet :=
    fun γ => Classical.choose (edge_arc_finite γ)
  have edgeSetPresentation_carrier :
      ∀ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs},
        (edgeSetPresentation γ).carrier = γ.1.carrier := by
    intro γ
    exact Classical.choose_spec (edge_arc_finite γ)
  have hcarrier :
      J.carrier =
        ⋃ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs},
          (edgeSetPresentation γ).carrier := by
    rw [J.carrier_eq]
    ext p
    constructor
    · intro hp
      rw [Set.mem_iUnion] at hp
      rcases hp with ⟨γ, hpγ⟩
      rw [Set.mem_iUnion]
      exact ⟨γ, by simpa [edgeSetPresentation_carrier γ] using hpγ⟩
    · intro hp
      rw [Set.mem_iUnion] at hp
      rcases hp with ⟨γ, hpγ⟩
      rw [Set.mem_iUnion]
      exact ⟨γ, by simpa [edgeSetPresentation_carrier γ] using hpγ⟩
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
  let pts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset {γ : PolygonalArc // γ ∈ J.edgeArcs}).biUnion
      (fun γ =>
        (edgeSetPresentation γ).points ∪ {γ.1.source, γ.1.target})
  let segs : Finset
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset {γ : PolygonalArc // γ ∈ J.edgeArcs}).biUnion
      (fun γ => (edgeSetPresentation γ).segments)
  have point_mem_pts_of_presentation_point :
      ∀ {γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}}
        {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ (edgeSetPresentation γ).points → p ∈ pts := by
    intro γ p hp
    dsimp [pts]
    rw [Finset.mem_biUnion]
    refine ⟨γ, by simp, ?_⟩
    exact Finset.mem_union.mpr (Or.inl hp)
  have source_mem_pts :
      ∀ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}, γ.1.source ∈ pts := by
    intro γ
    dsimp [pts]
    rw [Finset.mem_biUnion]
    refine ⟨γ, by simp, ?_⟩
    exact Finset.mem_union.mpr (Or.inr (by simp))
  have target_mem_pts :
      ∀ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}, γ.1.target ∈ pts := by
    intro γ
    dsimp [pts]
    rw [Finset.mem_biUnion]
    refine ⟨γ, by simp, ?_⟩
    exact Finset.mem_union.mpr (Or.inr (by simp))
  have seg_mem_segs_of_presentation :
      ∀ {γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}}
        {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)},
        s ∈ (edgeSetPresentation γ).segments → s ∈ segs := by
    intro γ s hs
    dsimp [segs]
    rw [Finset.mem_biUnion]
    exact ⟨γ, by simp, hs⟩
  have presentation_of_seg_mem_segs :
      ∀ {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)},
        s ∈ segs →
          ∃ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs},
            s ∈ (edgeSetPresentation γ).segments := by
    intro s hs
    dsimp [segs] at hs
    rw [Finset.mem_biUnion] at hs
    rcases hs with ⟨γ, _hγ, hsγ⟩
    exact ⟨γ, hsγ⟩
  have presentation_point_mem_arc :
      ∀ {γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}}
        {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ (edgeSetPresentation γ).points → p ∈ γ.1.carrier := by
    intro γ p hp
    have hpK : p ∈ (edgeSetPresentation γ).carrier := by
      rw [(edgeSetPresentation γ).carrier_eq]
      exact Or.inl hp
    simpa [edgeSetPresentation_carrier γ] using hpK
  have presentation_segment_point_mem_arc :
      ∀ {γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}}
        {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
        {p : EuclideanSpace ℝ (Fin 2)},
        s ∈ (edgeSetPresentation γ).segments →
          p ∈ segment ℝ s.1 s.2 → p ∈ γ.1.carrier := by
    intro γ s p hs hpseg
    have hpK : p ∈ (edgeSetPresentation γ).carrier := by
      rw [(edgeSetPresentation γ).carrier_eq]
      right
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hpseg⟩
    simpa [edgeSetPresentation_carrier γ] using hpK
  have arc_point_mem_J :
      ∀ {γ : {γ : PolygonalArc // γ ∈ J.edgeArcs}}
        {p : EuclideanSpace ℝ (Fin 2)}, p ∈ γ.1.carrier → p ∈ J.carrier := by
    intro γ p hp
    rw [hcarrier]
    have hpK : p ∈ (edgeSetPresentation γ).carrier := by
      simpa [edgeSetPresentation_carrier γ] using hp
    exact Set.mem_iUnion.mpr ⟨γ, hpK⟩
  refine ⟨
    { carrier := J.carrier
      points := pts
      segments := segs
      segment_nondegenerate := ?_
      segment_endpoints_listed := ?_
      segment_intersections_listed := ?_
      carrier_eq := ?_ },
    rfl⟩
  · intro s hs
    rcases presentation_of_seg_mem_segs hs with ⟨γ, hsγ⟩
    exact (edgeSetPresentation γ).segment_nondegenerate s hsγ
  · intro s hs
    rcases presentation_of_seg_mem_segs hs with ⟨γ, hsγ⟩
    have hendpoints := (edgeSetPresentation γ).segment_endpoints_listed s hsγ
    exact ⟨point_mem_pts_of_presentation_point hendpoints.1,
      point_mem_pts_of_presentation_point hendpoints.2⟩
  · intro s t hs ht hst p hps hpt
    rcases presentation_of_seg_mem_segs hs with ⟨γ, hsγ⟩
    rcases presentation_of_seg_mem_segs ht with ⟨δ, htδ⟩
    by_cases hγδ : γ = δ
    · subst δ
      exact point_mem_pts_of_presentation_point
        ((edgeSetPresentation γ).segment_intersections_listed
          s t hsγ htδ hst p hps hpt)
    · have hpγ_carrier : p ∈ γ.1.carrier :=
        presentation_segment_point_mem_arc hsγ hps
      have hpδ_carrier : p ∈ δ.1.carrier :=
        presentation_segment_point_mem_arc htδ hpt
      by_cases hδsucc : δ = J.successor γ
      · have hp_inter :
            p ∈ γ.1.carrier ∩ (J.successor γ).1.carrier := by
          exact ⟨hpγ_carrier, by simpa [hδsucc] using hpδ_carrier⟩
        have hp_single : p ∈ ({γ.1.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [J.adjacent_intersection γ] using hp_inter
        have hp_eq : p = γ.1.target := by
          simpa using hp_single
        simpa [hp_eq] using target_mem_pts γ
      · by_cases hsuccδ : J.successor δ = γ
        · have hp_inter :
              p ∈ δ.1.carrier ∩ (J.successor δ).1.carrier := by
            exact ⟨hpδ_carrier, by simpa [hsuccδ] using hpγ_carrier⟩
          have hp_single : p ∈ ({δ.1.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
            simpa [J.adjacent_intersection δ] using hp_inter
          have hp_eq : p = δ.1.target := by
            simpa using hp_single
          simpa [hp_eq] using target_mem_pts δ
        · have hdisj : Disjoint γ.1.carrier δ.1.carrier :=
            J.nonadjacent_disjoint γ δ (Ne.symm hγδ) hδsucc hsuccδ
          exact False.elim
            ((Set.disjoint_left.mp hdisj) hpγ_carrier hpδ_carrier)
  · ext p
    constructor
    · intro hpJ
      have hpUnion :
          p ∈ ⋃ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs},
            (edgeSetPresentation γ).carrier := by
        simpa [hcarrier] using hpJ
      rcases Set.mem_iUnion.mp hpUnion with ⟨γ, hpK⟩
      have hpK_parts :
          p ∈ ((edgeSetPresentation γ).points : Set (EuclideanSpace ℝ (Fin 2))) ∪
            ⋃ s : {s // s ∈ (edgeSetPresentation γ).segments},
              segment ℝ s.1.1 s.1.2 := by
        simpa [(edgeSetPresentation γ).carrier_eq] using hpK
      rcases hpK_parts with hp_point | hp_segment
      · exact Or.inl (point_mem_pts_of_presentation_point hp_point)
      · right
        rcases Set.mem_iUnion.mp hp_segment with ⟨s, hps⟩
        exact Set.mem_iUnion.mpr
          ⟨⟨s.1, seg_mem_segs_of_presentation s.2⟩, by simpa using hps⟩
    · intro hp
      rcases hp with hp_point | hp_segment
      · dsimp [pts] at hp_point
        simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_attach, true_and]
          at hp_point
        rcases hp_point with ⟨γ, hpγ⟩
        rcases Finset.mem_union.mp hpγ with hpK_point | hp_endpoint
        · exact arc_point_mem_J (presentation_point_mem_arc hpK_point)
        · have hp_endpoint' :
              p = γ.1.source ∨ p = γ.1.target := by
            simpa using hp_endpoint
          rcases hp_endpoint' with hp_source | hp_target
          · simpa [hp_source] using
              arc_point_mem_J (γ := γ) (arc_source_mem_carrier γ.1)
          · simpa [hp_target] using
              arc_point_mem_J (γ := γ) (arc_target_mem_carrier γ.1)
      · rcases Set.mem_iUnion.mp hp_segment with ⟨s, hps⟩
        rcases presentation_of_seg_mem_segs s.2 with ⟨γ, hsγ⟩
        exact arc_point_mem_J
          (presentation_segment_point_mem_arc hsγ (by simpa using hps))
