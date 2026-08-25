import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Util.IncidenceGeometry.FinitePolygonalSet

open Classical
noncomputable section

lemma FinitePolygonalSetCarrierEqSimpleClosedCurvePointsTwo
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier) :
    2 ≤ K.points.card := by
  have arc_source_mem_carrier :
      ∀ γ : PolygonalArc, γ.source ∈ γ.carrier := by
    intro γ
    rw [γ.carrier_eq]
    refine ⟨0, ?_, ?_⟩
    · have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      omega
    · have h0 : 0 < γ.vertices.length := by
        have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
        omega
      have hsource : γ.vertices[0] = γ.source := by
        have hget : γ.vertices[0]? = some γ.vertices[0] :=
          List.getElem?_eq_getElem h0
        rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
        exact Option.some.inj hget.symm
      have h1 : 1 < γ.vertices.length := by
        have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
        omega
      simpa [hsource] using left_mem_segment ℝ γ.source γ.vertices[1]
  have simple_closed_carrier_nontrivial :
      ∃ p q : EuclideanSpace ℝ (Fin 2),
        p ∈ J.carrier ∧ q ∈ J.carrier ∧ p ≠ q := by
    rcases J.edgeArcs_nonempty with ⟨γ, hγ⟩
    have h0lt : 0 < γ.vertices.length := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      omega
    have h1lt : 1 < γ.vertices.length := by
      have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
      omega
    have hsource : γ.vertices[0] = γ.source := by
      have hget : γ.vertices[0]? = some γ.vertices[0] :=
        List.getElem?_eq_getElem h0lt
      rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
      exact Option.some.inj hget.symm
    have hne01 : γ.source ≠ γ.vertices[1] := by
      intro hEq
      have hgetEq : γ.vertices[0] = γ.vertices[1] := by
        simpa [hsource] using hEq
      have hidx : (0 : ℕ) = 1 := by
        exact (γ.simple_vertices.getElem_inj_iff).mp hgetEq
      omega
    have hsrcJ : γ.source ∈ J.carrier := by
      rw [J.carrier_eq]
      exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, arc_source_mem_carrier γ⟩
    have h1arc : γ.vertices[1] ∈ γ.carrier := by
      rw [γ.carrier_eq]
      refine ⟨0, ?_, ?_⟩
      · omega
      · simpa [hsource] using right_mem_segment ℝ γ.source γ.vertices[1]
    have h1J : γ.vertices[1] ∈ J.carrier := by
      rw [J.carrier_eq]
      exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, h1arc⟩
    exact ⟨γ.source, γ.vertices[1], hsrcJ, h1J, hne01⟩
  by_contra hlt
  have hcard_le : K.points.card ≤ 1 := by omega
  have hsegments_empty : K.segments = ∅ := by
    ext s
    constructor
    · intro hs
      rcases K.segment_endpoints_listed s hs with ⟨hs1, hs2⟩
      have h_eq : s.1 = s.2 := by
        by_contra hne
        have hpair :
            ({s.1, s.2} : Finset (EuclideanSpace ℝ (Fin 2))) ⊆ K.points := by
          intro x hx
          simp at hx
          rcases hx with rfl | rfl
          · exact hs1
          · exact hs2
        have htwo : 2 ≤ K.points.card := by
          calc
            2 = ({s.1, s.2} : Finset (EuclideanSpace ℝ (Fin 2))).card := by
              simp [hne]
            _ ≤ K.points.card := Finset.card_le_card hpair
        omega
      exact (K.segment_nondegenerate s hs h_eq).elim
    · simp
  have hK_subset_points :
      K.carrier ⊆ (K.points : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro p hp
    rw [K.carrier_eq] at hp
    rcases hp with hp_points | hp_seg
    · exact hp_points
    · simp [hsegments_empty] at hp_seg
  rcases simple_closed_carrier_nontrivial with ⟨p, q, hpJ, hqJ, hpq⟩
  have hpK : p ∈ K.points := hK_subset_points (by rwa [hKJ])
  have hqK : q ∈ K.points := hK_subset_points (by rwa [hKJ])
  have hpair :
      ({p, q} : Finset (EuclideanSpace ℝ (Fin 2))) ⊆ K.points := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hpK
    · exact hqK
  have htwo : 2 ≤ K.points.card := by
    calc
      2 = ({p, q} : Finset (EuclideanSpace ℝ (Fin 2))).card := by
        simp [hpq]
      _ ≤ K.points.card := Finset.card_le_card hpair
  omega
