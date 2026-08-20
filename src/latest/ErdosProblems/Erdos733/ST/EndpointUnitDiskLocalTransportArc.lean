import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section


-- [TABLET NODE: EndpointUnitDiskLocalTransportArc]
lemma EndpointUnitDiskLocalTransportArc
    (toWorld : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (γ : PolygonalArc)
    (htoWorld_inj : Function.Injective toWorld)
    (hsegment : ∀ x y : EuclideanSpace ℝ (Fin 2),
      toWorld '' segment ℝ x y = segment ℝ (toWorld x) (toWorld y))
    (hopen : ∀ x y : EuclideanSpace ℝ (Fin 2),
      toWorld '' openSegment ℝ x y = openSegment ℝ (toWorld x) (toWorld y)) :
    ∃ Ω : PolygonalArc,
      Ω.vertices = γ.vertices.map toWorld ∧
        Ω.source = toWorld γ.source ∧
          Ω.target = toWorld γ.target ∧
            Ω.carrier = toWorld '' γ.carrier ∧
              Ω.relativeInterior = toWorld '' γ.relativeInterior := by
-- BODY
  let Ω : PolygonalArc :=
    { vertices := γ.vertices.map toWorld
      length_ge_two := by simpa using γ.length_ge_two
      source := toWorld γ.source
      target := toWorld γ.target
      source_eq_head := by
        have h := congrArg (Option.map toWorld) γ.source_eq_head
        simpa using h
      target_eq_last := by
        have h := congrArg (Option.map toWorld) γ.target_eq_last
        simpa using h
      carrier := toWorld '' γ.carrier
      relativeInterior := toWorld '' γ.relativeInterior
      carrier_eq := by
        ext p
        constructor
        · rintro ⟨q, hq, rfl⟩
          rw [γ.carrier_eq] at hq
          rcases hq with ⟨n, hn, hqseg⟩
          refine ⟨n, ?_, ?_⟩
          · simpa using hn
          · have himage :
                toWorld q ∈ toWorld '' segment ℝ γ.vertices[n] γ.vertices[n + 1] :=
              ⟨q, hqseg, rfl⟩
            rw [hsegment] at himage
            simpa using himage
        · rintro ⟨n, hn, hpseg⟩
          have hnγ : n + 1 < γ.vertices.length := by simpa using hn
          have hpimage :
              p ∈ toWorld '' segment ℝ γ.vertices[n] γ.vertices[n + 1] := by
            rw [hsegment]
            simpa using hpseg
          rcases hpimage with ⟨q, hqseg, rfl⟩
          refine ⟨q, ?_, rfl⟩
          rw [γ.carrier_eq]
          exact ⟨n, hnγ, hqseg⟩
      relativeInterior_eq := by
        ext p
        constructor
        · rintro ⟨q, hq, rfl⟩
          rw [γ.relativeInterior_eq] at hq
          constructor
          · exact ⟨q, hq.1, rfl⟩
          · intro hpends
            rcases hpends with hp | hp
            · exact hq.2 (Or.inl (htoWorld_inj hp))
            · exact hq.2 (Or.inr (htoWorld_inj hp))
        · intro hp
          rcases hp.1 with ⟨q, hqcarrier, hqeq⟩
          refine ⟨q, ?_, hqeq⟩
          rw [γ.relativeInterior_eq]
          refine ⟨hqcarrier, ?_⟩
          intro hqends
          apply hp.2
          rcases hqends with hqsource | hqtarget
          · left
            have hqsource' : q = γ.source := by simpa using hqsource
            rw [← hqeq, hqsource']
          · right
            have hqtarget' : q = γ.target := by simpa using hqtarget
            rw [← hqeq, hqtarget']
            simp
      simple_vertices := by
        exact γ.simple_vertices.map htoWorld_inj
      segment_intersections := by
        intro i j hi hj hij
        have hiγ : i + 1 < γ.vertices.length := by simpa using hi
        have hjγ : j + 1 < γ.vertices.length := by simpa using hj
        have h_inter_image :
            segment ℝ (toWorld γ.vertices[i]) (toWorld γ.vertices[i + 1]) ∩
                segment ℝ (toWorld γ.vertices[j]) (toWorld γ.vertices[j + 1]) =
              toWorld ''
                (segment ℝ γ.vertices[i] γ.vertices[i + 1] ∩
                  segment ℝ γ.vertices[j] γ.vertices[j + 1]) := by
          ext p
          constructor
          · intro hp
            have hpi :
                p ∈ toWorld '' segment ℝ γ.vertices[i] γ.vertices[i + 1] := by
              rw [hsegment]
              exact hp.1
            have hpj :
                p ∈ toWorld '' segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
              rw [hsegment]
              exact hp.2
            rcases hpi with ⟨pi, hpi, rfl⟩
            rcases hpj with ⟨pj, hpj, hpj_eq⟩
            have hpipj : pi = pj := htoWorld_inj hpj_eq.symm
            refine ⟨pi, ⟨hpi, ?_⟩, rfl⟩
            simpa [hpipj] using hpj
          · rintro ⟨q, hq, rfl⟩
            constructor
            · rw [← hsegment]
              exact ⟨q, hq.1, rfl⟩
            · rw [← hsegment]
              exact ⟨q, hq.2, rfl⟩
        have hγ := γ.segment_intersections hiγ hjγ hij
        have htarget :
            segment ℝ (toWorld γ.vertices[i]) (toWorld γ.vertices[i + 1]) ∩
                segment ℝ (toWorld γ.vertices[j]) (toWorld γ.vertices[j + 1]) =
              if j = i + 1 then {toWorld γ.vertices[j]} else ∅ := by
          rw [h_inter_image, hγ]
          by_cases hsucc : j = i + 1
          · simp [hsucc]
          · simp [hsucc]
        simpa only [List.getElem_map] using htarget
      vertices_avoid_nonincident_interiors := by
        intro i k hi hk hki hkine hmem
        have hiγ : i + 1 < γ.vertices.length := by simpa using hi
        have hkγ : k < γ.vertices.length := by simpa using hk
        have hpreimage :
            γ.vertices[k] ∈ openSegment ℝ γ.vertices[i] γ.vertices[i + 1] := by
          have himage :
              toWorld (γ.vertices[k]) ∈
                toWorld '' openSegment ℝ γ.vertices[i] γ.vertices[i + 1] := by
            rw [hopen]
            simpa using hmem
          rcases himage with ⟨q, hq, hqeq⟩
          have hqv : q = γ.vertices[k] := htoWorld_inj hqeq
          simpa [hqv] using hq
        exact γ.vertices_avoid_nonincident_interiors hiγ hkγ hki hkine hpreimage }
  exact ⟨Ω, rfl, rfl, rfl, rfl, rfl⟩
