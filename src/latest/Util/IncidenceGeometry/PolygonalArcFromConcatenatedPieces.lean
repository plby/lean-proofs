import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

lemma PolygonalArcFromConcatenatedPieces
    (pieces : List PolygonalArc)
    (vertices : List (EuclideanSpace ℝ (Fin 2)))
    (source target : EuclideanSpace ℝ (Fin 2))
    (edgeSet : Set (EuclideanSpace ℝ (Fin 2)))
    (edgeSet_eq :
      edgeSet =
        {p | ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
          p ∈ segment ℝ vertices[i] vertices[i + 1]})
    (length_ge_two : 2 ≤ vertices.length)
    (source_eq_head : vertices.head? = some source)
    (target_eq_last : vertices.getLast? = some target)
    (simple_vertices : vertices.Nodup)
    (segment_intersections :
      ∀ ⦃i j : ℕ⦄,
        (hi : i + 1 < vertices.length) →
        (hj : j + 1 < vertices.length) →
        i < j →
        (segment ℝ vertices[i] vertices[i + 1] ∩
            segment ℝ vertices[j] vertices[j + 1]) =
          if j = i + 1 then {vertices[j]} else ∅)
    (vertices_avoid_nonincident_interiors :
      ∀ ⦃i k : ℕ⦄,
        (hi : i + 1 < vertices.length) →
        (hk : k < vertices.length) →
        k ≠ i →
        k ≠ i + 1 →
        vertices[k] ∉ openSegment ℝ vertices[i] vertices[i + 1])
    (carrier_eq_pieces :
      edgeSet = {p | ∃ Γ : PolygonalArc, Γ ∈ pieces ∧ p ∈ Γ.carrier})
    (piece_relativeInterior_subset :
      ∀ Γ, Γ ∈ pieces →
        Γ.relativeInterior ⊆
          edgeSet \ ({source, target} : Set (EuclideanSpace ℝ (Fin 2))))
    (piece_segment_lift :
      ∀ Γ, Γ ∈ pieces →
        ∀ m (hm : m + 1 < Γ.vertices.length),
          ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
            ((vertices[i] = Γ.vertices[m] ∧
                vertices[i + 1] = Γ.vertices[m + 1]) ∨
              (vertices[i] = Γ.vertices[m + 1] ∧
                vertices[i + 1] = Γ.vertices[m])))
    (segment_localized :
      ∀ i (hi : i + 1 < vertices.length),
        ∃ Γ : PolygonalArc, Γ ∈ pieces ∧
          ∃ m : ℕ, ∃ hm : m + 1 < Γ.vertices.length,
            ((vertices[i] = Γ.vertices[m] ∧
                vertices[i + 1] = Γ.vertices[m + 1]) ∨
              (vertices[i] = Γ.vertices[m + 1] ∧
                vertices[i + 1] = Γ.vertices[m]))) :
    ∃ Γ : PolygonalArc,
      Γ.vertices = vertices ∧
        Γ.source = source ∧
          Γ.target = target ∧
            Γ.carrier =
              {p | ∃ piece : PolygonalArc, piece ∈ pieces ∧ p ∈ piece.carrier} ∧
              Γ.relativeInterior =
                {p | ∃ piece : PolygonalArc, piece ∈ pieces ∧ p ∈ piece.carrier} \
                  ({source, target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                (∀ piece, piece ∈ pieces → piece.relativeInterior ⊆ Γ.relativeInterior) ∧
                  (∀ piece, piece ∈ pieces →
                    ∀ m (hm : m + 1 < piece.vertices.length),
                      ∃ i : ℕ, ∃ hi : i + 1 < Γ.vertices.length,
                        ((Γ.vertices[i] = piece.vertices[m] ∧
                            Γ.vertices[i + 1] = piece.vertices[m + 1]) ∨
                          (Γ.vertices[i] = piece.vertices[m + 1] ∧
                            Γ.vertices[i + 1] = piece.vertices[m]))) ∧
                    (∀ i (hi : i + 1 < Γ.vertices.length),
                      ∃ piece : PolygonalArc, piece ∈ pieces ∧
                        ∃ m : ℕ, ∃ hm : m + 1 < piece.vertices.length,
                          ((Γ.vertices[i] = piece.vertices[m] ∧
                              Γ.vertices[i + 1] = piece.vertices[m + 1]) ∨
                            (Γ.vertices[i] = piece.vertices[m + 1] ∧
                              Γ.vertices[i + 1] = piece.vertices[m]))) := by
  let Γ : PolygonalArc :=
    { vertices := vertices
      length_ge_two := length_ge_two
      source := source
      target := target
      source_eq_head := source_eq_head
      target_eq_last := target_eq_last
      carrier := edgeSet
      relativeInterior :=
        edgeSet \ ({source, target} : Set (EuclideanSpace ℝ (Fin 2)))
      carrier_eq := edgeSet_eq
      relativeInterior_eq := by rfl
      simple_vertices := simple_vertices
      segment_intersections := by
        intro i j hi hj hij
        exact segment_intersections hi hj hij
      vertices_avoid_nonincident_interiors := by
        intro i k hi hk hki hkine
        exact vertices_avoid_nonincident_interiors hi hk hki hkine }
  refine ⟨Γ, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact carrier_eq_pieces
  · change
      edgeSet \ ({source, target} : Set (EuclideanSpace ℝ (Fin 2))) =
        {p | ∃ piece : PolygonalArc, piece ∈ pieces ∧ p ∈ piece.carrier} \
          ({source, target} : Set (EuclideanSpace ℝ (Fin 2)))
    rw [carrier_eq_pieces]
  · intro piece hpiece p hp
    exact piece_relativeInterior_subset piece hpiece hp
  · intro piece hpiece m hm
    simpa [Γ] using piece_segment_lift piece hpiece m hm
  · intro i hi
    simpa [Γ] using segment_localized i hi
