import Util.IncidenceGeometry.FinitePolygonalSet

open Classical
noncomputable section

lemma FinitePolygonalSetSegmentIntersectionOfEndpointOffLines
    (K : FinitePolygonalSet)
    (u v : EuclideanSpace ℝ (Fin 2))
    (hoff : ∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ K.segments →
        v ∉ (affineSpan ℝ ({s.1, s.2} :
          Set (EuclideanSpace ℝ (Fin 2))) :
            AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))) :
    Set.Finite (segment ℝ u v ∩ K.carrier) := by
  let E := EuclideanSpace ℝ (Fin 2)
  have segment_subset_line :
      ∀ (a b : E),
        segment ℝ a b ⊆
          (affineSpan ℝ ({a, b} : Set E) : Set E) := by
    intro a b z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, _ht, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair t a b
  have pairFinite :
      ∀ s : E × E, s ∈ K.segments →
        Set.Finite (segment ℝ u v ∩ segment ℝ s.1 s.2) := by
    intro s hs
    apply Set.Subsingleton.finite
    intro p hp q hq
    by_contra hpq
    have hp_uv :
        p ∈ (affineSpan ℝ ({u, v} : Set E) : Set E) :=
      segment_subset_line u v hp.1
    have hq_uv :
        q ∈ (affineSpan ℝ ({u, v} : Set E) : Set E) :=
      segment_subset_line u v hq.1
    have hp_s :
        p ∈ (affineSpan ℝ ({s.1, s.2} : Set E) : Set E) :=
      segment_subset_line s.1 s.2 hp.2
    have hq_s :
        q ∈ (affineSpan ℝ ({s.1, s.2} : Set E) : Set E) :=
      segment_subset_line s.1 s.2 hq.2
    have huv :
        affineSpan ℝ ({p, q} : Set E) =
          affineSpan ℝ ({u, v} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_uv hq_uv hpq
    have hsline :
        affineSpan ℝ ({p, q} : Set E) =
          affineSpan ℝ ({s.1, s.2} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_s hq_s hpq
    apply hoff s hs
    rw [← hsline, huv]
    exact right_mem_affineSpan_pair ℝ u v
  let intersections : Set E :=
    ⋃ s : {s : E × E // s ∈ K.segments},
      segment ℝ u v ∩ segment ℝ s.1.1 s.1.2
  have hsegmentsFinite : Set.Finite intersections := by
    haveI : Finite {s : E × E // s ∈ K.segments} :=
      K.segments.finite_toSet
    apply Set.finite_iUnion
    intro s
    exact pairFinite s.1 s.2
  have hcover :
      segment ℝ u v ∩ K.carrier ⊆
        (K.points : Set E) ∪ intersections := by
    intro p hp
    rw [K.carrier_eq] at hp
    rcases hp.2 with hpPoint | hpSegment
    · exact Or.inl hpPoint
    · exact Or.inr (by
        rcases Set.mem_iUnion.mp hpSegment with ⟨s, hps⟩
        exact Set.mem_iUnion.mpr ⟨s, hp.1, hps⟩)
  exact (K.points.finite_toSet.union hsegmentsFinite).subset hcover
