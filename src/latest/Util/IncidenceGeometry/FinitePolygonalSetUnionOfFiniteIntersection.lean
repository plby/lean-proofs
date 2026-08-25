import Util.IncidenceGeometry.FinitePolygonalSet

open Classical
noncomputable section

lemma FinitePolygonalSetUnionOfFiniteIntersection
    (K L : FinitePolygonalSet)
    (hfinite : Set.Finite (K.carrier ∩ L.carrier)) :
    ∃ M : FinitePolygonalSet,
      M.carrier = K.carrier ∪ L.carrier := by
  let E := EuclideanSpace ℝ (Fin 2)
  let crossPoints : Finset E := hfinite.toFinset
  let points : Finset E := K.points ∪ L.points ∪ crossPoints
  let segments : Finset (E × E) := K.segments ∪ L.segments
  have segment_mem_carrier :
      ∀ (N : FinitePolygonalSet) (s : E × E), s ∈ N.segments →
        segment ℝ s.1 s.2 ⊆ N.carrier := by
    intro N s hs x hx
    rw [N.carrier_eq]
    right
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩
  refine ⟨
    { carrier := K.carrier ∪ L.carrier
      points := points
      segments := segments
      segment_nondegenerate := ?_
      segment_endpoints_listed := ?_
      segment_intersections_listed := ?_
      carrier_eq := ?_ },
    rfl⟩
  · intro s hs
    simp only [segments, Finset.mem_union] at hs
    rcases hs with hs | hs
    · exact K.segment_nondegenerate s hs
    · exact L.segment_nondegenerate s hs
  · intro s hs
    simp only [segments, Finset.mem_union] at hs
    rcases hs with hs | hs
    · have hends := K.segment_endpoints_listed s hs
      constructor <;> simp [points, hends.1, hends.2]
    · have hends := L.segment_endpoints_listed s hs
      constructor <;> simp [points, hends.1, hends.2]
  · intro s t hs ht hst p hps hpt
    simp only [segments, Finset.mem_union] at hs ht
    rcases hs with hsK | hsL
    · rcases ht with htK | htL
      · have hp := K.segment_intersections_listed s t hsK htK hst p hps hpt
        simp [points, hp]
      · have hpK : p ∈ K.carrier := segment_mem_carrier K s hsK hps
        have hpL : p ∈ L.carrier := segment_mem_carrier L t htL hpt
        have hpCross : p ∈ crossPoints := by
          simpa [crossPoints] using (show p ∈ K.carrier ∩ L.carrier from ⟨hpK, hpL⟩)
        simp [points, hpCross]
    · rcases ht with htK | htL
      · have hpL : p ∈ L.carrier := segment_mem_carrier L s hsL hps
        have hpK : p ∈ K.carrier := segment_mem_carrier K t htK hpt
        have hpCross : p ∈ crossPoints := by
          simpa [crossPoints] using (show p ∈ K.carrier ∩ L.carrier from ⟨hpK, hpL⟩)
        simp [points, hpCross]
      · have hp := L.segment_intersections_listed s t hsL htL hst p hps hpt
        simp [points, hp]
  · ext p
    constructor
    · intro hp
      rcases hp with hpK | hpL
      · rw [K.carrier_eq] at hpK
        rcases hpK with hpPoint | hpSegment
        · left
          simp [points, hpPoint]
        · right
          rcases Set.mem_iUnion.mp hpSegment with ⟨s, hps⟩
          exact Set.mem_iUnion.mpr
            ⟨⟨s.1, by simp [segments, s.2]⟩, hps⟩
      · rw [L.carrier_eq] at hpL
        rcases hpL with hpPoint | hpSegment
        · left
          simp [points, hpPoint]
        · right
          rcases Set.mem_iUnion.mp hpSegment with ⟨s, hps⟩
          exact Set.mem_iUnion.mpr
            ⟨⟨s.1, by simp [segments, s.2]⟩, hps⟩
    · intro hp
      rcases hp with hpPoint | hpSegment
      · simp only [points, Finset.coe_union, Set.mem_union] at hpPoint
        rcases hpPoint with (hpK | hpL) | hpCross
        · left
          rw [K.carrier_eq]
          exact Or.inl hpK
        · right
          rw [L.carrier_eq]
          exact Or.inl hpL
        · have hpInter : p ∈ K.carrier ∩ L.carrier := by
            simpa [crossPoints] using hpCross
          exact Or.inl hpInter.1
      · rcases Set.mem_iUnion.mp hpSegment with ⟨s, hps⟩
        rcases s with ⟨s, hs⟩
        simp only [segments, Finset.mem_union] at hs
        rcases hs with hsK | hsL
        · exact Or.inl (segment_mem_carrier K s hsK hps)
        · exact Or.inr (segment_mem_carrier L s hsL hps)
