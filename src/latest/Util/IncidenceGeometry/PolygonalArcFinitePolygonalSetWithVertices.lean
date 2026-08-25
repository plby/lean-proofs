import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.PolygonalArcFinitePolygonalSet
import Util.IncidenceGeometry.PolygonalArcVertexMemCarrier

open Classical
noncomputable section

lemma PolygonalArcFinitePolygonalSetWithVertices (Γ : PolygonalArc) :
    ∃ K : FinitePolygonalSet,
      K.carrier = Γ.carrier ∧
        ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ Γ.vertices → v ∈ K.points := by
  obtain ⟨K₀, hK₀carrier⟩ := PolygonalArcFinitePolygonalSet Γ
  let pts : Finset (EuclideanSpace ℝ (Fin 2)) := K₀.points ∪ Γ.vertices.toFinset
  refine
    ⟨{ carrier := K₀.carrier
       points := pts
       segments := K₀.segments
       segment_nondegenerate := K₀.segment_nondegenerate
       segment_endpoints_listed := ?_
       segment_intersections_listed := ?_
       carrier_eq := ?_ },
      hK₀carrier, ?_⟩
  · intro s hs
    exact
      ⟨Finset.mem_union.mpr (Or.inl ((K₀.segment_endpoints_listed s hs).1)),
        Finset.mem_union.mpr (Or.inl ((K₀.segment_endpoints_listed s hs).2))⟩
  · intro s t hs ht hst p hps hpt
    exact
      Finset.mem_union.mpr
        (Or.inl (K₀.segment_intersections_listed s t hs ht hst p hps hpt))
  · ext p
    simp only [pts, Finset.coe_union, Set.mem_union]
    constructor
    · intro hp
      rw [K₀.carrier_eq] at hp
      rcases hp with hp | hp
      · exact Or.inl (Or.inl hp)
      · exact Or.inr hp
    · intro hp
      rw [K₀.carrier_eq]
      rcases hp with hp | hp
      · rcases hp with hp | hp
        · exact Or.inl hp
        · have hpΓvertices : p ∈ Γ.vertices := by
            simpa using hp
          have hpΓcarrier : p ∈ Γ.carrier :=
            PolygonalArcVertexMemCarrier Γ hpΓvertices
          have hpK₀carrier : p ∈ K₀.carrier := by
            simpa [hK₀carrier] using hpΓcarrier
          simpa [K₀.carrier_eq] using hpK₀carrier
      · exact Or.inr hp
  · intro v hv
    exact Finset.mem_union.mpr (Or.inr (by simpa using hv))
