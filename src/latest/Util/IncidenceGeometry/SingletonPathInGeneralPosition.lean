import Util.IncidenceGeometry.PolygonalPath
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.PolygonalPathInGeneralPosition

open Classical
noncomputable section

lemma SingletonPathInGeneralPosition (K : FinitePolygonalSet)
    (q : EuclideanSpace ℝ (Fin 2)) (hq : q ∉ K.carrier) :
    ∃ γ : PolygonalPath,
      γ.source = q ∧ γ.target = q ∧
        γ.carrier = ({q} : Set (EuclideanSpace ℝ (Fin 2))) ∧
          PolygonalPathInGeneralPosition γ K := by
  let γ : PolygonalPath :=
    { vertices := [q]
      vertices_nonempty := by simp
      source := q
      target := q
      source_eq_head := by simp
      target_eq_last := by simp
      carrier := ({q} : Set (EuclideanSpace ℝ (Fin 2)))
      carrier_eq := by
        ext p
        simp }
  refine ⟨γ, rfl, rfl, rfl, ?_⟩
  dsimp [PolygonalPathInGeneralPosition, γ]
  constructor
  · intro v hv hvK
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    exact hq (hv ▸ hvK)
  constructor
  · intro p hp hpγ
    have hpK : p ∈ K.carrier := by
      rw [K.carrier_eq]
      exact Or.inl hp
    simp only [Set.mem_singleton_iff] at hpγ
    exact hq (hpγ ▸ hpK)
  constructor
  · intro i hi s hs hoverlap
    simp at hi
  constructor
  · intro i hi s hs p hp_path hp_s hparallel
    simp at hi
  · exact (Set.finite_singleton q).inter_of_left K.carrier
