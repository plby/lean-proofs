import Util.IncidenceGeometry.EndpointUnitDiskAlternatingVertexList
import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

lemma EndpointUnitDiskAlternatingVertexListArc
    (A B : EuclideanSpace ℝ (Fin 2))
    (blocks : List (List (EuclideanSpace ℝ (Fin 2))))
    (C U : Set (EuclideanSpace ℝ (Fin 2))) :
    let V := EndpointUnitDiskAlternatingVertexList A B blocks
    let edgeSet : Set (EuclideanSpace ℝ (Fin 2)) :=
      {p | ∃ m : ℕ, ∃ hm : m + 1 < V.length,
        p ∈ segment ℝ V[m] V[m + 1]}
    V.Nodup →
      (∀ ⦃m n : ℕ⦄,
        (hm : m + 1 < V.length) →
        (hn : n + 1 < V.length) →
        m < n →
        (segment ℝ V[m] V[m + 1] ∩ segment ℝ V[n] V[n + 1]) =
          if n = m + 1 then {V[n]} else ∅) →
      (∀ ⦃m k : ℕ⦄,
        (hm : m + 1 < V.length) →
        (hk : k < V.length) →
        k ≠ m →
        k ≠ m + 1 →
        V[k] ∉ openSegment ℝ V[m] V[m + 1]) →
      (∀ ⦃m : ℕ⦄,
        (hm : m + 1 < V.length) →
        segment ℝ V[m] V[m + 1] ⊆ C) →
      (∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        p ∈ edgeSet → p ≠ A → p ≠ B → p ∈ U) →
      ∃ Γ : PolygonalArc,
        Γ.vertices = V ∧
          Γ.source = A ∧
            Γ.target = B ∧
              Γ.carrier = edgeSet ∧
                Γ.relativeInterior = edgeSet \ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                  Γ.carrier ⊆ C ∧
                    Γ.relativeInterior ⊆ U := by
  dsimp only
  intro hnodup hsegments havoid hcarrier hrelative
  let V := EndpointUnitDiskAlternatingVertexList A B blocks
  let edgeSet : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | ∃ m : ℕ, ∃ hm : m + 1 < V.length,
      p ∈ segment ℝ V[m] V[m + 1]}
  have hlen : 2 ≤ V.length := by
    simp [V, EndpointUnitDiskAlternatingVertexList]
  have hhead : V.head? = some A := by
    simp [V, EndpointUnitDiskAlternatingVertexList]
  have hlast : V.getLast? = some B := by
    rw [show V = [A] ++ (blocks.flatten ++ [B]) by
      simp [V, EndpointUnitDiskAlternatingVertexList]]
    rw [List.getLast?_append_of_ne_nil [A] (by simp :
      blocks.flatten ++ [B] ≠ [])]
    simp
  refine ⟨
    { vertices := V
      length_ge_two := hlen
      source := A
      target := B
      source_eq_head := hhead
      target_eq_last := hlast
      carrier := edgeSet
      relativeInterior := edgeSet \ ({A, B} : Set (EuclideanSpace ℝ (Fin 2)))
      carrier_eq := by rfl
      relativeInterior_eq := by rfl
      simple_vertices := by simpa [V] using hnodup
      segment_intersections := by
        intro m n hm hn hmn
        simpa [V] using hsegments hm hn hmn
      vertices_avoid_nonincident_interiors := by
        intro m k hm hk hkm hkm1
        simpa [V] using havoid hm hk hkm hkm1 },
    ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro p hp
    rcases hp with ⟨m, hm, hpm⟩
    exact hcarrier hm hpm
  · intro p hp
    change p ∈ edgeSet \ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))) at hp
    exact hrelative hp.1 (by intro h; exact hp.2 (by simp [h]))
      (by intro h; exact hp.2 (by simp [h]))
