import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalPathStraightLineComplex

open Classical
noncomputable section

lemma PolygonalPathStraightLineComplexToArc
    (γ : PolygonalPath) (C : PolygonalPathStraightLineComplex γ) :
    ∃ Γ : PolygonalArc,
      Γ.source = γ.source ∧
        Γ.target = γ.target ∧
          Γ.carrier ⊆ γ.carrier ∧
            ∀ i : ℕ, (hi : i + 1 < Γ.vertices.length) →
              ∃ j : ℕ, ∃ hj : j + 1 < γ.vertices.length,
                segment ℝ Γ.vertices[i] Γ.vertices[i + 1] ⊆
                  segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
  let P := EuclideanSpace ℝ (Fin 2)
  let edgeSet : Set P :=
    {p | ∃ i : ℕ, ∃ hi : i + 1 < C.walk.length,
      p ∈ segment ℝ C.walk[i] C.walk[i + 1]}
  have get_ne_of_ne :
      ∀ {a b : ℕ} (ha : a < C.walk.length) (hb : b < C.walk.length),
        a ≠ b → C.walk[a]'ha ≠ C.walk[b]'hb := by
    intro a b ha hb hne heq
    have hnodup := C.walk_nodup
    rw [List.nodup_iff_injective_getElem] at hnodup
    have hfin : (⟨a, ha⟩ : Fin C.walk.length) = ⟨b, hb⟩ := by
      apply hnodup
      exact heq
    exact hne (congrArg Fin.val hfin)
  have edge_ne_of_lt :
      ∀ {i j : ℕ}
        (hi : i + 1 < C.walk.length) (hj : j + 1 < C.walk.length),
        i < j →
          (C.walk[i], C.walk[i + 1]) ≠ (C.walk[j], C.walk[j + 1]) := by
    intro i j hi hj hij heq
    have hfirst : C.walk[i] = C.walk[j] := congrArg Prod.fst heq
    exact
      (get_ne_of_ne (Nat.lt_of_succ_lt hi) (Nat.lt_of_succ_lt hj) (by omega))
        (by simpa using hfirst)
  have adjacent_endpoint_inter :
      ∀ {i : ℕ} (hi : (i + 1) + 1 < C.walk.length),
        (({C.walk[i], C.walk[i + 1]} : Set P) ∩
            ({C.walk[i + 1], C.walk[(i + 1) + 1]} : Set P)) =
          {C.walk[i + 1]} := by
    intro i hi
    have h01 : C.walk[i] ≠ C.walk[i + 1] :=
      get_ne_of_ne (by omega) (by omega) (by omega)
    have h02 : C.walk[i] ≠ C.walk[(i + 1) + 1] :=
      get_ne_of_ne (by omega) (by omega) (by omega)
    ext p
    constructor
    · intro hp
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with ⟨hp_left, hp_right⟩
      rcases hp_left with hp_i | hp_i1
      · rcases hp_right with hp_i1' | hp_i2
        · exact False.elim (h01 (by rw [← hp_i, ← hp_i1']))
        · exact False.elim (h02 (by rw [← hp_i, ← hp_i2]))
      · exact hp_i1
    · intro hp
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      exact ⟨Or.inr hp, Or.inl hp⟩
  have nonadjacent_endpoint_inter :
      ∀ {i j : ℕ}
        (hi : i + 1 < C.walk.length) (hj : j + 1 < C.walk.length),
        i + 1 < j →
          (({C.walk[i], C.walk[i + 1]} : Set P) ∩
              ({C.walk[j], C.walk[j + 1]} : Set P)) = ∅ := by
    intro i j hi hj hgap
    have h_i_j : C.walk[i] ≠ C.walk[j] :=
      get_ne_of_ne (by omega) (by omega) (by omega)
    have h_i_j1 : C.walk[i] ≠ C.walk[j + 1] :=
      get_ne_of_ne (by omega) (by omega) (by omega)
    have h_i1_j : C.walk[i + 1] ≠ C.walk[j] :=
      get_ne_of_ne (by omega) (by omega) (by omega)
    have h_i1_j1 : C.walk[i + 1] ≠ C.walk[j + 1] :=
      get_ne_of_ne (by omega) (by omega) (by omega)
    ext p
    constructor
    · intro hp
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false] at hp ⊢
      rcases hp with ⟨hp_left, hp_right⟩
      rcases hp_left with hp_i | hp_i1
      · rcases hp_right with hp_j | hp_j1
        · exact h_i_j (by rw [← hp_i, ← hp_j])
        · exact h_i_j1 (by rw [← hp_i, ← hp_j1])
      · rcases hp_right with hp_j | hp_j1
        · exact h_i1_j (by rw [← hp_i1, ← hp_j])
        · exact h_i1_j1 (by rw [← hp_i1, ← hp_j1])
    · intro hp
      exact False.elim hp
  have segment_intersections :
      ∀ ⦃i j : ℕ⦄,
        (hi : i + 1 < C.walk.length) →
        (hj : j + 1 < C.walk.length) →
        i < j →
        (segment ℝ C.walk[i] C.walk[i + 1] ∩
            segment ℝ C.walk[j] C.walk[j + 1]) =
          if j = i + 1 then {C.walk[j]} else ∅ := by
    intro i j hi hj hij
    have hei := C.walk_steps i hi
    have hej := C.walk_steps j hj
    have hene := edge_ne_of_lt hi hj hij
    have hinter :=
      C.distinct_edges_meet_at_common_endpoints
        (C.walk[i], C.walk[i + 1]) (C.walk[j], C.walk[j + 1]) hei hej hene
    by_cases hadj : j = i + 1
    · subst j
      simpa [hinter] using adjacent_endpoint_inter (i := i) hj
    · have hgap : i + 1 < j := by omega
      simpa [hinter, hadj] using nonadjacent_endpoint_inter hi hj hgap
  have vertices_avoid :
      ∀ ⦃i k : ℕ⦄,
        (hi : i + 1 < C.walk.length) →
        (hk : k < C.walk.length) →
        k ≠ i →
        k ≠ i + 1 →
        C.walk[k] ∉ openSegment ℝ C.walk[i] C.walk[i + 1] := by
    intro i k hi hk _hki _hki1
    exact
      C.no_vertex_in_edge_interior (C.walk[i], C.walk[i + 1]) (C.walk_steps i hi)
        C.walk[k]
        (C.walk_vertices_mem C.walk[k] (List.getElem_mem (l := C.walk) (n := k) hk))
  let Γ : PolygonalArc :=
    { vertices := C.walk
      length_ge_two := C.walk_length_ge_two
      source := γ.source
      target := γ.target
      source_eq_head := C.walk_head
      target_eq_last := C.walk_last
      carrier := edgeSet
      relativeInterior := edgeSet \ ({γ.source, γ.target} : Set P)
      carrier_eq := by rfl
      relativeInterior_eq := by rfl
      simple_vertices := C.walk_nodup
      segment_intersections := by
        intro i j hi hj hij
        exact segment_intersections hi hj hij
      vertices_avoid_nonincident_interiors := by
        intro i k hi hk hki hki1
        exact vertices_avoid hi hk hki hki1 }
  refine ⟨Γ, rfl, rfl, ?_, ?_⟩
  · intro p hp
    change p ∈ edgeSet at hp
    rcases hp with ⟨i, hi, hpseg⟩
    exact C.edge_subset_carrier (C.walk[i], C.walk[i + 1]) (C.walk_steps i hi) hpseg
  · intro i hi
    exact C.edge_refines_path_segment
      (C.walk[i], C.walk[i + 1]) (C.walk_steps i hi)
