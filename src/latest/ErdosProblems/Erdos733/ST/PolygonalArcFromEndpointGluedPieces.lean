import ErdosProblems.Erdos733.ST.PolygonalArcEndpointGluedVerticesBasic
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointGluedSegmentTransfer
import ErdosProblems.Erdos733.ST.PolygonalArcFromConcatenatedPieces

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcFromEndpointGluedPieces]
lemma PolygonalArcFromEndpointGluedPieces
    (pieces : List PolygonalArc)
    (source target : EuclideanSpace ℝ (Fin 2))
    (hpieces : pieces ≠ [])
    (first_source :
      ∀ Γ, pieces.head? = some Γ → Γ.source = source)
    (last_target :
      ∀ Γ, pieces.getLast? = some Γ → Γ.target = target)
    (successive_attach :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source)
    (glued_segment_endpoints_distinct :
      ∀ i
        (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length),
        (PolygonalArcEndpointGluedVertices pieces)[i] ≠
          (PolygonalArcEndpointGluedVertices pieces)[i + 1])
    (adjacent_segment_intersections :
      ∀ i
        (hi : (i + 1) + 1 <
          (PolygonalArcEndpointGluedVertices pieces).length),
        (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i]
              (PolygonalArcEndpointGluedVertices pieces)[i + 1] ∩
            segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i + 1]
              (PolygonalArcEndpointGluedVertices pieces)[(i + 1) + 1]) =
          {(PolygonalArcEndpointGluedVertices pieces)[i + 1]})
    (nonadjacent_segment_disjoint :
      ∀ ⦃i j : ℕ⦄,
        (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length) →
        (hj : j + 1 < (PolygonalArcEndpointGluedVertices pieces).length) →
        i + 1 < j →
        Disjoint
          (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i]
            (PolygonalArcEndpointGluedVertices pieces)[i + 1])
          (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[j]
            (PolygonalArcEndpointGluedVertices pieces)[j + 1]))
    (piece_relativeInterior_avoids_endpoints :
      ∀ Γ, Γ ∈ pieces →
        Disjoint Γ.relativeInterior
          ({source, target} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ Γ : PolygonalArc,
      Γ.vertices = PolygonalArcEndpointGluedVertices pieces ∧
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
-- BODY
  have hbasic := PolygonalArcEndpointGluedVerticesBasic pieces hpieces
  have hsource :
      (PolygonalArcEndpointGluedVertices pieces).head? = some source := by
    cases pieces with
    | nil => contradiction
    | cons Γ rest =>
        have hhead :
            (PolygonalArcEndpointGluedVertices (Γ :: rest)).head? =
              some Γ.source :=
          (PolygonalArcEndpointGluedVerticesBasic (Γ :: rest) (by simp)).2.1 Γ rfl
        have hΓ : Γ.source = source := first_source Γ rfl
        simpa [hΓ] using hhead
  have hlast_exists :
      ∃ Γ : PolygonalArc, pieces.getLast? = some Γ := by
    rcases List.eq_nil_or_concat pieces with hnil | ⟨init, Γ, hconcat⟩
    · exact False.elim (hpieces hnil)
    · refine ⟨Γ, ?_⟩
      simp [hconcat]
  have htarget :
      (PolygonalArcEndpointGluedVertices pieces).getLast? = some target := by
    rcases hlast_exists with ⟨Γ, hΓ⟩
    have hlast_glued := hbasic.2.2 Γ hΓ
    have hΓtarget : Γ.target = target := last_target Γ hΓ
    simpa [hΓtarget] using hlast_glued
  have no_equal_vertices_of_lt :
      ∀ ⦃r s : ℕ⦄,
        (hr : r < (PolygonalArcEndpointGluedVertices pieces).length) →
        (hs : s < (PolygonalArcEndpointGluedVertices pieces).length) →
        r < s →
        (PolygonalArcEndpointGluedVertices pieces)[r]'hr =
          (PolygonalArcEndpointGluedVertices pieces)[s]'hs →
        False := by
    intro r s hr hs hrs hrs_eq
    by_cases hs_succ : s = r + 1
    · subst s
      exact glued_segment_endpoints_distinct r hs (by simpa using hrs_eq)
    · have hgap_vertex : r + 1 < s := by omega
      have hs_pos : 0 < s := by omega
      let k := s - 1
      have hk_succ : k + 1 = s := by
        dsimp [k]
        omega
      have hr_edge :
          r + 1 < (PolygonalArcEndpointGluedVertices pieces).length := by
        omega
      have hk_edge :
          k + 1 < (PolygonalArcEndpointGluedVertices pieces).length := by
        simpa [hk_succ] using hs
      have hp_left :
          (PolygonalArcEndpointGluedVertices pieces)[r] ∈
            segment ℝ (PolygonalArcEndpointGluedVertices pieces)[r]
              (PolygonalArcEndpointGluedVertices pieces)[r + 1] :=
        left_mem_segment ℝ (PolygonalArcEndpointGluedVertices pieces)[r]
          (PolygonalArcEndpointGluedVertices pieces)[r + 1]
      have hp_right :
          (PolygonalArcEndpointGluedVertices pieces)[r] ∈
            segment ℝ (PolygonalArcEndpointGluedVertices pieces)[k]
              (PolygonalArcEndpointGluedVertices pieces)[k + 1] := by
        have hp_s :
            (PolygonalArcEndpointGluedVertices pieces)[s] ∈
              segment ℝ (PolygonalArcEndpointGluedVertices pieces)[k]
                (PolygonalArcEndpointGluedVertices pieces)[k + 1] := by
          simpa [hk_succ] using
            right_mem_segment ℝ (PolygonalArcEndpointGluedVertices pieces)[k]
              (PolygonalArcEndpointGluedVertices pieces)[k + 1]
        simpa [hrs_eq] using hp_s
      by_cases hk_adj : k = r + 1
      · have hk_adj_len :
            (r + 1) + 1 <
              (PolygonalArcEndpointGluedVertices pieces).length := by
          simpa [hk_adj] using hk_edge
        have hinter := adjacent_segment_intersections r hk_adj_len
        have hp_inter :
            (PolygonalArcEndpointGluedVertices pieces)[r] ∈
              segment ℝ (PolygonalArcEndpointGluedVertices pieces)[r]
                  (PolygonalArcEndpointGluedVertices pieces)[r + 1] ∩
                segment ℝ (PolygonalArcEndpointGluedVertices pieces)[r + 1]
                  (PolygonalArcEndpointGluedVertices pieces)[(r + 1) + 1] := by
          exact ⟨hp_left, by simpa [hk_adj] using hp_right⟩
        have hr_eq_next :
            (PolygonalArcEndpointGluedVertices pieces)[r] =
              (PolygonalArcEndpointGluedVertices pieces)[r + 1] := by
          rw [hinter] at hp_inter
          simpa using hp_inter
        exact glued_segment_endpoints_distinct r hr_edge hr_eq_next
      · have hnonadj : r + 1 < k := by
          dsimp [k] at hk_adj ⊢
          omega
        have hdis :=
          nonadjacent_segment_disjoint
            (i := r) (j := k) hr_edge hk_edge hnonadj
        exact (Set.disjoint_left.mp hdis hp_left) hp_right
  have simple_vertices :
      (PolygonalArcEndpointGluedVertices pieces).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    apply Fin.ext
    rcases Nat.lt_trichotomy i.1 j.1 with hlt | heq | hgt
    · exact False.elim (no_equal_vertices_of_lt i.2 j.2 hlt hij)
    · exact heq
    · exact False.elim (no_equal_vertices_of_lt j.2 i.2 hgt hij.symm)
  have segment_intersections :
      ∀ ⦃i j : ℕ⦄,
        (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length) →
        (hj : j + 1 < (PolygonalArcEndpointGluedVertices pieces).length) →
        i < j →
        (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i]
              (PolygonalArcEndpointGluedVertices pieces)[i + 1] ∩
            segment ℝ (PolygonalArcEndpointGluedVertices pieces)[j]
              (PolygonalArcEndpointGluedVertices pieces)[j + 1]) =
          if j = i + 1 then
            {(PolygonalArcEndpointGluedVertices pieces)[j]}
          else ∅ := by
    intro i j hi hj hij
    by_cases hadj : j = i + 1
    · subst j
      simpa using adjacent_segment_intersections i hj
    · have hgap : i + 1 < j := by omega
      have hdis := nonadjacent_segment_disjoint hi hj hgap
      simpa [hadj] using hdis.inter_eq
  let edgeSet : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | ∃ i : ℕ,
      ∃ hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length,
        p ∈ segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i]
          (PolygonalArcEndpointGluedVertices pieces)[i + 1]}
  have htransfer :=
    PolygonalArcEndpointGluedSegmentTransfer pieces successive_attach
  have hpiece_segment_lift := htransfer.1
  have hsegment_localized := htransfer.2
  have hcarrier_eq_pieces :
      edgeSet =
        {p | ∃ Γ : PolygonalArc, Γ ∈ pieces ∧ p ∈ Γ.carrier} := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨i, hi, hpseg⟩
      rcases hsegment_localized i hi with
        ⟨Γ, hΓ, m, hm, hmatch | hmatch⟩
      · refine ⟨Γ, hΓ, ?_⟩
        rw [Γ.carrier_eq]
        refine ⟨m, hm, ?_⟩
        simpa [edgeSet, hmatch.1, hmatch.2] using hpseg
      · refine ⟨Γ, hΓ, ?_⟩
        rw [Γ.carrier_eq]
        refine ⟨m, hm, ?_⟩
        simpa [edgeSet, hmatch.1, hmatch.2, segment_symm] using hpseg
    · intro hp
      rcases hp with ⟨Γ, hΓ, hpΓ⟩
      rw [Γ.carrier_eq] at hpΓ
      rcases hpΓ with ⟨m, hm, hpseg⟩
      rcases hpiece_segment_lift Γ hΓ m hm with
        ⟨i, hi, hmatch | hmatch⟩
      · refine ⟨i, hi, ?_⟩
        simpa [edgeSet, hmatch.1, hmatch.2] using hpseg
      · refine ⟨i, hi, ?_⟩
        simpa [edgeSet, hmatch.1, hmatch.2, segment_symm] using hpseg
  have hpiece_relativeInterior_subset :
      ∀ Γ, Γ ∈ pieces →
        Γ.relativeInterior ⊆
          edgeSet \ ({source, target} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro Γ hΓ p hp
    have hp_carrier : p ∈ Γ.carrier := by
      have hp' := hp
      rw [Γ.relativeInterior_eq] at hp'
      exact hp'.1
    have hp_edge : p ∈ edgeSet := by
      rw [hcarrier_eq_pieces]
      exact ⟨Γ, hΓ, hp_carrier⟩
    have hp_not : p ∉ ({source, target} : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hp_endpoint
      exact (Set.disjoint_left.mp
        (piece_relativeInterior_avoids_endpoints Γ hΓ) hp) hp_endpoint
    exact ⟨hp_edge, hp_not⟩
  have avoid_from_segments :
      ∀ (V : List (EuclideanSpace ℝ (Fin 2))),
        V.Nodup →
        (∀ ⦃m n : ℕ⦄,
          (hm : m + 1 < V.length) →
          (hn : n + 1 < V.length) →
          m < n →
          (segment ℝ V[m] V[m + 1] ∩
              segment ℝ V[n] V[n + 1]) =
            if n = m + 1 then {V[n]} else ∅) →
        ∀ ⦃m k : ℕ⦄,
          (hm : m + 1 < V.length) →
          (hk : k < V.length) →
          k ≠ m →
          k ≠ m + 1 →
          V[k] ∉ openSegment ℝ V[m] V[m + 1] := by
    intro V hnodup hsegments m k hm hk hkm hkm1 hopen
    have hseg_m : V[k] ∈ segment ℝ V[m] V[m + 1] :=
      openSegment_subset_segment ℝ V[m] V[m + 1] hopen
    rcases lt_or_gt_of_ne hkm with hkm_lt | hmk_lt
    · have hk_edge : k + 1 < V.length := by omega
      have hk_left : V[k] ∈ segment ℝ V[k] V[k + 1] :=
        left_mem_segment ℝ V[k] V[k + 1]
      have hinter :=
        hsegments (m := k) (n := m) hk_edge hm hkm_lt
      by_cases hm_adj : m = k + 1
      · have hmem_singleton :
            V[k] = V[m] := by
          have hp_inter :
              V[k] ∈ segment ℝ V[k] V[k + 1] ∩
                  segment ℝ V[m] V[m + 1] := ⟨hk_left, hseg_m⟩
          rw [hinter] at hp_inter
          simpa [hm_adj] using hp_inter
        have hk_lt_len : k < V.length := Nat.lt_trans (Nat.lt_succ_self k) hk_edge
        exact (Nat.ne_of_lt hkm_lt)
          ((hnodup.getElem_inj_iff (i := k) (j := m)
            (hi := hk_lt_len) (hj := Nat.lt_trans (Nat.lt_succ_self m) hm)).1
            hmem_singleton)
      · have hmem_empty :
            False := by
          have hp_inter :
              V[k] ∈ segment ℝ V[k] V[k + 1] ∩
                  segment ℝ V[m] V[m + 1] := ⟨hk_left, hseg_m⟩
          rw [hinter] at hp_inter
          simpa [hm_adj] using hp_inter
        exact hmem_empty
    · have hk_pos : 0 < k := by omega
      let j := k - 1
      have hj_succ : j + 1 = k := by omega
      have hj_edge : j + 1 < V.length := by simpa [hj_succ] using hk
      have hmj : m < j := by omega
      have hk_right : V[k] ∈ segment ℝ V[j] V[j + 1] := by
        simpa [hj_succ] using right_mem_segment ℝ V[j] V[j + 1]
      have hinter :=
        hsegments (m := m) (n := j) hm hj_edge hmj
      by_cases hj_adj : j = m + 1
      · have hmem_singleton :
            V[k] = V[j] := by
          have hp_inter :
              V[k] ∈ segment ℝ V[m] V[m + 1] ∩
                  segment ℝ V[j] V[j + 1] := ⟨hseg_m, hk_right⟩
          rw [hinter] at hp_inter
          simpa [hj_adj] using hp_inter
        have hj_lt_len : j < V.length := Nat.lt_trans (Nat.lt_succ_self j) hj_edge
        exact (Nat.ne_of_gt (by omega : j < k))
          ((hnodup.getElem_inj_iff (i := k) (j := j)
            (hi := hk) (hj := hj_lt_len)).1 hmem_singleton)
      · have hmem_empty :
            False := by
          have hp_inter :
              V[k] ∈ segment ℝ V[m] V[m + 1] ∩
                  segment ℝ V[j] V[j + 1] := ⟨hseg_m, hk_right⟩
          rw [hinter] at hp_inter
          simpa [hj_adj] using hp_inter
        exact hmem_empty
  have hvertices_avoid_nonincident_interiors :
      ∀ ⦃i k : ℕ⦄,
        (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length) →
        (hk : k < (PolygonalArcEndpointGluedVertices pieces).length) →
        k ≠ i →
        k ≠ i + 1 →
        (PolygonalArcEndpointGluedVertices pieces)[k] ∉
          openSegment ℝ (PolygonalArcEndpointGluedVertices pieces)[i]
            (PolygonalArcEndpointGluedVertices pieces)[i + 1] := by
    exact avoid_from_segments (PolygonalArcEndpointGluedVertices pieces)
      simple_vertices (by
        intro m n hm hn hmn
        exact segment_intersections hm hn hmn)
  rcases PolygonalArcFromConcatenatedPieces
      (pieces := pieces)
      (vertices := PolygonalArcEndpointGluedVertices pieces)
      (source := source)
      (target := target)
      (edgeSet := edgeSet)
      (edgeSet_eq := by rfl)
      (length_ge_two := hbasic.1)
      (source_eq_head := hsource)
      (target_eq_last := htarget)
      (simple_vertices := simple_vertices)
      (segment_intersections := by
        intro i j hi hj hij
        exact segment_intersections hi hj hij)
      (vertices_avoid_nonincident_interiors := by
        intro i k hi hk hki hkine
        exact hvertices_avoid_nonincident_interiors hi hk hki hkine)
      (carrier_eq_pieces := by
        exact hcarrier_eq_pieces)
      (piece_relativeInterior_subset := by
        intro Γ hΓ p hp
        exact hpiece_relativeInterior_subset Γ hΓ hp)
      (piece_segment_lift := by
        intro Γ hΓ m hm
        simpa using hpiece_segment_lift Γ hΓ m hm)
      (segment_localized := by
        intro i hi
        simpa using hsegment_localized i hi) with
    ⟨Γ, hvertices, hΓsource, hΓtarget, hcarrier, hrelativeInterior,
      hpiece_subset, hpiece_lift, hsegment_localized⟩
  exact ⟨Γ, hvertices, hΓsource, hΓtarget, hcarrier, hrelativeInterior,
    hpiece_subset, hpiece_lift, hsegment_localized⟩
