import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.Convex
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcOpenSegmentSubsetRelativeInterior
import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section


private lemma arcCrossingOrderedTailArc_construct
    (δ : PolygonalArc) (j : ℕ) (c : EuclideanSpace ℝ (Fin 2))
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1]) :
    ∃ τ : PolygonalArc,
      τ.vertices = c :: δ.vertices.drop (j + 1) ∧
        τ.source = c ∧
          τ.target = δ.target ∧
            τ.carrier ⊆ δ.carrier := by
  let V : List (EuclideanSpace ℝ (Fin 2)) := c :: δ.vertices.drop (j + 1)
  let C : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | ∃ i : ℕ, ∃ hi : i + 1 < V.length,
      p ∈ segment ℝ V[i] V[i + 1]}
  have hV_len : 2 ≤ V.length := by
    dsimp [V]
    simp [List.length_drop]
    omega
  have hV_head : V.head? = some c := by
    simp [V]
  have hV_last : V.getLast? = some δ.target := by
    dsimp [V]
    rw [List.getLast?_cons, List.getLast?_drop]
    have hnot : ¬ δ.vertices.length ≤ j + 1 := by omega
    simp [hnot, δ.target_eq_last]
  have hV_get_succ :
      ∀ n (hn : n + 1 < V.length),
        V[n + 1] = δ.vertices[j + 1 + n]'(by
          have hdrop : n < (δ.vertices.drop (j + 1)).length := by
            dsimp [V] at hn
            simpa using hn
          simp [List.length_drop] at hdrop
          omega) := by
    intro n hn
    have hdrop : n < (δ.vertices.drop (j + 1)).length := by
      dsimp [V] at hn
      simpa using hn
    dsimp [V]
    simpa using (List.getElem_drop (xs := δ.vertices) (i := j + 1)
      (j := n) (h := hdrop))
  have hV_get_pos :
      ∀ n (hnpos : 0 < n) (hn : n < V.length),
        V[n] = δ.vertices[j + n]'(by
          cases n with
          | zero => omega
          | succ q =>
              have hq : q + 1 < V.length := by simpa using hn
              have hdrop : q < (δ.vertices.drop (j + 1)).length := by
                dsimp [V] at hq
                simpa using hq
              simp [List.length_drop] at hdrop
              omega) := by
    intro n hnpos hn
    cases n with
    | zero => omega
    | succ q =>
        have hq : q + 1 < V.length := by simpa using hn
        have hidx : j + 1 + q = j + (q + 1) := by omega
        simpa [hidx] using hV_get_succ q hq
  have hc_ne_left : c ≠ δ.vertices[j] := by
    intro h
    have hleft : δ.vertices[j] ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1] := by
      simpa [h] using hcOpen
    have hne : δ.vertices[j] ≠ δ.vertices[j + 1] := by
      intro hEq
      have hidx : j = j + 1 :=
        (δ.simple_vertices.getElem_inj_iff
          (i := j) (j := j + 1)
          (hi := Nat.lt_of_succ_lt hj) (hj := hj)).1 hEq
      omega
    exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)
      (x := δ.vertices[j]) (y := δ.vertices[j + 1])).1 hleft)
  have hc_ne_right : c ≠ δ.vertices[j + 1] := by
    intro h
    have hright : δ.vertices[j + 1] ∈
        openSegment ℝ δ.vertices[j] δ.vertices[j + 1] := by
      simpa [h] using hcOpen
    have hne : δ.vertices[j] ≠ δ.vertices[j + 1] := by
      intro hEq
      have hidx : j = j + 1 :=
        (δ.simple_vertices.getElem_inj_iff
          (i := j) (j := j + 1)
          (hi := Nat.lt_of_succ_lt hj) (hj := hj)).1 hEq
      omega
    exact hne ((right_mem_openSegment_iff (𝕜 := ℝ)
      (x := δ.vertices[j]) (y := δ.vertices[j + 1])).1 hright)
  have hV_nodup : V.Nodup := by
    dsimp [V]
    rw [List.nodup_cons]
    constructor
    · intro hc_mem
      rcases List.get_of_mem hc_mem with ⟨k, hk⟩
      have hk_orig_lt : j + 1 + k.1 < δ.vertices.length := by
        have hklen : k.1 < (δ.vertices.drop (j + 1)).length := k.2
        simp [List.length_drop] at hklen
        omega
      have hc_eq : c = δ.vertices[j + 1 + k.1] := by
        rw [← hk]
        exact (List.getElem_drop (xs := δ.vertices) (i := j + 1)
          (j := k.1) (h := k.2))
      by_cases hk0 : k.1 = 0
      · exact hc_ne_right (by simpa [hk0, Nat.add_assoc] using hc_eq)
      · have hopen_vertex :
            δ.vertices[j + 1 + k.1] ∈
              openSegment ℝ δ.vertices[j] δ.vertices[j + 1] := by
          simpa [hc_eq] using hcOpen
        have hnot :=
          δ.vertices_avoid_nonincident_interiors (i := j) (k := j + 1 + k.1)
            hj hk_orig_lt (by omega) (by omega)
        exact hnot hopen_vertex
    · exact δ.simple_vertices.drop
  have hV_segment_pos :
      ∀ n (hn : n + 1 < V.length), 0 < n →
        segment ℝ V[n] V[n + 1] =
          segment ℝ (δ.vertices[j + n]'(by
            dsimp [V] at hn
            simp [List.length_drop] at hn
            omega))
            (δ.vertices[j + n + 1]'(by
              dsimp [V] at hn
              simp [List.length_drop] at hn
              omega)) := by
    intro n hn hnpos
    have hVn := hV_get_pos n hnpos (Nat.lt_of_succ_lt hn)
    have hVn1 := hV_get_pos (n + 1) (by omega) hn
    simpa [Nat.add_assoc, hVn, hVn1]
  have hV_first_subset :
      segment ℝ V[0] V[1] ⊆
        segment ℝ δ.vertices[j] δ.vertices[j + 1] := by
    intro z hz
    have hcseg : c ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
      openSegment_subset_segment ℝ δ.vertices[j] δ.vertices[j + 1] hcOpen
    have hright : δ.vertices[j + 1] ∈
        segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
      right_mem_segment ℝ δ.vertices[j] δ.vertices[j + 1]
    have hV0 : V[0] = c := by simp [V]
    have hV1 : V[1] = δ.vertices[j + 1] := by
      simpa using hV_get_succ 0 (by
        dsimp [V]
        simp [List.length_drop]
        omega)
    have hz' : z ∈ segment ℝ c δ.vertices[j + 1] := by
      simpa [hV0, hV1] using hz
    exact (convex_segment δ.vertices[j] δ.vertices[j + 1]).segment_subset
      hcseg hright hz'
  have hV_segment_intersections :
      ∀ ⦃i k : ℕ⦄,
        (hi : i + 1 < V.length) →
        (hk : k + 1 < V.length) →
        i < k →
        (segment ℝ V[i] V[i + 1] ∩
            segment ℝ V[k] V[k + 1]) =
          if k = i + 1 then {V[k]} else ∅ := by
    intro i k hi hk hik
    by_cases hi0 : i = 0
    · subst i
      have hkpos : 0 < k := by omega
      have hsegk := hV_segment_pos k hk hkpos
      have hk_orig : j + k + 1 < δ.vertices.length := by
        dsimp [V] at hk
        simp [List.length_drop] at hk
        omega
      have hj_lt_jk : j < j + k := by omega
      have hδinter :=
        δ.segment_intersections (i := j) (j := j + k) hj hk_orig hj_lt_jk
      by_cases hk1 : k = 1
      · subst k
        have hV1 : V[1] = δ.vertices[j + 1] := by
          simpa using hV_get_succ 0 (by
            dsimp [V]
            simp [List.length_drop]
            omega)
        ext p
        constructor
        · intro hp
          have hpδ : p ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] ∩
              segment ℝ δ.vertices[j + 1] δ.vertices[j + 1 + 1] := by
            exact ⟨hV_first_subset hp.1, by
              simpa [hsegk, Nat.add_assoc] using hp.2⟩
          have hp_single : p ∈ ({δ.vertices[j + 1]} :
              Set (EuclideanSpace ℝ (Fin 2))) := by
            have hδinter_single :
                segment ℝ δ.vertices[j] δ.vertices[j + 1] ∩
                    segment ℝ δ.vertices[j + 1] δ.vertices[j + 1 + 1] =
                  ({δ.vertices[j + 1]} :
                    Set (EuclideanSpace ℝ (Fin 2))) := by
              simpa [Nat.add_assoc] using hδinter
            simpa [hδinter_single] using hpδ
          simpa [hV1] using hp_single
        · intro hp
          have hpV : p = V[1] := by simpa using hp
          subst p
          constructor
          · exact right_mem_segment ℝ V[0] V[1]
          · have hleft : δ.vertices[j + 1] ∈
                segment ℝ δ.vertices[j + 1] δ.vertices[j + 1 + 1] :=
              left_mem_segment ℝ δ.vertices[j + 1] δ.vertices[j + 1 + 1]
            rw [hsegk]
            simpa [hV1, Nat.add_assoc] using hleft
      · have hδempty :
            segment ℝ δ.vertices[j] δ.vertices[j + 1] ∩
              segment ℝ δ.vertices[j + k] δ.vertices[j + k + 1] =
                (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [hk1, Nat.add_assoc] using hδinter
        ext p
        constructor
        · intro hp
          have hpδ : p ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] ∩
              segment ℝ δ.vertices[j + k] δ.vertices[j + k + 1] := by
            exact ⟨hV_first_subset hp.1, by simpa [hsegk] using hp.2⟩
          rw [hδempty] at hpδ
          exact False.elim hpδ
        · intro hp
          simp [hk1] at hp
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hkpos : 0 < k := by omega
      have hsegi := hV_segment_pos i hi hipos
      have hsegk := hV_segment_pos k hk hkpos
      have hi_orig : j + i + 1 < δ.vertices.length := by
        dsimp [V] at hi
        simp [List.length_drop] at hi
        omega
      have hk_orig : j + k + 1 < δ.vertices.length := by
        dsimp [V] at hk
        simp [List.length_drop] at hk
        omega
      have hlt_orig : j + i < j + k := by omega
      have hδinter :=
        δ.segment_intersections (i := j + i) (j := j + k)
          hi_orig hk_orig hlt_orig
      by_cases hadj : k = i + 1
      · subst k
        have hVi1 : V[i + 1] = δ.vertices[j + (i + 1)] := by
          exact hV_get_pos (i + 1) (by omega) (Nat.lt_of_succ_lt hk)
        rw [hsegi, hsegk]
        simpa [hVi1, Nat.add_assoc] using hδinter
      · have hnot_adj_orig : j + k ≠ j + i + 1 := by omega
        simpa [hsegi, hsegk, hadj, hnot_adj_orig, Nat.add_assoc] using hδinter
  have avoid_from_segments :
      ∀ (W : List (EuclideanSpace ℝ (Fin 2))),
        W.Nodup →
        (∀ ⦃m n : ℕ⦄,
          (hm : m + 1 < W.length) →
          (hn : n + 1 < W.length) →
          m < n →
          (segment ℝ W[m] W[m + 1] ∩
              segment ℝ W[n] W[n + 1]) =
            if n = m + 1 then {W[n]} else ∅) →
        ∀ ⦃m k : ℕ⦄,
          (hm : m + 1 < W.length) →
          (hk : k < W.length) →
          k ≠ m →
          k ≠ m + 1 →
          W[k] ∉ openSegment ℝ W[m] W[m + 1] := by
    intro W hnodup hsegments m k hm hk hkm hkm1 hopen
    have hseg_m : W[k] ∈ segment ℝ W[m] W[m + 1] :=
      openSegment_subset_segment ℝ W[m] W[m + 1] hopen
    rcases lt_or_gt_of_ne hkm with hkm_lt | hmk_lt
    · have hk_edge : k + 1 < W.length := by omega
      have hk_left : W[k] ∈ segment ℝ W[k] W[k + 1] :=
        left_mem_segment ℝ W[k] W[k + 1]
      have hinter :=
        hsegments (m := k) (n := m) hk_edge hm hkm_lt
      by_cases hm_adj : m = k + 1
      · have hmem_singleton :
            W[k] = W[m] := by
          have hp_inter :
              W[k] ∈ segment ℝ W[k] W[k + 1] ∩
                  segment ℝ W[m] W[m + 1] := ⟨hk_left, hseg_m⟩
          rw [hinter] at hp_inter
          simpa [hm_adj] using hp_inter
        have hk_lt_len : k < W.length := Nat.lt_trans (Nat.lt_succ_self k) hk_edge
        exact (Nat.ne_of_lt hkm_lt)
          ((hnodup.getElem_inj_iff (i := k) (j := m)
            (hi := hk_lt_len) (hj := Nat.lt_trans (Nat.lt_succ_self m) hm)).1
            hmem_singleton)
      · have hmem_empty :
            False := by
          have hp_inter :
              W[k] ∈ segment ℝ W[k] W[k + 1] ∩
                  segment ℝ W[m] W[m + 1] := ⟨hk_left, hseg_m⟩
          rw [hinter] at hp_inter
          simpa [hm_adj] using hp_inter
        exact hmem_empty
    · have hk_pos : 0 < k := by omega
      let n := k - 1
      have hn_succ : n + 1 = k := by omega
      have hn_edge : n + 1 < W.length := by simpa [hn_succ] using hk
      have hmn : m < n := by omega
      have hk_right : W[k] ∈ segment ℝ W[n] W[n + 1] := by
        simpa [hn_succ] using right_mem_segment ℝ W[n] W[n + 1]
      have hinter :=
        hsegments (m := m) (n := n) hm hn_edge hmn
      by_cases hn_adj : n = m + 1
      · have hmem_singleton :
            W[k] = W[n] := by
          have hp_inter :
              W[k] ∈ segment ℝ W[m] W[m + 1] ∩
                  segment ℝ W[n] W[n + 1] := ⟨hseg_m, hk_right⟩
          rw [hinter] at hp_inter
          simpa [hn_adj] using hp_inter
        have hn_lt_len : n < W.length := Nat.lt_trans (Nat.lt_succ_self n) hn_edge
        exact (Nat.ne_of_gt (by omega : n < k))
          ((hnodup.getElem_inj_iff (i := k) (j := n)
            (hi := hk) (hj := hn_lt_len)).1 hmem_singleton)
      · have hmem_empty :
            False := by
          have hp_inter :
              W[k] ∈ segment ℝ W[m] W[m + 1] ∩
                  segment ℝ W[n] W[n + 1] := ⟨hseg_m, hk_right⟩
          rw [hinter] at hp_inter
          simpa [hn_adj] using hp_inter
        exact hmem_empty
  have hV_vertices_avoid :
      ∀ ⦃i k : ℕ⦄,
        (hi : i + 1 < V.length) →
        (hk : k < V.length) →
        k ≠ i →
        k ≠ i + 1 →
        V[k] ∉ openSegment ℝ V[i] V[i + 1] := by
    intro i k hi hk hki hki1
    exact avoid_from_segments V hV_nodup
      (by
        intro m n hm hn hmn
        exact hV_segment_intersections hm hn hmn)
      hi hk hki hki1
  let τ : PolygonalArc :=
    { vertices := V
      length_ge_two := hV_len
      source := c
      target := δ.target
      source_eq_head := hV_head
      target_eq_last := hV_last
      carrier := C
      relativeInterior := C \ ({c, δ.target} :
        Set (EuclideanSpace ℝ (Fin 2)))
      carrier_eq := rfl
      relativeInterior_eq := rfl
      simple_vertices := hV_nodup
      segment_intersections := by
        intro i k hi hk hik
        exact hV_segment_intersections hi hk hik
      vertices_avoid_nonincident_interiors := by
        intro i k hi hk hki hki1
        exact hV_vertices_avoid hi hk hki hki1 }
  have hτcarrier_subset : τ.carrier ⊆ δ.carrier := by
    intro p hp
    dsimp [τ, C] at hp
    rcases hp with ⟨i, hi, hpseg⟩
    by_cases hi0 : i = 0
    · subst i
      have hfirst_sub :
          segment ℝ V[0] V[0 + 1] ⊆
            segment ℝ δ.vertices[j] δ.vertices[j + 1] := by
        intro z hz
        have hcseg : c ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
          openSegment_subset_segment ℝ δ.vertices[j] δ.vertices[j + 1] hcOpen
        have hright : δ.vertices[j + 1] ∈
            segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
          right_mem_segment ℝ δ.vertices[j] δ.vertices[j + 1]
        have hz' : z ∈ segment ℝ c δ.vertices[j + 1] := by
          simpa [V] using hz
        exact (convex_segment δ.vertices[j] δ.vertices[j + 1]).segment_subset
          hcseg hright hz'
      rw [δ.carrier_eq]
      exact ⟨j, hj, hfirst_sub hpseg⟩
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hji1 : j + i + 1 < δ.vertices.length := by
        dsimp [V] at hi
        simp [List.length_drop] at hi
        omega
      have hOrig :
          p ∈ segment ℝ δ.vertices[j + i] δ.vertices[j + i + 1] := by
        have hVi := hV_get_pos i hipos (Nat.lt_of_succ_lt hi)
        have hVi1 := hV_get_pos (i + 1) (by omega) hi
        simpa [Nat.add_assoc, hVi, hVi1] using hpseg
      rw [δ.carrier_eq]
      exact ⟨j + i, hji1, hOrig⟩
  exact ⟨τ, rfl, rfl, rfl, hτcarrier_subset⟩

lemma ArcCrossingOrderedTailArc
    (K : Set (EuclideanSpace ℝ (Fin 2))) (δ : PolygonalArc)
    (α : PolygonalPath) (j : ℕ) (c : EuclideanSpace ℝ (Fin 2))
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hc_notα : c ∉ α.carrier)
    (hbefore :
      ∀ (i : ℕ) (hi : i + 1 < δ.vertices.length),
        i < j → Disjoint α.carrier (segment ℝ δ.vertices[i] δ.vertices[i + 1]))
    (hprefix_disjoint : Disjoint (segment ℝ δ.vertices[j] c) α.carrier)
    (hδverticesAvoid :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ δ.vertices → v ∉ α.carrier)
    (hδK :
      δ.carrier ∩ K = ({δ.source} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ τ : PolygonalArc,
      τ.vertices = c :: δ.vertices.drop (j + 1) ∧
        τ.source = c ∧
          τ.target = δ.target ∧
            τ.carrier ⊆ δ.carrier ∧
              α.carrier ∩ δ.carrier ⊆ τ.relativeInterior ∧
                Disjoint τ.carrier K := by
  rcases arcCrossingOrderedTailArc_construct δ j c hj hcOpen with
    ⟨τ, hτvertices, hτsource, hτtarget, hτcarrier_subset⟩
  let V : List (EuclideanSpace ℝ (Fin 2)) :=
      c :: δ.vertices.drop (j + 1)
  have hτverticesV : τ.vertices = V := by
      simpa [V] using hτvertices
  have hV_get_succ :
        ∀ n (hn : n + 1 < V.length),
          V[n + 1] = δ.vertices[j + 1 + n]'(by
            have hdrop : n < (δ.vertices.drop (j + 1)).length := by
              dsimp [V] at hn
              simpa using hn
            simp [List.length_drop] at hdrop
            omega) := by
      intro n hn
      have hdrop : n < (δ.vertices.drop (j + 1)).length := by
        dsimp [V] at hn
        simpa using hn
      dsimp [V]
      simpa using (List.getElem_drop (xs := δ.vertices) (i := j + 1)
        (j := n) (h := hdrop))
  have hV_get_pos :
        ∀ n (hnpos : 0 < n) (hn : n < V.length),
          V[n] = δ.vertices[j + n]'(by
            cases n with
            | zero => omega
            | succ q =>
                have hq : q + 1 < V.length := by simpa using hn
                have hdrop : q < (δ.vertices.drop (j + 1)).length := by
                  dsimp [V] at hq
                  simpa using hq
                simp [List.length_drop] at hdrop
                omega) := by
      intro n hnpos hn
      cases n with
      | zero => omega
      | succ q =>
          have hq : q + 1 < V.length := by simpa using hn
          have hidx : j + 1 + q = j + (q + 1) := by omega
          simpa [hidx] using hV_get_succ q hq
  have hc_ne_left : c ≠ δ.vertices[j] := by
      intro h
      have hleft : δ.vertices[j] ∈
          openSegment ℝ δ.vertices[j] δ.vertices[j + 1] := by
        simpa [h] using hcOpen
      have hne : δ.vertices[j] ≠ δ.vertices[j + 1] := by
        intro hEq
        have hidx : j = j + 1 :=
          (δ.simple_vertices.getElem_inj_iff
            (i := j) (j := j + 1)
            (hi := Nat.lt_of_succ_lt hj) (hj := hj)).1 hEq
        omega
      exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)
        (x := δ.vertices[j]) (y := δ.vertices[j + 1])).1 hleft)
  have hV_segment_pos :
        ∀ n (hn : n + 1 < V.length), 0 < n →
          segment ℝ V[n] V[n + 1] =
            segment ℝ (δ.vertices[j + n]'(by
              dsimp [V] at hn
              simp [List.length_drop] at hn
              omega))
              (δ.vertices[j + n + 1]'(by
                dsimp [V] at hn
                simp [List.length_drop] at hn
                omega)) := by
      intro n hn hnpos
      have hVn := hV_get_pos n hnpos (Nat.lt_of_succ_lt hn)
      have hVn1 := hV_get_pos (n + 1) (by omega) hn
      simpa [Nat.add_assoc, hVn, hVn1]
  have hV_len : 2 ≤ V.length := by
      dsimp [V]
      simp [List.length_drop]
      omega
  have hV_first_subset :
        segment ℝ V[0] V[1] ⊆
          segment ℝ δ.vertices[j] δ.vertices[j + 1] := by
      intro z hz
      have hcseg : c ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
        openSegment_subset_segment ℝ δ.vertices[j] δ.vertices[j + 1] hcOpen
      have hright : δ.vertices[j + 1] ∈
          segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
        right_mem_segment ℝ δ.vertices[j] δ.vertices[j + 1]
      have hV0 : V[0] = c := by simp [V]
      have hV1 : V[1] = δ.vertices[j + 1] := by
        simpa using hV_get_succ 0 (by
          dsimp [V]
          simp [List.length_drop]
          omega)
      have hz' : z ∈ segment ℝ c δ.vertices[j + 1] := by
        simpa [hV0, hV1] using hz
      exact (convex_segment δ.vertices[j] δ.vertices[j + 1]).segment_subset
        hcseg hright hz'
  refine ⟨τ, hτvertices, hτsource, hτtarget, hτcarrier_subset, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hpα, hpδ⟩
    rw [δ.carrier_eq] at hpδ
    rcases hpδ with ⟨m, hm, hpsegδ⟩
    rcases lt_trichotomy m j with hm_lt_j | hm_eq_j | hj_lt_m
    · have hdis := hbefore m hm hm_lt_j
      exact False.elim ((Set.disjoint_left.mp hdis hpα) hpsegδ)
    · subst m
      have hp_ne_left : p ≠ δ.vertices[j] := by
        intro hp_eq
        exact hδverticesAvoid δ.vertices[j]
          (List.getElem_mem (l := δ.vertices) (n := j)
            (Nat.lt_of_succ_lt hj)) (by simpa [hp_eq] using hpα)
      have hp_ne_right : p ≠ δ.vertices[j + 1] := by
        intro hp_eq
        exact hδverticesAvoid δ.vertices[j + 1]
          (List.getElem_mem (l := δ.vertices) (n := j + 1) hj)
          (by simpa [hp_eq] using hpα)
      have hpOpenδ :
          p ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1] :=
        mem_openSegment_of_ne_left_right (𝕜 := ℝ)
          hp_ne_left.symm hp_ne_right.symm hpsegδ
      have hp_not_prefix : p ∉ segment ℝ δ.vertices[j] c := by
        intro hprefix
        exact (Set.disjoint_left.mp hprefix_disjoint hprefix) hpα
      have hcRange :
          c ∈ Set.range
            (AffineMap.lineMap δ.vertices[j] δ.vertices[j + 1] : ℝ →ᵃ[ℝ]
              EuclideanSpace ℝ (Fin 2)) := by
        have hcseg : c ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
          openSegment_subset_segment ℝ δ.vertices[j] δ.vertices[j + 1]
            hcOpen
        rw [segment_eq_image_lineMap] at hcseg
        rcases hcseg with ⟨t, _ht, ht⟩
        exact ⟨t, ht⟩
      have hp_split :=
        openSegment_subset_union (𝕜 := ℝ) δ.vertices[j] δ.vertices[j + 1]
          hcRange hpOpenδ
      rcases hp_split with hp_eq_c | hp_left_or_right
      · exact False.elim (hc_notα (by simpa [hp_eq_c] using hpα))
      · rcases hp_left_or_right with hp_left | hp_right
        · have hprefix : p ∈ segment ℝ δ.vertices[j] c :=
            openSegment_subset_segment ℝ δ.vertices[j] c hp_left
          exact False.elim (hp_not_prefix hprefix)
        · refine PolygonalArcOpenSegmentSubsetRelativeInterior τ 0
            (by
              have hfirst : 0 + 1 < V.length := by omega
              simpa only [hτverticesV] using hfirst) ?_
          have hV0 : V[0] = c := by simp [V]
          have hV1 : V[1] = δ.vertices[j + 1] := by
            simpa using hV_get_succ 0 (by
              dsimp [V]
              simp [List.length_drop]
              omega)
          simpa only [hτverticesV, hV0, hV1, Nat.zero_add] using hp_right
    · let n := m - j
      have hn_pos : 0 < n := by
        dsimp [n]
        omega
      have hm_eq : m = j + n := by
        dsimp [n]
        omega
      have hn_V : n + 1 < V.length := by
        dsimp [V, n]
        simp [List.length_drop]
        omega
      have hn_tau : n + 1 < τ.vertices.length := by
        simpa [hτverticesV] using hn_V
      have hp_ne_left : p ≠ δ.vertices[m] := by
        intro hp_eq
        exact hδverticesAvoid δ.vertices[m]
          (List.getElem_mem (l := δ.vertices) (n := m)
            (Nat.lt_of_succ_lt hm)) (by simpa [hp_eq] using hpα)
      have hp_ne_right : p ≠ δ.vertices[m + 1] := by
        intro hp_eq
        exact hδverticesAvoid δ.vertices[m + 1]
          (List.getElem_mem (l := δ.vertices) (n := m + 1) hm)
          (by simpa [hp_eq] using hpα)
      have hpOpenδ : p ∈ openSegment ℝ δ.vertices[m] δ.vertices[m + 1] :=
        mem_openSegment_of_ne_left_right (𝕜 := ℝ)
          hp_ne_left.symm hp_ne_right.symm hpsegδ
      have htailOpen : p ∈ openSegment ℝ τ.vertices[n] τ.vertices[n + 1] := by
        have hVn := hV_get_pos n hn_pos (Nat.lt_of_succ_lt hn_V)
        have hVn1 := hV_get_pos (n + 1) (by omega) hn_V
        simpa only [hτverticesV, hm_eq, Nat.add_assoc, hVn, hVn1] using hpOpenδ
      exact PolygonalArcOpenSegmentSubsetRelativeInterior τ n hn_tau htailOpen
  · rw [Set.disjoint_left]
    have hsource0 : δ.vertices[0]'(by
        have hlen := δ.length_ge_two
        omega) = δ.source := by
      have hidx : 0 < δ.vertices.length := by
        have hlen := δ.length_ge_two
        omega
      have hhead := δ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem hidx] at hhead
      exact Option.some.inj hhead
    have hsource_mem_segment_iff_first :
        ∀ {m : ℕ} (hm : m + 1 < δ.vertices.length),
          δ.source ∈ segment ℝ δ.vertices[m] δ.vertices[m + 1] ↔ m = 0 := by
      intro m hm
      constructor
      · intro hmem
        by_contra hm0
        have h0lt : 0 < δ.vertices.length := by
          have hlen := δ.length_ge_two
          omega
        have hsource0' : δ.vertices[0] = δ.source := by
          simpa using hsource0
        have hm_lt : m < δ.vertices.length := by omega
        have hm1_lt : m + 1 < δ.vertices.length := hm
        have hleft_ne : δ.vertices[m] ≠ δ.source := by
          intro h
          have hidx : m = 0 :=
            (δ.simple_vertices.getElem_inj_iff
              (i := m) (j := 0) (hi := hm_lt) (hj := h0lt)).1
              (by rw [h, ← hsource0'])
          exact hm0 hidx
        have hright_ne : δ.vertices[m + 1] ≠ δ.source := by
          intro h
          have hidx : m + 1 = 0 :=
            (δ.simple_vertices.getElem_inj_iff
              (i := m + 1) (j := 0) (hi := hm1_lt) (hj := h0lt)).1
              (by rw [h, ← hsource0'])
          omega
        have hopen :
            δ.source ∈ openSegment ℝ δ.vertices[m] δ.vertices[m + 1] :=
          mem_openSegment_of_ne_left_right hleft_ne hright_ne hmem
        have hnot :=
          δ.vertices_avoid_nonincident_interiors hm h0lt
            (by omega : 0 ≠ m) (by omega : 0 ≠ m + 1)
        exact hnot (by simpa [hsource0'] using hopen)
      · intro hm0
        subst m
        have hsource0' : δ.vertices[0] = δ.source := by
          simpa using hsource0
        rw [← hsource0']
        exact left_mem_segment ℝ δ.vertices[0] δ.vertices[0 + 1]
    have hsource_not_tail : δ.source ∉ τ.carrier := by
      intro hsrcτ
      rw [τ.carrier_eq] at hsrcτ
      simp only [hτverticesV] at hsrcτ
      rcases hsrcτ with ⟨i, hi, hsegτ⟩
      change i + 1 < V.length at hi
      change δ.source ∈ segment ℝ V[i] V[i + 1] at hsegτ
      by_cases hi0 : i = 0
      · subst i
        have hsrc_orig : δ.source ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
          hV_first_subset hsegτ
        have hj0 : j = 0 := (hsource_mem_segment_iff_first hj).1 hsrc_orig
        have hV1 : V[1] = δ.vertices[j + 1] := by
          simpa using hV_get_succ 0 (by
            dsimp [V]
            simp [List.length_drop]
            omega)
        have hsrc_cseg : δ.source ∈ segment ℝ c δ.vertices[j + 1] := by
          simpa [V, hV1] using hsegτ
        have hcseg_source :
            c ∈ segment ℝ δ.source δ.vertices[j + 1] := by
          have hcseg : c ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
            openSegment_subset_segment ℝ δ.vertices[j] δ.vertices[j + 1]
              hcOpen
          simpa [hj0, hsource0] using hcseg
        have hdist1 := dist_add_dist_of_mem_segment hcseg_source
        have hdist2 := dist_add_dist_of_mem_segment hsrc_cseg
        have hsource_ne_c : δ.source ≠ c := by
          intro hsc
          exact hc_ne_left (by simpa [hj0, hsource0, hsc])
        have hpos : 0 < dist δ.source c := dist_pos.2 hsource_ne_c
        have hcomm : dist c δ.source = dist δ.source c := dist_comm c δ.source
        nlinarith
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
        have hsegi := hV_segment_pos i hi hipos
        have hi_orig : j + i + 1 < δ.vertices.length := by
          dsimp [V] at hi
          simp [List.length_drop] at hi
          omega
        have hsrc_orig :
            δ.source ∈ segment ℝ δ.vertices[j + i] δ.vertices[j + i + 1] := by
          simpa [hsegi] using hsegτ
        have hzero : j + i = 0 :=
          (hsource_mem_segment_iff_first hi_orig).1 hsrc_orig
        omega
    intro p hpτ hpK
    have hpδ : p ∈ δ.carrier := hτcarrier_subset hpτ
    have hp_inter : p ∈ δ.carrier ∩ K := ⟨hpδ, hpK⟩
    rw [hδK] at hp_inter
    have hp_source : p = δ.source := by simpa using hp_inter
    subst p
    exact hsource_not_tail hpτ
