import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentOccurrence

open Classical
noncomputable section

lemma PolygonalArcEndpointGluedSegmentCertificates
    (pieces : List PolygonalArc)
    (successive_attach :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source)
    (successive_carrier_intersections_subset :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).carrier ∩ (pieces[n + 1]).carrier ⊆
          ({(pieces[n]).target} : Set (EuclideanSpace ℝ (Fin 2))))
    (non_successive_carrier_disjoint :
      ∀ k l (hk : k < pieces.length) (hl : l < pieces.length),
        k + 1 < l ∨ l + 1 < k →
          Disjoint (pieces[k]).carrier (pieces[l]).carrier) :
    (∀ i
      (hi : (i + 1) + 1 <
        (PolygonalArcEndpointGluedVertices pieces).length),
      (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i]
            (PolygonalArcEndpointGluedVertices pieces)[i + 1] ∩
          segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i + 1]
            (PolygonalArcEndpointGluedVertices pieces)[(i + 1) + 1]) =
        {(PolygonalArcEndpointGluedVertices pieces)[i + 1]}) ∧
    (∀ ⦃i j : ℕ⦄,
      (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length) →
      (hj : j + 1 < (PolygonalArcEndpointGluedVertices pieces).length) →
      i + 1 < j →
      Disjoint
        (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[i]
          (PolygonalArcEndpointGluedVertices pieces)[i + 1])
        (segment ℝ (PolygonalArcEndpointGluedVertices pieces)[j]
          (PolygonalArcEndpointGluedVertices pieces)[j + 1])) := by
  classical
  have polygonalArc_source_eq_first :
      ∀ Γ : PolygonalArc,
        Γ.vertices[0]'(by
          have hlen := Γ.length_ge_two
          omega) = Γ.source := by
    intro Γ
    have h0 : 0 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    have hhead := Γ.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem h0] at hhead
    exact Option.some.inj hhead
  have polygonalArc_target_eq_last :
      ∀ Γ : PolygonalArc,
        Γ.vertices[Γ.vertices.length - 1]'(by
          have hlen := Γ.length_ge_two
          omega) = Γ.target := by
    intro Γ
    have hlast_lt : Γ.vertices.length - 1 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    have hlast := Γ.target_eq_last
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getElem?_eq_getElem hlast_lt] at hlast
    exact Option.some.inj hlast
  have polygonalArc_source_mem_segment_iff_first :
      ∀ (Γ : PolygonalArc) {m : ℕ}
        (hm : m + 1 < Γ.vertices.length),
        Γ.source ∈ segment ℝ Γ.vertices[m] Γ.vertices[m + 1] ↔ m = 0 := by
    intro Γ m hm
    constructor
    · intro hmem
      by_contra hm0
      have h0lt : 0 < Γ.vertices.length := by
        have hlen := Γ.length_ge_two
        omega
      have hsource0 : Γ.vertices[0] = Γ.source := by
        have hhead := Γ.source_eq_head
        rw [List.head?_eq_getElem?] at hhead
        rw [List.getElem?_eq_getElem h0lt] at hhead
        exact Option.some.inj hhead
      have hm_lt : m < Γ.vertices.length := by omega
      have hm1_lt : m + 1 < Γ.vertices.length := hm
      have hleft_ne : Γ.vertices[m] ≠ Γ.source := by
        intro h
        have hidx : m = 0 :=
          (Γ.simple_vertices.getElem_inj_iff
            (i := m) (j := 0) (hi := hm_lt) (hj := h0lt)).1
            (by rw [h, ← hsource0])
        exact hm0 hidx
      have hright_ne : Γ.vertices[m + 1] ≠ Γ.source := by
        intro h
        have hidx : m + 1 = 0 :=
          (Γ.simple_vertices.getElem_inj_iff
            (i := m + 1) (j := 0) (hi := hm1_lt) (hj := h0lt)).1
            (by rw [h, ← hsource0])
        omega
      have hopen :
          Γ.source ∈ openSegment ℝ Γ.vertices[m] Γ.vertices[m + 1] :=
        mem_openSegment_of_ne_left_right hleft_ne hright_ne hmem
      have hnot :=
        Γ.vertices_avoid_nonincident_interiors hm h0lt
          (by omega : 0 ≠ m) (by omega : 0 ≠ m + 1)
      exact hnot (by simpa [hsource0] using hopen)
    · intro hm0
      subst m
      have h0 : 0 < Γ.vertices.length := by omega
      have hsource0 : Γ.vertices[0] = Γ.source := by
        have hhead := Γ.source_eq_head
        rw [List.head?_eq_getElem?] at hhead
        rw [List.getElem?_eq_getElem h0] at hhead
        exact Option.some.inj hhead
      rw [← hsource0]
      exact left_mem_segment ℝ Γ.vertices[0] Γ.vertices[0 + 1]
  have polygonalArc_target_mem_segment_iff_last :
      ∀ (Γ : PolygonalArc) {m : ℕ}
        (hm : m + 1 < Γ.vertices.length),
        Γ.target ∈ segment ℝ Γ.vertices[m] Γ.vertices[m + 1] ↔
          m + 1 = Γ.vertices.length - 1 := by
    intro Γ m hm
    constructor
    · intro hmem
      by_contra hmlast
      have hlast_lt : Γ.vertices.length - 1 < Γ.vertices.length := by
        have hlen := Γ.length_ge_two
        omega
      have htarget_last : Γ.vertices[Γ.vertices.length - 1] = Γ.target := by
        have hlast := Γ.target_eq_last
        rw [List.getLast?_eq_getElem?] at hlast
        rw [List.getElem?_eq_getElem hlast_lt] at hlast
        exact Option.some.inj hlast
      have hm_lt : m < Γ.vertices.length := by omega
      have hm1_lt : m + 1 < Γ.vertices.length := hm
      have hleft_ne : Γ.vertices[m] ≠ Γ.target := by
        intro h
        have hidx : m = Γ.vertices.length - 1 :=
          (Γ.simple_vertices.getElem_inj_iff
            (i := m) (j := Γ.vertices.length - 1)
            (hi := hm_lt) (hj := hlast_lt)).1
            (by rw [h, ← htarget_last])
        omega
      have hright_ne : Γ.vertices[m + 1] ≠ Γ.target := by
        intro h
        have hidx : m + 1 = Γ.vertices.length - 1 :=
          (Γ.simple_vertices.getElem_inj_iff
            (i := m + 1) (j := Γ.vertices.length - 1)
            (hi := hm1_lt) (hj := hlast_lt)).1
            (by rw [h, ← htarget_last])
        exact hmlast hidx
      have hopen :
          Γ.target ∈ openSegment ℝ Γ.vertices[m] Γ.vertices[m + 1] :=
        mem_openSegment_of_ne_left_right hleft_ne hright_ne hmem
      have hnot :=
        Γ.vertices_avoid_nonincident_interiors hm hlast_lt
          (by omega : Γ.vertices.length - 1 ≠ m)
          (by
            intro h
            exact hmlast h.symm)
      exact hnot (by simpa [htarget_last] using hopen)
    · intro hlast
      have hm1_lt : m + 1 < Γ.vertices.length := hm
      have hlast_lt : Γ.vertices.length - 1 < Γ.vertices.length := by
        have hlen := Γ.length_ge_two
        omega
      have htarget_last : Γ.vertices[Γ.vertices.length - 1] = Γ.target := by
        have hlast_get := Γ.target_eq_last
        rw [List.getLast?_eq_getElem?] at hlast_get
        rw [List.getElem?_eq_getElem hlast_lt] at hlast_get
        exact Option.some.inj hlast_get
      have hidx :
          (⟨m + 1, hm1_lt⟩ : Fin Γ.vertices.length) =
            ⟨Γ.vertices.length - 1, hlast_lt⟩ := by
        apply Fin.ext
        exact hlast
      have hget :
          Γ.vertices[m + 1] = Γ.vertices[Γ.vertices.length - 1] := by
        simpa using
          congrArg (fun q : Fin Γ.vertices.length => Γ.vertices[q]) hidx
      rw [← htarget_last, ← hget]
      exact right_mem_segment ℝ Γ.vertices[m] Γ.vertices[m + 1]
  have segment_subset_polygonalArc_carrier :
      ∀ (Γ : PolygonalArc) {m : ℕ}
        (hm : m + 1 < Γ.vertices.length),
        segment ℝ Γ.vertices[m] Γ.vertices[m + 1] ⊆ Γ.carrier := by
    intro Γ m hm p hp
    rw [Γ.carrier_eq]
    exact ⟨m, hm, hp⟩
  have disjoint_of_inter_eq_empty :
      ∀ {s t : Set (EuclideanSpace ℝ (Fin 2))},
        s ∩ t = ∅ → Disjoint s t := by
    intro s t h
    rw [Set.disjoint_left]
    intro x hs ht
    have hx : x ∈ s ∩ t := ⟨hs, ht⟩
    rw [h] at hx
    exact hx
  let W := PolygonalArcEndpointGluedVertices pieces
  let wt : PolygonalArc → ℕ := fun Γ => Γ.vertices.length - 1
  let pref : ℕ → ℕ := fun k => ((pieces.take k).map wt).sum
  have wt_pos : ∀ {k : ℕ} (hk : k < pieces.length),
      0 < wt (pieces[k]'hk) := by
    intro k hk
    dsimp [wt]
    have hlen := (pieces[k]).length_ge_two
    omega
  have pref_succ : ∀ {k : ℕ} (hk : k < pieces.length),
      pref (k + 1) = pref k + wt (pieces[k]'hk) := by
    intro k hk
    dsimp [pref]
    have hsum :=
      List.sum_take_succ (pieces.map wt) k (by
        simpa using hk)
    simpa [List.map_take] using hsum
  have pref_mono :
      ∀ {a b : ℕ}, a ≤ b → b ≤ pieces.length → pref a ≤ pref b := by
    intro a b hab
    induction hab with
    | refl =>
        intro _hb
        exact le_rfl
    | @step b hab ih =>
        intro hb
        have hb_lt : b < pieces.length := by omega
        have hstep :
            pref (b + 1) = pref b + wt (pieces[b]'hb_lt) := by
          exact pref_succ (k := b) hb_lt
        have hih : pref a ≤ pref b := ih (Nat.le_of_lt hb_lt)
        rw [hstep]
        exact Nat.le_trans hih (Nat.le_add_right _ _)
  have pref_strict :
      ∀ {a b : ℕ}, a < b → b ≤ pieces.length → pref a < pref b := by
    intro a b hab hb
    have ha : a < pieces.length := lt_of_lt_of_le hab hb
    have hsucc := pref_succ (k := a) ha
    have hmono : pref (a + 1) ≤ pref b :=
      pref_mono (Nat.succ_le_of_lt hab) hb
    have hpos : 0 < wt (pieces[a]'ha) := wt_pos ha
    rw [hsucc] at hmono
    omega
  have occ :=
    PolygonalArcEndpointGluedSegmentOccurrence pieces successive_attach
  have seg_occ :
      ∀ i (hi : i + 1 < W.length),
        ∃ k : ℕ, ∃ hk : k < pieces.length,
          ∃ m : ℕ, ∃ hm : m + 1 < (pieces[k]).vertices.length,
            i = pref k + m ∧
            W[i] = (pieces[k]).vertices[m] ∧
            W[i + 1] = (pieces[k]).vertices[m + 1] := by
    intro i hi
    rcases occ i (by simpa [W] using hi) with
      ⟨k, hk, m, hm, hidx, hleft, hright⟩
    refine ⟨k, hk, m, hm, ?_, ?_, ?_⟩
    · simpa [pref, wt] using hidx
    · simpa [W] using hleft
    · simpa [W] using hright
  have seg_subset_occ :
      ∀ {i k m : ℕ} (hi : i + 1 < W.length)
        (hk : k < pieces.length)
        (hm : m + 1 < (pieces[k]).vertices.length),
        W[i] = (pieces[k]).vertices[m] →
        W[i + 1] = (pieces[k]).vertices[m + 1] →
        segment ℝ W[i] W[i + 1] ⊆ (pieces[k]).carrier := by
    intro i k m hi hk hm hleft hright p hp
    rw [(pieces[k]).carrier_eq]
    exact ⟨m, hm, by simpa [hleft, hright] using hp⟩
  have occ_interval :
      ∀ {i k m : ℕ} (hk : k < pieces.length)
        (hm : m + 1 < (pieces[k]).vertices.length),
        i = pref k + m →
          pref k ≤ i ∧ i < pref (k + 1) := by
    intro i k m hk hm hidx
    have hm_wt : m < wt (pieces[k]'hk) := by
      dsimp [wt]
      have hlen := (pieces[k]).length_ge_two
      omega
    have hsucc := pref_succ (k := k) hk
    rw [hidx, hsucc]
    constructor <;> omega
  have occ_index_le_of_lt :
      ∀ {i j k l m n : ℕ}
        (hk : k < pieces.length) (hl : l < pieces.length)
        (hm : m + 1 < (pieces[k]).vertices.length)
        (hn : n + 1 < (pieces[l]).vertices.length),
        i = pref k + m → j = pref l + n → i < j → k ≤ l := by
    intro i j k l m n hk hl hm hn hidx hidx2 hij
    by_contra hnot
    have hlk : l < k := Nat.lt_of_not_ge hnot
    have hli : j < pref (l + 1) :=
      (occ_interval (i := j) (k := l) (m := n) hl hn hidx2).2
    have hmono : pref (l + 1) ≤ pref k :=
      pref_mono (Nat.succ_le_of_lt hlk) (Nat.le_of_lt hk)
    have hki : pref k ≤ i :=
      (occ_interval (i := i) (k := k) (m := m) hk hm hidx).1
    omega
  constructor
  · intro i hi
    have hiW : (i + 1) + 1 < W.length := by
      simpa [W] using hi
    have hi1 : i + 1 < W.length := by omega
    have hi2 : (i + 1) + 1 < W.length := hiW
    rcases seg_occ i hi1 with
      ⟨k, hk, m, hm, hidx, hleft, hright⟩
    rcases seg_occ (i + 1) hi2 with
      ⟨l, hl, n, hn, hidx2, hleft2, hright2⟩
    have hkl_le : k ≤ l :=
      occ_index_le_of_lt hk hl hm hn hidx hidx2 (by omega)
    rcases lt_or_eq_of_le hkl_le with hkl | hkl
    · have hkl_succ : l = k + 1 := by
        by_contra hne
        have hgap : k + 1 < l := by omega
        have hi_upper :
            i < pref (k + 1) :=
          (occ_interval (i := i) (k := k) (m := m) hk hm hidx).2
        have hi1_le : i + 1 ≤ pref (k + 1) := by omega
        have hpref_gap : pref (k + 1) < pref l :=
          pref_strict hgap (Nat.le_of_lt hl)
        have hl_lower :
            pref l ≤ i + 1 :=
          (occ_interval (i := i + 1) (k := l) (m := n) hl hn hidx2).1
        omega
      subst l
      have hk_succ : k + 1 < pieces.length := by simpa using hl
      have hm_wt : m < wt (pieces[k]'hk) := by
        dsimp [wt]
        have hlen := (pieces[k]).length_ge_two
        omega
      have hpref_succ := pref_succ (k := k) hk
      have hn_zero : n = 0 := by
        rw [hpref_succ] at hidx2
        omega
      have hm_last :
          m + 1 = (pieces[k]).vertices.length - 1 := by
        rw [hpref_succ] at hidx2
        dsimp [wt] at hidx2
        omega
      have hshared :
          W[i + 1] = (pieces[k]).target := by
        have hlast :
            (pieces[k]).vertices[(pieces[k]).vertices.length - 1] =
              (pieces[k]).target :=
          polygonalArc_target_eq_last (pieces[k])
        have hlast_lt :
            (pieces[k]).vertices.length - 1 < (pieces[k]).vertices.length := by
          have hlen := (pieces[k]).length_ge_two
          omega
        have hidx_last :
            (⟨m + 1, hm⟩ : Fin (pieces[k]).vertices.length) =
              ⟨(pieces[k]).vertices.length - 1, hlast_lt⟩ := by
          apply Fin.ext
          exact hm_last
        have hget :
            (pieces[k]).vertices[m + 1] =
              (pieces[k]).vertices[(pieces[k]).vertices.length - 1] := by
          simpa using
            congrArg
              (fun q : Fin (pieces[k]).vertices.length =>
                (pieces[k]).vertices[q]) hidx_last
        exact hright.trans (hget.trans hlast)
      apply Set.Subset.antisymm
      · intro p hp
        have hp_car :
            p ∈ (pieces[k]).carrier ∩ (pieces[k + 1]).carrier := by
          exact
            ⟨seg_subset_occ hi1 hk hm hleft hright hp.1,
              seg_subset_occ hi2 hk_succ hn hleft2 hright2 hp.2⟩
        have hp_target :=
          successive_carrier_intersections_subset k hk_succ hp_car
        rw [Set.mem_singleton_iff] at hp_target ⊢
        exact hp_target.trans hshared.symm
      · intro p hp
        rw [Set.mem_singleton_iff] at hp
        subst p
        exact ⟨right_mem_segment ℝ W[i] W[i + 1],
          left_mem_segment ℝ W[i + 1] W[(i + 1) + 1]⟩
    · subst l
      have hn_eq : n = m + 1 := by omega
      subst n
      have hlocal :=
        (pieces[k]).segment_intersections
          (i := m) (j := m + 1) hm hn (by omega)
      have hlocal' :
          (segment ℝ (pieces[k]).vertices[m]
                (pieces[k]).vertices[m + 1] ∩
              segment ℝ (pieces[k]).vertices[m + 1]
                (pieces[k]).vertices[(m + 1) + 1]) =
            {(pieces[k]).vertices[m + 1]} := by
        simpa using hlocal
      simpa [← hleft, ← hright, ← hleft2, ← hright2] using hlocal'
  · intro i j hi hj hij
    rcases seg_occ i hi with
      ⟨k, hk, m, hm, hidx, hleft, hright⟩
    rcases seg_occ j hj with
      ⟨l, hl, n, hn, hidx2, hleft2, hright2⟩
    have hkl_le : k ≤ l :=
      occ_index_le_of_lt hk hl hm hn hidx hidx2 (by omega)
    rcases lt_or_eq_of_le hkl_le with hkl | hkl
    · by_cases hsucc : l = k + 1
      · subst l
        have hk_succ : k + 1 < pieces.length := by simpa using hl
        rw [Set.disjoint_left]
        intro p hp_i hp_j
        have hp_car :
            p ∈ (pieces[k]).carrier ∩ (pieces[k + 1]).carrier := by
          exact
            ⟨seg_subset_occ hi hk hm hleft hright hp_i,
              seg_subset_occ hj hk_succ hn hleft2 hright2 hp_j⟩
        have hp_target_mem :=
          successive_carrier_intersections_subset k hk_succ hp_car
        have hp_eq_target : p = (pieces[k]).target := by
          simpa using hp_target_mem
        have htarget_mem :
            (pieces[k]).target ∈
              segment ℝ (pieces[k]).vertices[m]
                (pieces[k]).vertices[m + 1] := by
          simpa [← hleft, ← hright, hp_eq_target] using hp_i
        have hm_last :
            m + 1 = (pieces[k]).vertices.length - 1 :=
          (polygonalArc_target_mem_segment_iff_last (pieces[k]) hm).1
            htarget_mem
        have hattach :
            (pieces[k]).target = (pieces[k + 1]).source :=
          successive_attach k hk_succ
        have hsource_mem :
            (pieces[k + 1]).source ∈
              segment ℝ (pieces[k + 1]).vertices[n]
                (pieces[k + 1]).vertices[n + 1] := by
          have hp_eq_source : p = (pieces[k + 1]).source := by
            rw [hp_eq_target, hattach]
          simpa [← hleft2, ← hright2, hp_eq_source] using hp_j
        have hn_zero : n = 0 :=
          (polygonalArc_source_mem_segment_iff_first (pieces[k + 1]) hn).1
            hsource_mem
        have hpref_succ := pref_succ (k := k) hk
        have hm_wt : m + 1 = wt (pieces[k]'hk) := by
          dsimp [wt]
          exact hm_last
        rw [hpref_succ] at hidx2
        omega
      · have hgap : k + 1 < l := by omega
        have hdis :=
          non_successive_carrier_disjoint k l hk hl (Or.inl hgap)
        rw [Set.disjoint_left]
        intro p hp_i hp_j
        exact
          (Set.disjoint_left.mp hdis
            (seg_subset_occ hi hk hm hleft hright hp_i))
            (seg_subset_occ hj hl hn hleft2 hright2 hp_j)
    · subst l
      have hmn_gap : m + 1 < n := by omega
      have hlocal :=
        (pieces[k]).segment_intersections
          (i := m) (j := n) hm hn (by omega)
      have hnonadj : n ≠ m + 1 := by omega
      have hlocal_empty :
          (segment ℝ (pieces[k]).vertices[m]
                (pieces[k]).vertices[m + 1] ∩
              segment ℝ (pieces[k]).vertices[n]
                (pieces[k]).vertices[n + 1]) = ∅ := by
        simpa [hnonadj] using hlocal
      simpa [← hleft, ← hright, ← hleft2, ← hright2] using
        disjoint_of_inter_eq_empty hlocal_empty
