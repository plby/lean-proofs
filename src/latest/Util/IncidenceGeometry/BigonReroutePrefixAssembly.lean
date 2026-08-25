import Util.IncidenceGeometry.EndpointSidePrefixAttachment
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentCertificates
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentTransfer
import Util.IncidenceGeometry.PolygonalArcFromEndpointGluedPieces

open Classical
noncomputable section

lemma BigonReroutePrefixAssembly
    (Aarc Barc BplusArc : PolygonalArc)
    (Rbeta H Bad DeltaX Qx : Set (EuclideanSpace ℝ (Fin 2)))
    (K : FinitePolygonalSet)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : EndpointSidePrefixAttachment Aarc Barc BplusArc
      Rbeta H Bad DeltaX Qx K XA)
    (hsource : Aarc.source = Barc.source)
    (htarget_not_A : BplusArc.target ∉ Aarc.carrier)
    (htarget_Rbeta : BplusArc.target ∈ Rbeta) :
    ∃ Bprefix : PolygonalArc,
      Bprefix.source = Aarc.source ∧
        Bprefix.target = BplusArc.target ∧
          Bprefix.carrier =
            ({z | ∃ i : ℕ, i ≤ E.r ∧ z ∈ (E.prefixPiece i).carrier} ∪
              E.terminalSide.carrier) ∪ E.terminalConnector.carrier ∧
            Bprefix.relativeInterior =
              Bprefix.carrier \ ({Aarc.source, BplusArc.target} : Set _) ∧
              Bprefix.carrier ∩ Aarc.carrier = ({Aarc.source} : Set _) ∧
                Bprefix.carrier ∩ (Barc.carrier ∪ BplusArc.carrier) =
                  ({Aarc.source, BplusArc.target} : Set _) ∧
                  Bprefix.carrier ∩ Rbeta = ({BplusArc.target} : Set _) ∧
                    Bprefix.relativeInterior ∩ H =
                      (E.xPrefix : Set (EuclideanSpace ℝ (Fin 2))) ∧
                      (∀ i : ℕ, i ≤ E.r →
                        (E.prefixPiece i).relativeInterior ⊆
                          Bprefix.relativeInterior) ∧
                        E.terminalSide.relativeInterior ⊆
                          Bprefix.relativeInterior ∧
                          E.terminalConnector.relativeInterior ⊆
                            Bprefix.relativeInterior ∧
                            (∀ i : ℕ, i ≤ E.r →
                              ∀ m (hm : m + 1 < (E.prefixPiece i).vertices.length),
                                ∃ j : ℕ, ∃ hj : j + 1 < Bprefix.vertices.length,
                                  ((Bprefix.vertices[j] =
                                      (E.prefixPiece i).vertices[m] ∧
                                    Bprefix.vertices[j + 1] =
                                      (E.prefixPiece i).vertices[m + 1]) ∨
                                   (Bprefix.vertices[j] =
                                      (E.prefixPiece i).vertices[m + 1] ∧
                                    Bprefix.vertices[j + 1] =
                                      (E.prefixPiece i).vertices[m]))) ∧
                              (∀ m (hm : m + 1 < E.terminalSide.vertices.length),
                                ∃ j : ℕ, ∃ hj : j + 1 < Bprefix.vertices.length,
                                  ((Bprefix.vertices[j] = E.terminalSide.vertices[m] ∧
                                    Bprefix.vertices[j + 1] =
                                      E.terminalSide.vertices[m + 1]) ∨
                                   (Bprefix.vertices[j] =
                                      E.terminalSide.vertices[m + 1] ∧
                                    Bprefix.vertices[j + 1] =
                                      E.terminalSide.vertices[m]))) ∧
                                (∀ m
                                  (hm : m + 1 < E.terminalConnector.vertices.length),
                                  ∃ j : ℕ, ∃ hj : j + 1 < Bprefix.vertices.length,
                                    ((Bprefix.vertices[j] =
                                        E.terminalConnector.vertices[m] ∧
                                      Bprefix.vertices[j + 1] =
                                        E.terminalConnector.vertices[m + 1]) ∨
                                     (Bprefix.vertices[j] =
                                        E.terminalConnector.vertices[m + 1] ∧
                                      Bprefix.vertices[j + 1] =
                                        E.terminalConnector.vertices[m]))) ∧
                                  ∀ j (hj : j + 1 < Bprefix.vertices.length),
                                    ∃ piece : PolygonalArc,
                                      ((∃ i : ℕ, i ≤ E.r ∧ piece = E.prefixPiece i) ∨
                                        piece = E.terminalSide ∨
                                        piece = E.terminalConnector) ∧
                                        ∃ m : ℕ,
                                          ∃ hm : m + 1 < piece.vertices.length,
                                            ((Bprefix.vertices[j] = piece.vertices[m] ∧
                                              Bprefix.vertices[j + 1] =
                                                piece.vertices[m + 1]) ∨
                                             (Bprefix.vertices[j] = piece.vertices[m + 1] ∧
                                              Bprefix.vertices[j + 1] =
                                                piece.vertices[m])) := by
  let pieces : List PolygonalArc :=
    (List.range (E.r + 1)).map E.prefixPiece ++
      [E.terminalSide, E.terminalConnector]
  have hpieces_length : pieces.length = E.r + 3 := by
    simp [pieces]
  have hprefix_length :
      ((List.range (E.r + 1)).map E.prefixPiece).length = E.r + 1 := by
    simp
  have hpiece_prefix : ∀ i (hi : i ≤ E.r), pieces[i] = E.prefixPiece i := by
    intro i hi
    rw [List.getElem_append_left (by rw [hprefix_length]; omega)]
    rw [List.getElem_map, List.getElem_range]
  have hpiece_side : pieces[E.r + 1] = E.terminalSide := by
    rw [List.getElem_append_right (by simpa [hprefix_length])]
    simp
  have hpiece_connector : pieces[E.r + 2] = E.terminalConnector := by
    rw [List.getElem_append_right (by rw [hprefix_length]; omega)]
    simp
  have hsuccessive :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source := by
    intro n hn
    have hnle : n ≤ E.r + 1 := by rw [hpieces_length] at hn; omega
    rcases Nat.lt_trichotomy n E.r with hlt | heq | hgt
    · rw [hpiece_prefix n (by omega), hpiece_prefix (n + 1) (by omega)]
      exact E.prefix_consecutive_sources n hlt
    · subst n
      rw [hpiece_prefix E.r le_rfl, hpiece_side]
      exact E.prefix_target
    · have heq : n = E.r + 1 := by omega
      subst n
      rw [hpiece_side, hpiece_connector]
      exact E.terminal_side_target.trans E.terminal_connector_source.symm
  have hsuccessive_intersections :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).carrier ∩ (pieces[n + 1]).carrier ⊆
          ({(pieces[n]).target} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro n hn
    have hnle : n ≤ E.r + 1 := by rw [hpieces_length] at hn; omega
    rcases Nat.lt_trichotomy n E.r with hlt | heq | hgt
    · rw [hpiece_prefix n (by omega), hpiece_prefix (n + 1) (by omega),
        E.prefix_consecutive_meets n hlt]
    · subst n
      rw [hpiece_prefix E.r le_rfl, hpiece_side,
        E.predecessor_meets_terminal]
      simpa [E.prefix_target]
    · have heq : n = E.r + 1 := by omega
      subst n
      rw [hpiece_side, hpiece_connector]
      intro z hz
      have hzQ : z ∈ E.terminalSide.carrier ∩ Qx :=
        ⟨hz.1, E.terminal_connector_subset_Q hz.2⟩
      rw [E.terminal_side_meets_Q] at hzQ
      simpa [E.terminal_side_target] using hzQ
  have hforward_disjoint :
      ∀ k l (hk : k < pieces.length) (hl : l < pieces.length),
        k + 1 < l → Disjoint (pieces[k]).carrier (pieces[l]).carrier := by
    intro k l hk hl hkl
    have hkbound : k ≤ E.r + 1 := by rw [hpieces_length] at hk; omega
    have hlbound : l ≤ E.r + 2 := by rw [hpieces_length] at hl; omega
    by_cases hlprefix : l ≤ E.r
    · rw [hpiece_prefix k (by omega), hpiece_prefix l hlprefix]
      exact E.prefix_nonconsecutive_disjoint k l (by omega) hlprefix hkl
    · by_cases hlside : l = E.r + 1
      · subst l
        rw [hpiece_prefix k (by omega), hpiece_side]
        exact E.earlier_prefix_disjoint_terminal k (by omega)
      · have hlconnector : l = E.r + 2 := by omega
        subst l
        by_cases hkprefix : k ≤ E.r
        · rw [hpiece_prefix k hkprefix, hpiece_connector]
          exact E.prefix_disjoint_terminal_connector k hkprefix
        · have hkside : k = E.r + 1 := by omega
          omega
  have hnon_successive :
      ∀ k l (hk : k < pieces.length) (hl : l < pieces.length),
        k + 1 < l ∨ l + 1 < k →
          Disjoint (pieces[k]).carrier (pieces[l]).carrier := by
    intro k l hk hl hkl
    rcases hkl with hkl | hlk
    · exact hforward_disjoint k l hk hl hkl
    · exact (hforward_disjoint l k hl hk hlk).symm
  have hsegmentCerts :=
    PolygonalArcEndpointGluedSegmentCertificates pieces hsuccessive
      hsuccessive_intersections hnon_successive
  have htransfer := PolygonalArcEndpointGluedSegmentTransfer pieces hsuccessive
  have hnondegenerate :
      ∀ i (hi : i + 1 < (PolygonalArcEndpointGluedVertices pieces).length),
        (PolygonalArcEndpointGluedVertices pieces)[i] ≠
          (PolygonalArcEndpointGluedVertices pieces)[i + 1] := by
    intro i hi heq
    rcases htransfer.2 i hi with ⟨piece, _hpiece, m, hm, hmatch | hmatch⟩
    · have hlocal : piece.vertices[m] = piece.vertices[m + 1] := by
        calc
          piece.vertices[m] = (PolygonalArcEndpointGluedVertices pieces)[i] :=
            hmatch.1.symm
          _ = (PolygonalArcEndpointGluedVertices pieces)[i + 1] := heq
          _ = piece.vertices[m + 1] := hmatch.2
      exact (Nat.ne_of_lt (by omega : m < m + 1))
        ((piece.simple_vertices.getElem_inj_iff
          (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 hlocal)
    · have hlocal : piece.vertices[m] = piece.vertices[m + 1] := by
        calc
          piece.vertices[m] = (PolygonalArcEndpointGluedVertices pieces)[i + 1] :=
            hmatch.2.symm
          _ = (PolygonalArcEndpointGluedVertices pieces)[i] := heq.symm
          _ = piece.vertices[m + 1] := hmatch.1
      exact (Nat.ne_of_lt (by omega : m < m + 1))
        ((piece.simple_vertices.getElem_inj_iff
          (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 hlocal)
  have arc_source_mem_carrier : ∀ Q : PolygonalArc, Q.source ∈ Q.carrier := by
    intro Q
    rw [Q.carrier_eq]
    have hlen := Q.length_ge_two
    refine ⟨0, by omega, ?_⟩
    have hzero : Q.vertices[0] = Q.source := by
      have hhead := Q.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    rw [hzero]
    exact left_mem_segment ℝ Q.source Q.vertices[1]
  have arc_target_mem_carrier : ∀ Q : PolygonalArc, Q.target ∈ Q.carrier := by
    intro Q
    rw [Q.carrier_eq]
    have hlen := Q.length_ge_two
    let m := Q.vertices.length - 2
    have hm : m + 1 < Q.vertices.length := by dsimp [m]; omega
    refine ⟨m, hm, ?_⟩
    have hlast : Q.vertices[m + 1] = Q.target := by
      have htarget := Q.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at htarget
      have hm_eq : m + 1 = Q.vertices.length - 1 := by dsimp [m]; omega
      simpa [hm_eq] using Option.some.inj htarget
    rw [hlast]
    exact right_mem_segment ℝ Q.vertices[m] Q.target
  have hpiece_mem : ∀ piece : PolygonalArc, piece ∈ pieces →
      ((∃ i : ℕ, i ≤ E.r ∧ piece = E.prefixPiece i) ∨
        piece = E.terminalSide ∨ piece = E.terminalConnector) := by
    intro piece hpiece
    simp only [pieces, List.mem_append, List.mem_map, List.mem_range,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hpiece
    rcases hpiece with ⟨i, hi, rfl⟩ | hpiece | hpiece
    · exact Or.inl ⟨i, by omega, rfl⟩
    · exact Or.inr (Or.inl hpiece)
    · exact Or.inr (Or.inr hpiece)
  have hpiece_avoids_endpoints : ∀ piece, piece ∈ pieces →
      Disjoint piece.relativeInterior
        ({Aarc.source, BplusArc.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro piece hpiece
    rcases hpiece_mem piece hpiece with ⟨i, hi, rfl⟩ | rfl | rfl
    · rw [Set.disjoint_left]
      intro z hz hzendpoint
      have hzinter := E.prefix_relative_interiors_avoid i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
      rcases hzendpoint with rfl | rfl
      · have hmem : Aarc.source ∈
            (E.prefixPiece i).relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) :=
          ⟨hz, Or.inl (Or.inl (Or.inl (Or.inl (arc_source_mem_carrier Aarc))))⟩
        rw [hzinter] at hmem
        exact hmem
      · have hmem : BplusArc.target ∈
            (E.prefixPiece i).relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) :=
          ⟨hz, Or.inl (Or.inl
            (Or.inr (arc_target_mem_carrier BplusArc)))⟩
        rw [hzinter] at hmem
        exact hmem
    · rw [Set.disjoint_left]
      intro z hz hzendpoint
      have hzinter := E.terminal_side_relativeInterior_avoid
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
      rcases hzendpoint with rfl | rfl
      · have hmem : Aarc.source ∈ E.terminalSide.relativeInterior ∩
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
          ⟨hz, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
            (arc_source_mem_carrier Aarc)))))⟩
        rw [hzinter] at hmem
        exact hmem
      · have hmem : BplusArc.target ∈ E.terminalSide.relativeInterior ∩
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
          ⟨hz, Or.inl (Or.inl (Or.inl (Or.inr
            (arc_target_mem_carrier BplusArc))))⟩
        rw [hzinter] at hmem
        exact hmem
    · rw [Set.disjoint_left]
      intro z hz hzendpoint
      have hzinter := E.terminal_connector_relativeInterior_avoid
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
      rcases hzendpoint with rfl | rfl
      · have hmem : Aarc.source ∈ E.terminalConnector.relativeInterior ∩
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
          ⟨hz, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
            (arc_source_mem_carrier Aarc)))))⟩
        rw [hzinter] at hmem
        exact hmem
      · have hmem : BplusArc.target ∈ E.terminalConnector.relativeInterior ∩
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
          ⟨hz, Or.inl (Or.inl (Or.inl
            (Or.inr (arc_target_mem_carrier BplusArc))))⟩
        rw [hzinter] at hmem
        exact hmem
  rcases PolygonalArcFromEndpointGluedPieces
      (pieces := pieces) (source := Aarc.source) (target := BplusArc.target)
      (hpieces := by simp [pieces])
      (first_source := by
        intro piece hhead
        have hzero : (0 : ℕ) ≤ E.r := Nat.zero_le _
        have hp0 : pieces[0]'(by rw [hpieces_length]; omega) = E.prefixPiece 0 :=
          hpiece_prefix 0 hzero
        have hhead' : pieces.head? = some pieces[0] := by
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by
            rw [hpieces_length]
            omega)]
        rw [hhead, Option.some.injEq] at hhead'
        subst piece
        rw [hp0]
        exact E.prefix_source)
      (last_target := by
        intro piece hlast
        have hlastSome : some E.terminalConnector = some piece := by
          simpa [pieces] using hlast
        have hlast' : E.terminalConnector = piece := Option.some.inj hlastSome
        subst piece
        exact E.terminal_connector_target)
      (successive_attach := hsuccessive)
      (glued_segment_endpoints_distinct := hnondegenerate)
      (adjacent_segment_intersections := hsegmentCerts.1)
      (nonadjacent_segment_disjoint := by
        intro i j hi hj hij
        exact hsegmentCerts.2 hi hj hij)
      (piece_relativeInterior_avoids_endpoints := hpiece_avoids_endpoints) with
    ⟨Bprefix, _hvertices, hBsource, hBtarget, hBcarrier, hBinterior,
      hpieceInterior, hpieceSegment, hsegmentPiece⟩
  have hcarrier : Bprefix.carrier =
      ({z | ∃ i : ℕ, i ≤ E.r ∧ z ∈ (E.prefixPiece i).carrier} ∪
        E.terminalSide.carrier) ∪ E.terminalConnector.carrier := by
    rw [hBcarrier]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union, pieces, List.mem_append,
      List.mem_map, List.mem_range, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨piece, (⟨i, hi, rfl⟩ | rfl | rfl), hz⟩
      · exact Or.inl (Or.inl ⟨i, by omega, hz⟩)
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
    · rintro ((⟨i, hi, hz⟩ | hz) | hz)
      · exact ⟨E.prefixPiece i, Or.inl ⟨i, by omega, rfl⟩, hz⟩
      · exact ⟨E.terminalSide, Or.inr (Or.inl rfl), hz⟩
      · exact ⟨E.terminalConnector, Or.inr (Or.inr rfl), hz⟩
  have arc_carrier_cases : ∀ (Q : PolygonalArc) z, z ∈ Q.carrier →
      z ∈ Q.relativeInterior ∨ z = Q.source ∨ z = Q.target := by
    intro Q z hz
    by_cases hend : z ∈ ({Q.source, Q.target} : Set _)
    · exact Or.inr (by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hend)
    · exact Or.inl (Q.relativeInterior_eq.symm ▸ ⟨hz, hend⟩)
  have hprefix_source_old_avoid : ∀ i, i ≤ E.r → i ≠ 0 →
      (E.prefixPiece i).source ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) := by
    intro i hi hi0 hz
    have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    let k := i - 1
    have hk : k < E.r := by dsimp [k]; omega
    have hki : k + 1 = i := by dsimp [k]; omega
    have hsource_eq : (E.prefixPiece i).source = (E.prefixPiece k).target := by
      simpa [hki] using (E.prefix_consecutive_sources k hk).symm
    exact E.prefix_internal_gates_avoid k hk (by simpa [hsource_eq] using hz)
  have hprefix_target_old_avoid : ∀ i, i ≤ E.r →
      (E.prefixPiece i).target ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) := by
    intro i hi hz
    by_cases hir : i = E.r
    · exact E.terminal_source_avoid (by simpa [hir, E.prefix_target] using hz)
    · exact E.prefix_internal_gates_avoid i (by omega) hz
  have hcarrier_A : Bprefix.carrier ∩ Aarc.carrier = ({Aarc.source} : Set _) := by
    ext z
    constructor
    · rintro ⟨hzB, hzA⟩
      rw [hcarrier] at hzB
      rcases hzB with ((⟨i, hi, hz⟩ | hz) | hz)
      · rcases arc_carrier_cases (E.prefixPiece i) z hz with hzri | hzsrc | hztgt
        · have hbad := E.prefix_relative_interiors_avoid i hi
          have : z ∈ (E.prefixPiece i).relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) :=
            ⟨hzri, Or.inl (Or.inl (Or.inl (Or.inl hzA)))⟩
          rw [hbad] at this
          exact this.elim
        · by_cases hi0 : i = 0
          · simpa [hzsrc, hi0, E.prefix_source]
          · exact (hprefix_source_old_avoid i hi hi0
              (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hzsrc ▸ hzA))))))).elim
        · exact (hprefix_target_old_avoid i hi
            (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hztgt ▸ hzA))))))).elim
      · rcases arc_carrier_cases E.terminalSide z hz with hzri | hzsrc | hztgt
        · have hbad := E.terminal_side_relativeInterior_avoid
          have : z ∈ E.terminalSide.relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
            ⟨hzri, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hzA))))⟩
          rw [hbad] at this
          exact this.elim
        · exact (E.terminal_source_avoid
            (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hzsrc ▸ hzA))))))).elim
        · exact (E.omega_avoid
            (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
              (E.terminal_side_target ▸ hztgt ▸ hzA))))))).elim
      · rcases arc_carrier_cases E.terminalConnector z hz with hzri | hzsrc | hztgt
        · have hbad := E.terminal_connector_relativeInterior_avoid
          have : z ∈ E.terminalConnector.relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
            ⟨hzri, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hzA))))⟩
          rw [hbad] at this
          exact this.elim
        · exact (E.omega_avoid
            (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
              (E.terminal_connector_source ▸ hzsrc ▸ hzA))))))).elim
        · exact (htarget_not_A (E.terminal_connector_target ▸ hztgt ▸ hzA)).elim
    · intro hz
      have hzEq : z = Aarc.source := by simpa using hz
      subst z
      refine ⟨?_, arc_source_mem_carrier Aarc⟩
      rw [hcarrier]
      left; left
      refine ⟨0, Nat.zero_le _, ?_⟩
      simpa [E.prefix_source] using arc_source_mem_carrier (E.prefixPiece 0)
  have hcarrier_B :
      Bprefix.carrier ∩ (Barc.carrier ∪ BplusArc.carrier) =
        ({Aarc.source, BplusArc.target} : Set _) := by
    ext z
    constructor
    · rintro ⟨hzB, hzOld⟩
      have hzOldFull : z ∈
          (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
            Rbeta ∪ H ∪ Bad) := by
        rcases hzOld with hzBarc | hzBplus
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hzBarc))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hzBplus)))
      rw [hcarrier] at hzB
      rcases hzB with ((⟨i, hi, hz⟩ | hz) | hz)
      · rcases arc_carrier_cases (E.prefixPiece i) z hz with hzri | hzsrc | hztgt
        · have hbad := E.prefix_relative_interiors_avoid i hi
          have hzOld' : z ∈
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) := by
            rcases hzOld with hzBarc | hzBplus
            · exact Or.inl (Or.inl (Or.inl (Or.inr hzBarc)))
            · exact Or.inl (Or.inl (Or.inr hzBplus))
          have : z ∈ (E.prefixPiece i).relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) :=
            ⟨hzri, hzOld'⟩
          rw [hbad] at this
          exact this.elim
        · by_cases hi0 : i = 0
          · simp [hzsrc, hi0, E.prefix_source]
          · have hzOld' : z ∈
                (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                  Rbeta ∪ H ∪ Bad) := by
              rcases hzOld with hzBarc | hzBplus
              · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hzBarc))))
              · exact Or.inl (Or.inl (Or.inl (Or.inr hzBplus)))
            exact (hprefix_source_old_avoid i hi hi0 (hzsrc ▸ hzOld')).elim
        · have hzOld' : z ∈
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H ∪ Bad) := by
            rcases hzOld with hzBarc | hzBplus
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hzBarc))))
            · exact Or.inl (Or.inl (Or.inl (Or.inr hzBplus)))
          exact (hprefix_target_old_avoid i hi (hztgt ▸ hzOld')).elim
      · rcases arc_carrier_cases E.terminalSide z hz with hzri | hzsrc | hztgt
        · have hbad := E.terminal_side_relativeInterior_avoid
          have hzOld' : z ∈
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) := by
            rcases hzOld with hzBarc | hzBplus
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hzBarc))))
            · exact Or.inl (Or.inl (Or.inl (Or.inr hzBplus)))
          have : z ∈ E.terminalSide.relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
            ⟨hzri, hzOld'⟩
          rw [hbad] at this
          exact this.elim
        · exact (E.terminal_source_avoid (hzsrc ▸ hzOldFull)).elim
        · exact (E.omega_avoid
            (E.terminal_side_target ▸ hztgt ▸ hzOldFull)).elim
      · rcases arc_carrier_cases E.terminalConnector z hz with hzri | hzsrc | hztgt
        · have hbad := E.terminal_connector_relativeInterior_avoid
          have hzOld' : z ∈
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) := by
            rcases hzOld with hzBarc | hzBplus
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hzBarc))))
            · exact Or.inl (Or.inl (Or.inl (Or.inr hzBplus)))
          have : z ∈ E.terminalConnector.relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
            ⟨hzri, hzOld'⟩
          rw [hbad] at this
          exact this.elim
        · exact (E.omega_avoid
            (E.terminal_connector_source ▸ hzsrc ▸ hzOldFull)).elim
        · simp [hztgt, E.terminal_connector_target]
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · refine ⟨?_, Or.inl ?_⟩
        · rw [hcarrier]
          left; left
          refine ⟨0, Nat.zero_le _, ?_⟩
          simpa [E.prefix_source] using arc_source_mem_carrier (E.prefixPiece 0)
        · rw [hsource]
          exact arc_source_mem_carrier Barc
      · refine ⟨?_, Or.inr (arc_target_mem_carrier BplusArc)⟩
        rw [hcarrier]
        right
        simpa [E.terminal_connector_target] using
          arc_target_mem_carrier E.terminalConnector
  have hcarrier_Rbeta :
      Bprefix.carrier ∩ Rbeta = ({BplusArc.target} : Set _) := by
    ext z
    constructor
    · rintro ⟨hzB, hzR⟩
      rw [hcarrier] at hzB
      rcases hzB with ((⟨i, hi, hz⟩ | hz) | hz)
      · rcases arc_carrier_cases (E.prefixPiece i) z hz with hzri | hzsrc | hztgt
        · have hbad := E.prefix_relative_interiors_avoid i hi
          have : z ∈ (E.prefixPiece i).relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) :=
            ⟨hzri, Or.inl (Or.inr hzR)⟩
          rw [hbad] at this
          exact this.elim
        · by_cases hi0 : i = 0
          · have hA : z ∈ Aarc.carrier := by
              simpa [hzsrc, hi0, E.prefix_source] using arc_source_mem_carrier Aarc
            exact (Set.disjoint_left.mp E.copied_prefix_disjoint_tail hA hzR).elim
          · exact (hprefix_source_old_avoid i hi hi0
              (hzsrc ▸ Or.inl (Or.inl (Or.inr hzR)))).elim
        · exact (hprefix_target_old_avoid i hi
            (hztgt ▸ Or.inl (Or.inl (Or.inr hzR)))).elim
      · rcases arc_carrier_cases E.terminalSide z hz with hzri | hzsrc | hztgt
        · have hbad := E.terminal_side_relativeInterior_avoid
          have : z ∈ E.terminalSide.relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
            ⟨hzri, Or.inl (Or.inl (Or.inr hzR))⟩
          rw [hbad] at this
          exact this.elim
        · exact (E.terminal_source_avoid
            (hzsrc ▸ Or.inl (Or.inl (Or.inr hzR)))).elim
        · exact (E.omega_avoid
            (E.terminal_side_target ▸ hztgt ▸
              Or.inl (Or.inl (Or.inr hzR)))).elim
      · rcases arc_carrier_cases E.terminalConnector z hz with hzri | hzsrc | hztgt
        · have hbad := E.terminal_connector_relativeInterior_avoid
          have : z ∈ E.terminalConnector.relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
            ⟨hzri, Or.inl (Or.inl (Or.inr hzR))⟩
          rw [hbad] at this
          exact this.elim
        · exact (E.omega_avoid
            (E.terminal_connector_source ▸ hzsrc ▸
              Or.inl (Or.inl (Or.inr hzR)))).elim
        · simpa [hztgt, E.terminal_connector_target]
    · intro hz
      have hzEq : z = BplusArc.target := by simpa using hz
      subst z
      refine ⟨?_, htarget_Rbeta⟩
      rw [hcarrier]
      right
      simpa [E.terminal_connector_target] using
        arc_target_mem_carrier E.terminalConnector
  have hinterH : Bprefix.relativeInterior ∩ H =
      (E.xPrefix : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext z
    constructor
    · rintro ⟨hzBri, hzH⟩
      have hzBcar : z ∈ Bprefix.carrier := by
        rw [Bprefix.relativeInterior_eq] at hzBri
        exact hzBri.1
      have hznotends : z ∉ ({Aarc.source, BplusArc.target} : Set _) := by
        rw [hBinterior] at hzBri
        exact hzBri.2
      rw [hcarrier] at hzBcar
      rcases hzBcar with ((⟨i, hi, hz⟩ | hz) | hz)
      · rcases arc_carrier_cases (E.prefixPiece i) z hz with hzri | hzsrc | hztgt
        · exact (E.xPrefix_spec z).2 ⟨⟨i, hi, hzri⟩, hzH⟩
        · by_cases hi0 : i = 0
          · exact (hznotends (by simp [hzsrc, hi0, E.prefix_source])).elim
          · exact (hprefix_source_old_avoid i hi hi0
              (hzsrc ▸ Or.inl (Or.inr hzH))).elim
        · exact (hprefix_target_old_avoid i hi
            (hztgt ▸ Or.inl (Or.inr hzH))).elim
      · rcases arc_carrier_cases E.terminalSide z hz with hzri | hzsrc | hztgt
        · have hbad := E.terminal_side_relativeInterior_avoid
          have : z ∈ E.terminalSide.relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
            ⟨hzri, Or.inl (Or.inr hzH)⟩
          rw [hbad] at this
          exact this.elim
        · exact (E.terminal_source_avoid
            (hzsrc ▸ Or.inl (Or.inr hzH))).elim
        · exact (E.omega_avoid
            (E.terminal_side_target ▸ hztgt ▸
              Or.inl (Or.inr hzH))).elim
      · rcases arc_carrier_cases E.terminalConnector z hz with hzri | hzsrc | hztgt
        · have hbad := E.terminal_connector_relativeInterior_avoid
          have : z ∈ E.terminalConnector.relativeInterior ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) :=
            ⟨hzri, Or.inl (Or.inr hzH)⟩
          rw [hbad] at this
          exact this.elim
        · exact (E.omega_avoid
            (E.terminal_connector_source ▸ hzsrc ▸
              Or.inl (Or.inr hzH))).elim
        · exact (hznotends (by
            simp [hztgt, E.terminal_connector_target])).elim
    · intro hzX
      have hspec := (E.xPrefix_spec z).1 hzX
      rcases hspec.1 with ⟨i, hi, hzri⟩
      refine ⟨hpieceInterior (E.prefixPiece i) ?_ hzri, hspec.2⟩
      simp only [pieces, List.mem_append, List.mem_map, List.mem_range,
        List.mem_cons, List.mem_singleton]
      exact Or.inl ⟨i, by omega, rfl⟩
  refine ⟨Bprefix, hBsource, hBtarget, hcarrier, ?_, hcarrier_A,
    hcarrier_B, hcarrier_Rbeta, hinterH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBcarrier]
    simpa [hBsource, hBtarget] using hBinterior
  · intro i hi
    apply hpieceInterior (E.prefixPiece i)
    simp only [pieces, List.mem_append, List.mem_map, List.mem_range,
      List.mem_cons, List.mem_singleton]
    exact Or.inl ⟨i, by omega, rfl⟩
  · apply hpieceInterior E.terminalSide
    simp [pieces]
  · apply hpieceInterior E.terminalConnector
    simp [pieces]
  · intro i hi m hm
    apply hpieceSegment (E.prefixPiece i)
    simp only [pieces, List.mem_append, List.mem_map, List.mem_range,
      List.mem_cons, List.mem_singleton]
    exact Or.inl ⟨i, by omega, rfl⟩
  · intro m hm
    exact hpieceSegment E.terminalSide (by simp [pieces]) m hm
  · intro m hm
    exact hpieceSegment E.terminalConnector (by simp [pieces]) m hm
  · intro j hj
    rcases hsegmentPiece j hj with ⟨piece, hpiece, m, hm, hmatch⟩
    exact ⟨piece, hpiece_mem piece hpiece, m, hm, hmatch⟩
