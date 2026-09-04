import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentCertificates
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentTransfer
import Util.IncidenceGeometry.PolygonalArcFromEndpointGluedPieces
import Util.IncidenceGeometry.StraightSegmentPolygonalArc

open Classical
noncomputable section

lemma EndpointSidePrefixTerminalChain
    (predecessor approach : PolygonalArc)
    (lastGate h terminalGate : EuclideanSpace ℝ (Fin 2)) :
    predecessor.target = lastGate →
      approach.source = lastGate →
        predecessor.carrier ∩ approach.carrier =
          ({lastGate} : Set (EuclideanSpace ℝ (Fin 2))) →
          approach.target = h →
            approach.carrier ∩ segment ℝ h terminalGate =
              ({h} : Set (EuclideanSpace ℝ (Fin 2))) →
              Disjoint predecessor.carrier (segment ℝ h terminalGate) →
                h ≠ terminalGate →
                  ∃ terminalSegment chain : PolygonalArc,
                    terminalSegment.source = h ∧
                      terminalSegment.target = terminalGate ∧
                        terminalSegment.carrier = segment ℝ h terminalGate ∧
                          terminalSegment.relativeInterior =
                            openSegment ℝ h terminalGate ∧
                            approach.carrier ∩ terminalSegment.carrier =
                              ({h} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                              Disjoint predecessor.carrier terminalSegment.carrier ∧
                                chain.vertices =
                                  PolygonalArcEndpointGluedVertices
                                    [predecessor, approach, terminalSegment] ∧
                                  chain.source = predecessor.source ∧
                                    chain.target = terminalGate ∧
                                      chain.carrier =
                                        predecessor.carrier ∪ approach.carrier ∪
                                          terminalSegment.carrier ∧
                                        chain.relativeInterior =
                                          (predecessor.carrier ∪ approach.carrier ∪
                                              terminalSegment.carrier) \
                                            ({predecessor.source, terminalGate} :
                                              Set (EuclideanSpace ℝ (Fin 2))) ∧
                                          predecessor.relativeInterior ⊆
                                            chain.relativeInterior ∧
                                            approach.relativeInterior ⊆
                                              chain.relativeInterior ∧
                                              terminalSegment.relativeInterior ⊆
                                                chain.relativeInterior ∧
                                                ∀ piece : PolygonalArc,
                                                  piece ∈
                                                      [predecessor, approach,
                                                        terminalSegment] →
                                                    ∀ z m
                                                      (hm : m + 1 <
                                                        piece.vertices.length),
                                                      z ∈ openSegment ℝ
                                                          piece.vertices[m]
                                                          piece.vertices[m + 1] →
                                                        ∃ i : ℕ,
                                                          ∃ hi : i + 1 <
                                                              chain.vertices.length,
                                                            z ∈ openSegment ℝ
                                                                chain.vertices[i]
                                                                chain.vertices[i + 1] ∧
                                                              ∃ c : ℝ, c ≠ 0 ∧
                                                                chain.vertices[i + 1] -
                                                                    chain.vertices[i] =
                                                                  c •
                                                                    (piece.vertices[m + 1] -
                                                                      piece.vertices[m]) := by
  intro hpredecessor_target happ_source hpredecessor_approach
    happ_target happ_segment hpredecessor_segment hne
  rcases StraightSegmentPolygonalArc h terminalGate hne with
    ⟨terminalSegment, hterminal_source, hterminal_target,
      hterminal_carrier, hterminal_interior⟩
  let pieces : List PolygonalArc := [predecessor, approach, terminalSegment]
  have happ_terminal :
      approach.carrier ∩ terminalSegment.carrier =
        ({h} : Set (EuclideanSpace ℝ (Fin 2))) := by
    simpa [hterminal_carrier] using happ_segment
  have hpredecessor_terminal :
      Disjoint predecessor.carrier terminalSegment.carrier := by
    simpa [hterminal_carrier] using hpredecessor_segment
  have hsuccessive :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source := by
    intro n hn
    have hn_cases : n = 0 ∨ n = 1 := by
      simp [pieces] at hn
      omega
    rcases hn_cases with rfl | rfl
    · simpa [pieces, hpredecessor_target] using happ_source.symm
    · simpa [pieces] using happ_target.trans hterminal_source.symm
  have hsegmentCerts :=
    PolygonalArcEndpointGluedSegmentCertificates pieces hsuccessive
      (by
        intro n hn
        have hn_cases : n = 0 ∨ n = 1 := by
          simp [pieces] at hn
          omega
        rcases hn_cases with rfl | rfl
        · intro z hz
          change z ∈ predecessor.carrier ∩ approach.carrier at hz
          change z ∈ ({predecessor.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
          rw [hpredecessor_approach] at hz
          simpa [hpredecessor_target] using hz
        · intro z hz
          change z ∈ approach.carrier ∩ terminalSegment.carrier at hz
          change z ∈ ({approach.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
          rw [happ_terminal] at hz
          simpa [happ_target] using hz)
      (by
        intro k l hk hl hkl
        simp [pieces] at hk hl
        have hcases : (k = 0 ∧ l = 2) ∨ (k = 2 ∧ l = 0) := by
          omega
        rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [pieces] using hpredecessor_terminal
        · simpa [pieces] using hpredecessor_terminal.symm)
  have arc_source_ne_target :
      ∀ Q : PolygonalArc, Q.source ≠ Q.target := by
    intro Q
    have hlen := Q.length_ge_two
    have hzero : Q.vertices[0]'(by omega) = Q.source := by
      have hhead := Q.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    have hlast :
        Q.vertices[Q.vertices.length - 1]'(by omega) = Q.target := by
      have htarget := Q.target_eq_last
      rw [List.getLast?_eq_getElem?] at htarget
      rw [List.getElem?_eq_getElem (by omega)] at htarget
      exact Option.some.inj htarget
    intro hsource_target
    have hidx : 0 = Q.vertices.length - 1 :=
      (Q.simple_vertices.getElem_inj_iff).mp (by
        rw [hzero, hlast, hsource_target])
    omega
  have arc_source_mem_carrier :
      ∀ Q : PolygonalArc, Q.source ∈ Q.carrier := by
    intro Q
    have hlen := Q.length_ge_two
    rw [Q.carrier_eq]
    refine ⟨0, by omega, ?_⟩
    have hzero : Q.vertices[0]'(by omega) = Q.source := by
      have hhead := Q.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    rw [hzero]
    exact left_mem_segment ℝ Q.source Q.vertices[1]
  have arc_target_mem_carrier :
      ∀ Q : PolygonalArc, Q.target ∈ Q.carrier := by
    intro Q
    have hlen := Q.length_ge_two
    rw [Q.carrier_eq]
    let m := Q.vertices.length - 2
    have hm : m + 1 < Q.vertices.length := by
      dsimp [m]
      omega
    refine ⟨m, hm, ?_⟩
    have hlast : Q.vertices[m + 1] = Q.target := by
      have htarget := Q.target_eq_last
      rw [List.getLast?_eq_getElem?] at htarget
      have hidx : Q.vertices.length - 1 < Q.vertices.length := by omega
      rw [List.getElem?_eq_getElem hidx] at htarget
      have hm_eq : m + 1 = Q.vertices.length - 1 := by
        dsimp [m]
        omega
      simpa [hm_eq] using Option.some.inj htarget
    rw [hlast]
    exact right_mem_segment ℝ Q.vertices[m] Q.target
  have hpiece_avoids :
      ∀ Q, Q ∈ pieces →
        Disjoint Q.relativeInterior
          ({predecessor.source, terminalGate} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
    intro Q hQ
    simp only [pieces, List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with hQ | hQ | hQ
    · subst Q
      rw [Set.disjoint_left]
      intro z hz hzendpoint
      have hz_not_own :
          z ∉ ({predecessor.source, predecessor.target} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
        have hz' := hz
        rw [predecessor.relativeInterior_eq] at hz'
        exact hz'.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
      rcases hzendpoint with hzsource | hzterminal
      · subst z
        exact hz_not_own (by simp)
      · subst z
        have hzcarrier : terminalGate ∈ predecessor.carrier := by
          have hz' := hz
          rw [predecessor.relativeInterior_eq] at hz'
          exact hz'.1
        exact (Set.disjoint_left.mp hpredecessor_terminal hzcarrier)
          (by simpa [hterminal_target] using arc_target_mem_carrier terminalSegment)
    · subst Q
      rw [Set.disjoint_left]
      intro z hz hzendpoint
      have hzcarrier : z ∈ approach.carrier := by
        have hz' := hz
        rw [approach.relativeInterior_eq] at hz'
        exact hz'.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
      rcases hzendpoint with hzsource | hzterminal
      · subst z
        have hinter : predecessor.source ∈
            predecessor.carrier ∩ approach.carrier :=
          ⟨arc_source_mem_carrier predecessor, hzcarrier⟩
        rw [hpredecessor_approach] at hinter
        have heq : predecessor.source = predecessor.target := by
          simpa [hpredecessor_target] using hinter
        exact arc_source_ne_target predecessor heq
      · subst z
        have hinter : terminalGate ∈
            approach.carrier ∩ terminalSegment.carrier :=
          ⟨hzcarrier, by
            simpa [hterminal_target] using arc_target_mem_carrier terminalSegment⟩
        rw [happ_terminal] at hinter
        exact hne (by simpa using hinter.symm)
    · subst Q
      rw [Set.disjoint_left]
      intro z hz hzendpoint
      have hz_not_own :
          z ∉ ({terminalSegment.source, terminalSegment.target} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
        have hz' := hz
        rw [terminalSegment.relativeInterior_eq] at hz'
        exact hz'.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzendpoint
      rcases hzendpoint with hzsource | hzterminal
      · subst z
        have hzcarrier : predecessor.source ∈ terminalSegment.carrier := by
          have hz' := hz
          rw [terminalSegment.relativeInterior_eq] at hz'
          exact hz'.1
        exact (Set.disjoint_left.mp hpredecessor_terminal
          (arc_source_mem_carrier predecessor)) hzcarrier
      · subst z
        exact hz_not_own (by simp [hterminal_target])
  have htransfer :=
    PolygonalArcEndpointGluedSegmentTransfer pieces hsuccessive
  rcases PolygonalArcFromEndpointGluedPieces
      (pieces := pieces) (source := predecessor.source) (target := terminalGate)
      (hpieces := by simp [pieces])
      (first_source := by
        intro Q hQ
        simp [pieces] at hQ
        subst Q
        rfl)
      (last_target := by
        intro Q hQ
        simp [pieces] at hQ
        subst Q
        exact hterminal_target)
      (successive_attach := hsuccessive)
      (glued_segment_endpoints_distinct := by
        intro i hi
        rcases htransfer.2 i hi with
          ⟨piece, _hpiece, m, hm, hmatch | hmatch⟩
        · intro hglued
          have hlocal : piece.vertices[m] = piece.vertices[m + 1] := by
            calc
              piece.vertices[m] =
                  (PolygonalArcEndpointGluedVertices pieces)[i] := hmatch.1.symm
              _ = (PolygonalArcEndpointGluedVertices pieces)[i + 1] := hglued
              _ = piece.vertices[m + 1] := hmatch.2
          exact (Nat.ne_of_lt (by omega : m < m + 1))
            ((piece.simple_vertices.getElem_inj_iff
              (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 hlocal)
        · intro hglued
          have hlocal : piece.vertices[m] = piece.vertices[m + 1] := by
            calc
              piece.vertices[m] =
                  (PolygonalArcEndpointGluedVertices pieces)[i + 1] := hmatch.2.symm
              _ = (PolygonalArcEndpointGluedVertices pieces)[i] := hglued.symm
              _ = piece.vertices[m + 1] := hmatch.1
          exact (Nat.ne_of_lt (by omega : m < m + 1))
            ((piece.simple_vertices.getElem_inj_iff
              (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 hlocal))
      (adjacent_segment_intersections := hsegmentCerts.1)
      (nonadjacent_segment_disjoint := by
        intro i j hi hj hij
        exact hsegmentCerts.2 hi hj hij)
      (piece_relativeInterior_avoids_endpoints := hpiece_avoids) with
    ⟨chain, hvertices, hchain_source, hchain_target, hchain_carrier,
      hchain_interior, hpiece_interior, hpiece_segment, _hsegment_piece⟩
  refine ⟨terminalSegment, chain, hterminal_source, hterminal_target,
    hterminal_carrier, hterminal_interior, happ_terminal,
    hpredecessor_terminal, ?_, hchain_source, hchain_target, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simpa [pieces] using hvertices
  · rw [hchain_carrier]
    ext z
    simp [pieces, or_assoc]
  · rw [hchain_interior]
    ext z
    simp [pieces, or_assoc]
  · exact hpiece_interior predecessor (by simp [pieces])
  · exact hpiece_interior approach (by simp [pieces])
  · exact hpiece_interior terminalSegment (by simp [pieces])
  · intro piece hpiece z m hm hz
    rcases hpiece_segment piece (by simpa [pieces] using hpiece) m hm with
      ⟨i, hi, hforward | hreverse⟩
    · refine ⟨i, hi, ?_, 1, one_ne_zero, ?_⟩
      · simpa [hforward.1, hforward.2] using hz
      · simp [hforward.1, hforward.2]
    · refine ⟨i, hi, ?_, -1, neg_ne_zero.mpr one_ne_zero, ?_⟩
      · simpa [hreverse.1, hreverse.2, openSegment_symm] using hz
      · simp [hreverse.1, hreverse.2]
