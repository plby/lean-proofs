import Util.IncidenceGeometry.BigonRerouteOrderedBetaTailData
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentCertificates
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentTransfer
import Util.IncidenceGeometry.PolygonalArcFromEndpointGluedPieces

open Classical
noncomputable section

lemma BigonRerouteBetaSpliceAssembly
    {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (beta : G.edgeFinset) (u : V)
    (y : EuclideanSpace ℝ (Fin 2))
    (B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (Tail : BigonRerouteOrderedBetaTailData G D beta u y B Bplus Rbeta H)
    (Bprefix : PolygonalArc)
    (hprefix_source : Bprefix.source = D.vertexPlacement u)
    (hprefix_target : Bprefix.target = y)
    (hprefix_tail : Bprefix.carrier ∩ Tail.tailArc.carrier = ({y} : Set _)) :
    ∃ betaArcNew : PolygonalArc,
      ∃ edgeArcNew : G.edgeFinset → PolygonalArc,
        betaArcNew.source = D.vertexPlacement u ∧
          betaArcNew.target = D.vertexPlacement Tail.farEndpoint ∧
            betaArcNew.carrier = Bprefix.carrier ∪ Tail.tailArc.carrier ∧
              betaArcNew.relativeInterior =
                (Bprefix.carrier ∪ Tail.tailArc.carrier) \
                  ({D.vertexPlacement u, D.vertexPlacement Tail.farEndpoint} : Set _) ∧
                Bprefix.relativeInterior ⊆ betaArcNew.relativeInterior ∧
                  Tail.tailArc.relativeInterior ⊆ betaArcNew.relativeInterior ∧
                    Bprefix.carrier ⊆ betaArcNew.carrier ∧
                      Tail.tailArc.carrier ⊆ betaArcNew.carrier ∧
                        edgeArcNew beta = betaArcNew ∧
                          (∀ e : G.edgeFinset, e ≠ beta →
                            edgeArcNew e = D.edgeArc e) ∧
                            (∀ e : G.edgeFinset,
                              ∃ a b : V,
                                G.Adj a b ∧ e.1 = Sym2.mk a b ∧
                                  (((edgeArcNew e).source = D.vertexPlacement a ∧
                                      (edgeArcNew e).target = D.vertexPlacement b) ∨
                                    ((edgeArcNew e).source = D.vertexPlacement b ∧
                                      (edgeArcNew e).target = D.vertexPlacement a))) ∧
                              (∀ m (hm : m + 1 < Bprefix.vertices.length),
                                ∃ j : ℕ, ∃ hj : j + 1 < betaArcNew.vertices.length,
                                  ((betaArcNew.vertices[j] = Bprefix.vertices[m] ∧
                                    betaArcNew.vertices[j + 1] = Bprefix.vertices[m + 1]) ∨
                                   (betaArcNew.vertices[j] = Bprefix.vertices[m + 1] ∧
                                    betaArcNew.vertices[j + 1] = Bprefix.vertices[m]))) ∧
                                (∀ m (hm : m + 1 < Tail.tailArc.vertices.length),
                                  ∃ j : ℕ, ∃ hj : j + 1 < betaArcNew.vertices.length,
                                    ((betaArcNew.vertices[j] = Tail.tailArc.vertices[m] ∧
                                      betaArcNew.vertices[j + 1] =
                                        Tail.tailArc.vertices[m + 1]) ∨
                                     (betaArcNew.vertices[j] =
                                        Tail.tailArc.vertices[m + 1] ∧
                                      betaArcNew.vertices[j + 1] = Tail.tailArc.vertices[m]))) ∧
                                  ∀ j (hj : j + 1 < betaArcNew.vertices.length),
                                    ∃ piece : PolygonalArc,
                                      (piece = Bprefix ∨ piece = Tail.tailArc) ∧
                                        ∃ m : ℕ,
                                          ∃ hm : m + 1 < piece.vertices.length,
                                            ((betaArcNew.vertices[j] = piece.vertices[m] ∧
                                              betaArcNew.vertices[j + 1] =
                                                piece.vertices[m + 1]) ∨
                                             (betaArcNew.vertices[j] = piece.vertices[m + 1] ∧
                                              betaArcNew.vertices[j + 1] =
                                                piece.vertices[m])) := by
  let pieces : List PolygonalArc := [Bprefix, Tail.tailArc]
  have hsuccessive :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source := by
    intro n hn
    have hn0 : n = 0 := by simp [pieces] at hn; omega
    subst n
    simpa [pieces, hprefix_target] using Tail.source_eq.symm
  have hsegmentCerts :=
    PolygonalArcEndpointGluedSegmentCertificates pieces hsuccessive
      (by
        intro n hn
        have hn0 : n = 0 := by simp [pieces] at hn; omega
        subst n
        intro z hz
        change z ∈ Bprefix.carrier ∩ Tail.tailArc.carrier at hz
        change z ∈ ({Bprefix.target} : Set _)
        rw [hprefix_tail] at hz
        simpa [hprefix_target] using hz)
      (by
        intro k l hk hl hkl
        simp [pieces] at hk hl
        omega)
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
  have arc_source_ne_target : ∀ Q : PolygonalArc, Q.source ≠ Q.target := by
    intro Q heq
    have hlen := Q.length_ge_two
    have hzero : Q.vertices[0] = Q.source := by
      have hhead := Q.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    have hlast : Q.vertices[Q.vertices.length - 1] = Q.target := by
      have htarget := Q.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at htarget
      exact Option.some.inj htarget
    have hidx : 0 = Q.vertices.length - 1 :=
      (Q.simple_vertices.getElem_inj_iff).mp (by rw [hzero, hlast, heq])
    omega
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
  have hpiece_avoids : ∀ piece, piece ∈ pieces →
      Disjoint piece.relativeInterior
        ({D.vertexPlacement u, D.vertexPlacement Tail.farEndpoint} : Set _) := by
    intro piece hpiece
    change piece ∈ [Bprefix, Tail.tailArc] at hpiece
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpiece
    rcases hpiece with hpiece | hpiece
    · subst piece
      rw [Set.disjoint_left]
      intro z hz hzend
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzend
      rcases hzend with hzu | hzfar
      · have hznot : z ∉ ({Bprefix.source, Bprefix.target} : Set _) := by
          have hz' := hz
          rw [Bprefix.relativeInterior_eq] at hz'
          exact hz'.2
        apply hznot
        simp [hzu, hprefix_source]
      · have hzcarrier : D.vertexPlacement Tail.farEndpoint ∈ Bprefix.carrier :=
          hzfar ▸ (Bprefix.relativeInterior_eq ▸ hz).1
        have htailcarrier : D.vertexPlacement Tail.farEndpoint ∈ Tail.tailArc.carrier := by
          simpa [Tail.target_eq] using arc_target_mem_carrier Tail.tailArc
        have hinter : D.vertexPlacement Tail.farEndpoint ∈
            Bprefix.carrier ∩ Tail.tailArc.carrier := ⟨hzcarrier, htailcarrier⟩
        rw [hprefix_tail] at hinter
        have hfar_y : D.vertexPlacement Tail.farEndpoint = y := by simpa using hinter
        have htail_eq : Tail.tailArc.target = Tail.tailArc.source := by
          rw [Tail.target_eq, Tail.source_eq, hfar_y]
        exact arc_source_ne_target Tail.tailArc htail_eq.symm
    · subst piece
      rw [Set.disjoint_left]
      intro z hz hzend
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzend
      rcases hzend with hzu | hzfar
      · have hzcarrier : D.vertexPlacement u ∈ Tail.tailArc.carrier :=
          hzu ▸ (Tail.tailArc.relativeInterior_eq ▸ hz).1
        have hprefixcarrier : D.vertexPlacement u ∈ Bprefix.carrier := by
          simpa [hprefix_source] using arc_source_mem_carrier Bprefix
        have hinter : D.vertexPlacement u ∈
            Bprefix.carrier ∩ Tail.tailArc.carrier := ⟨hprefixcarrier, hzcarrier⟩
        rw [hprefix_tail] at hinter
        have hu_y : D.vertexPlacement u = y := by simpa using hinter
        have hprefix_eq : Bprefix.source = Bprefix.target := by
          rw [hprefix_source, hprefix_target, hu_y]
        exact arc_source_ne_target Bprefix hprefix_eq
      · have hznot : z ∉ ({Tail.tailArc.source, Tail.tailArc.target} : Set _) := by
          have hz' := hz
          rw [Tail.tailArc.relativeInterior_eq] at hz'
          exact hz'.2
        apply hznot
        simp [hzfar, Tail.target_eq]
  rcases PolygonalArcFromEndpointGluedPieces
      (pieces := pieces) (source := D.vertexPlacement u)
      (target := D.vertexPlacement Tail.farEndpoint)
      (hpieces := by simp [pieces])
      (first_source := by
        intro piece hhead
        have hpiece : piece = Bprefix := by simpa [pieces] using Option.some.inj hhead.symm
        subst piece
        exact hprefix_source)
      (last_target := by
        intro piece hlast
        have hpiece : Tail.tailArc = piece := by
          have : some Tail.tailArc = some piece := by simpa [pieces] using hlast
          exact Option.some.inj this
        subst piece
        exact Tail.target_eq)
      (successive_attach := hsuccessive)
      (glued_segment_endpoints_distinct := hnondegenerate)
      (adjacent_segment_intersections := hsegmentCerts.1)
      (nonadjacent_segment_disjoint := by
        intro i j hi hj hij
        exact hsegmentCerts.2 hi hj hij)
      (piece_relativeInterior_avoids_endpoints := hpiece_avoids) with
    ⟨betaArcNew, _hvertices, hbetaSource, hbetaTarget, hbetaCarrier,
      hbetaInterior, hpieceInterior, hpieceSegment, hsegmentPiece⟩
  let edgeArcNew : G.edgeFinset → PolygonalArc :=
    fun e => if e = beta then betaArcNew else D.edgeArc e
  have hbetaEdge : edgeArcNew beta = betaArcNew := by simp [edgeArcNew]
  have hotherEdges : ∀ e : G.edgeFinset, e ≠ beta →
      edgeArcNew e = D.edgeArc e := by
    intro e he
    simp [edgeArcNew, he]
  have hbetaAdj : G.Adj u Tail.farEndpoint ∧
      beta.1 = Sym2.mk u Tail.farEndpoint := by
    have hpair := (Sym2.mem_and_mem_iff Tail.farEndpoint_ne_u.symm).mp
      ⟨Tail.u_mem_beta, Tail.farEndpoint_mem_beta⟩
    have hedge : beta.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp beta.2
    rw [hpair] at hedge
    exact ⟨by simpa using hedge, hpair⟩
  have hEndpoints : ∀ e : G.edgeFinset,
      ∃ a b : V,
        G.Adj a b ∧ e.1 = Sym2.mk a b ∧
          (((edgeArcNew e).source = D.vertexPlacement a ∧
              (edgeArcNew e).target = D.vertexPlacement b) ∨
            ((edgeArcNew e).source = D.vertexPlacement b ∧
              (edgeArcNew e).target = D.vertexPlacement a)) := by
    intro e
    by_cases he : e = beta
    · subst e
      refine ⟨u, Tail.farEndpoint, hbetaAdj.1, hbetaAdj.2, Or.inl ?_⟩
      simpa [hbetaEdge] using And.intro hbetaSource hbetaTarget
    · rcases D.edgeArc_endpoints e with ⟨a, b, hab, heq, hends⟩
      exact ⟨a, b, hab, heq, by simpa [hotherEdges e he] using hends⟩
  refine ⟨betaArcNew, edgeArcNew, hbetaSource, hbetaTarget, ?_, ?_, ?_, ?_,
    ?_, ?_, hbetaEdge, hotherEdges, hEndpoints, ?_, ?_, ?_⟩
  · rw [hbetaCarrier]
    ext z
    simp [pieces]
  · rw [hbetaInterior]
    ext z
    simp [pieces]
  · exact hpieceInterior Bprefix (by simp [pieces])
  · exact hpieceInterior Tail.tailArc (by simp [pieces])
  · intro z hz
    rw [hbetaCarrier]
    exact ⟨Bprefix, by simp [pieces], hz⟩
  · intro z hz
    rw [hbetaCarrier]
    exact ⟨Tail.tailArc, by simp [pieces], hz⟩
  · intro m hm
    exact hpieceSegment Bprefix (by simp [pieces]) m hm
  · intro m hm
    exact hpieceSegment Tail.tailArc (by simp [pieces]) m hm
  · intro j hj
    rcases hsegmentPiece j hj with ⟨piece, hpiece, m, hm, hmatch⟩
    have hp : piece = Bprefix ∨ piece = Tail.tailArc := by simpa [pieces] using hpiece
    exact ⟨piece, hp, m, hm, hmatch⟩
