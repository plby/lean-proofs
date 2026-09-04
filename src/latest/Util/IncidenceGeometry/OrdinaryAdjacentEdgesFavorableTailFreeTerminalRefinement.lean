import Util.IncidenceGeometry.CollinearAdjacentSubsegmentsMeetAtEndpoint
import Util.IncidenceGeometry.OrdinaryAdjacentEdgesFavorableTailFreeCandidate
import Util.IncidenceGeometry.OrdinaryLabeledCrossingDiskDataExistsBelow
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentCertificates
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentTransfer
import Util.IncidenceGeometry.PolygonalArcFromEndpointGluedPieces
import Util.IncidenceGeometry.StraightSegmentPolygonalArc
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Tactic

open Classical
noncomputable section

private lemma favorableTailFreeArcSourceNeTarget (Q : PolygonalArc) :
    Q.source ≠ Q.target := by
  intro h
  have hlen := Q.length_ge_two
  have hzero : Q.vertices[0] = Q.source := by
    have hh := Q.source_eq_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some.inj hh
  have hlast : Q.vertices[Q.vertices.length - 1] = Q.target := by
    have ht := Q.target_eq_last
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
    exact Option.some.inj ht
  have hidx := (Q.simple_vertices.getElem_inj_iff
    (i := 0) (j := Q.vertices.length - 1)
    (hi := by omega) (hj := by omega)).1 (by rw [hzero, hlast, h])
  omega

private lemma favorableTailFreeArcSourceMem (Q : PolygonalArc) :
    Q.source ∈ Q.carrier := by
  have hlen := Q.length_ge_two
  rw [Q.carrier_eq]
  have hzero : Q.vertices[0] = Q.source := by
    have hhead := Q.source_eq_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
    exact Option.some.inj hhead
  exact ⟨0, by omega, by simpa [hzero] using
    (left_mem_segment ℝ Q.source Q.vertices[1])⟩

private lemma favorableTailFreeArcTargetMem (Q : PolygonalArc) :
    Q.target ∈ Q.carrier := by
  have hlen := Q.length_ge_two
  rw [Q.carrier_eq]
  let k := Q.vertices.length - 2
  have hk : k + 1 < Q.vertices.length := by dsimp [k]; omega
  have hlast : Q.vertices[k + 1] = Q.target := by
    have ht := Q.target_eq_last
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
    have heq : k + 1 = Q.vertices.length - 1 := by dsimp [k]; omega
    simpa [heq] using Option.some.inj ht
  exact ⟨k, hk, by simpa [hlast] using
    (right_mem_segment ℝ Q.vertices[k] Q.target)⟩

private lemma favorableTailFreePrefixInterior
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (e : G.edgeFinset) (u : V)
    (Q : PolygonalArc) (x : EuclideanSpace ℝ (Fin 2))
    (Cut : PolygonalArcPointCutData Q x)
    (p : EuclideanSpace ℝ (Fin 2))
    (hsource : Q.source = D.vertexPlacement u)
    (hrelative : Q.relativeInterior = (D.edgeArc e).relativeInterior)
    (hp : p ∈ Cut.prefixArc.carrier)
    (hpu : p ≠ D.vertexPlacement u) (hpx : p ≠ x) :
    p ∈ (D.edgeArc e).relativeInterior := by
  have hpTarget : p ≠ Q.target := by
    intro hpT
    have htargetSuffix : Q.target ∈ Cut.suffixArc.carrier := by
      have ht := favorableTailFreeArcTargetMem Cut.suffixArc
      rw [Cut.suffix_target] at ht
      exact ht
    have hpInter : p ∈ Cut.prefixArc.carrier ∩ Cut.suffixArc.carrier :=
      ⟨hp, hpT ▸ htargetSuffix⟩
    have hpx' : p = x := by
      have : p ∈ ({x} : Set _) := Cut.carrier_intersection ▸ hpInter
      simpa using this
    exact hpx hpx'
  have hpQrel : p ∈ Q.relativeInterior := by
    rw [Q.relativeInterior_eq]
    refine ⟨Cut.prefix_carrier_subset hp, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hpSource => hpu (hpSource.trans hsource), hpTarget⟩
  rwa [hrelative] at hpQrel

private lemma favorableTailFreeCarrierRelativeOfNotVertex
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (p : EuclideanSpace ℝ (Fin 2))
    (hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v)
    (e : G.edgeFinset) (hp : p ∈ (D.edgeArc e).carrier) :
    p ∈ (D.edgeArc e).relativeInterior := by
  rw [(D.edgeArc e).relativeInterior_eq]
  refine ⟨hp, ?_⟩
  rcases D.edgeArc_endpoints e with ⟨a, b, _hab, _he, hends⟩
  rcases hends with hends | hends
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hpNotVertex a (h.trans hends.1),
      fun h => hpNotVertex b (h.trans hends.2)⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hpNotVertex b (h.trans hends.1),
      fun h => hpNotVertex a (h.trans hends.2)⟩

private lemma favorableTailFreeOpenIndexUnique (Q : PolygonalArc) :
    ∀ z a b (ha : a + 1 < Q.vertices.length)
      (hb : b + 1 < Q.vertices.length),
      z ∈ openSegment ℝ Q.vertices[a] Q.vertices[a + 1] →
      z ∈ segment ℝ Q.vertices[b] Q.vertices[b + 1] → a = b := by
  intro z a b ha hb hza hzb
  have habne : Q.vertices[a] ≠ Q.vertices[a + 1] := by
    intro heq
    have hidx := (Q.simple_vertices.getElem_inj_iff
      (i := a) (j := a + 1) (hi := by omega) (hj := ha)).1 heq
    omega
  have hzleft : z ≠ Q.vertices[a] := by
    intro hz
    subst z
    exact habne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hza)
  have hzright : z ≠ Q.vertices[a + 1] := by
    intro hz
    subst z
    exact habne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hza)
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hraw := Q.segment_intersections ha hb hab
    have hzint : z ∈ segment ℝ Q.vertices[a] Q.vertices[a + 1] ∩
        segment ℝ Q.vertices[b] Q.vertices[b + 1] :=
      ⟨openSegment_subset_segment ℝ _ _ hza, hzb⟩
    by_cases hadj : b = a + 1
    · rw [hraw, if_pos hadj] at hzint
      exact False.elim (hzright (by simpa [hadj] using hzint))
    · rw [hraw, if_neg hadj] at hzint
      exact False.elim hzint
  · rfl
  · have hraw := Q.segment_intersections hb ha hba
    have hzint : z ∈ segment ℝ Q.vertices[b] Q.vertices[b + 1] ∩
        segment ℝ Q.vertices[a] Q.vertices[a + 1] :=
      ⟨hzb, openSegment_subset_segment ℝ _ _ hza⟩
    by_cases hadj : a = b + 1
    · rw [hraw, if_pos hadj] at hzint
      exact False.elim (hzleft (by simpa [hadj] using hzint))
    · rw [hraw, if_neg hadj] at hzint
      exact False.elim hzint

private lemma favorableTailFreeGlueResidualTail
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (secondEdge : G.edgeFinset) (u : V)
    (y y' : EuclideanSpace ℝ (Fin 2))
    (B BplusOld RbetaOld HOld : Set (EuclideanSpace ℝ (Fin 2)))
    (TailOld : BigonRerouteOrderedBetaTailData
      G D secondEdge u y B BplusOld RbetaOld HOld)
    (Residual : PolygonalArc)
    (hy'neY : y' ≠ y)
    (hResidualSource : Residual.source = y')
    (hResidualTarget : Residual.target = y)
    (hResidualCarrier : Residual.carrier = segment ℝ y' y)
    (hResidualInterior : Residual.relativeInterior = openSegment ℝ y' y)
    (hResidualTailArc :
      Residual.carrier ∩ TailOld.tailArc.carrier = ({y} : Set _)) :
    ∃ TailArc : PolygonalArc,
      TailArc.source = y' ∧
      TailArc.target = D.vertexPlacement TailOld.farEndpoint ∧
      TailArc.carrier = segment ℝ y' y ∪ TailOld.tailArc.carrier ∧
      TailArc.relativeInterior =
        (segment ℝ y' y ∪ TailOld.tailArc.carrier) \
          ({y', D.vertexPlacement TailOld.farEndpoint} : Set _) := by
  let pieces : List PolygonalArc := [Residual, TailOld.tailArc]
  have hsuccessive :
      ∀ n (hn : n + 1 < pieces.length),
        (pieces[n]).target = (pieces[n + 1]).source := by
    intro n hn
    have hn0 : n = 0 := by simp [pieces] at hn; omega
    subst n
    simpa [pieces, hResidualTarget] using TailOld.source_eq.symm
  have hsegmentCerts :=
    PolygonalArcEndpointGluedSegmentCertificates pieces hsuccessive
      (by
        intro n hn
        have hn0 : n = 0 := by simp [pieces] at hn; omega
        subst n
        intro p hp
        change p ∈ Residual.carrier ∩ TailOld.tailArc.carrier at hp
        change p ∈ ({Residual.target} : Set _)
        rw [hResidualTailArc] at hp
        simpa [hResidualTarget] using hp)
      (by
        intro k l hk hl hkl
        simp [pieces] at hk hl
        omega)
  have htransfer :=
    PolygonalArcEndpointGluedSegmentTransfer pieces hsuccessive
  have hnondegenerate :
      ∀ k
        (hk : k + 1 < (PolygonalArcEndpointGluedVertices pieces).length),
        (PolygonalArcEndpointGluedVertices pieces)[k] ≠
          (PolygonalArcEndpointGluedVertices pieces)[k + 1] := by
    intro k hk heq
    rcases htransfer.2 k hk with
      ⟨piece, _hpiece, m, hm, hmatch | hmatch⟩
    · have hlocal : piece.vertices[m] = piece.vertices[m + 1] := by
        calc
          piece.vertices[m] =
              (PolygonalArcEndpointGluedVertices pieces)[k] := hmatch.1.symm
          _ = (PolygonalArcEndpointGluedVertices pieces)[k + 1] := heq
          _ = piece.vertices[m + 1] := hmatch.2
      exact (Nat.ne_of_lt (by omega : m < m + 1))
        ((piece.simple_vertices.getElem_inj_iff
          (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 hlocal)
    · have hlocal : piece.vertices[m] = piece.vertices[m + 1] := by
        calc
          piece.vertices[m] =
              (PolygonalArcEndpointGluedVertices pieces)[k + 1] := hmatch.2.symm
          _ = (PolygonalArcEndpointGluedVertices pieces)[k] := heq.symm
          _ = piece.vertices[m + 1] := hmatch.1
      exact (Nat.ne_of_lt (by omega : m < m + 1))
        ((piece.simple_vertices.getElem_inj_iff
          (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 hlocal)
  have hpieceAvoids : ∀ piece, piece ∈ pieces →
      Disjoint piece.relativeInterior
        ({y', D.vertexPlacement TailOld.farEndpoint} : Set _) := by
    intro piece hpiece
    have hpiece' : piece = Residual ∨ piece = TailOld.tailArc := by
      simpa only [pieces, List.mem_cons, List.not_mem_nil, or_false] using hpiece
    rcases hpiece' with hpiece | hpiece
    · subst piece
      rw [Set.disjoint_left]
      intro p hp hpEnd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpEnd
      rcases hpEnd with hpSource | hpFar
      · have hpOpen : p ∈ openSegment ℝ y' y := by
          simpa [hResidualInterior] using hp
        have hy'Open : y' ∈ openSegment ℝ y' y := by
          simpa [hpSource] using hpOpen
        exact hy'neY ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hy'Open)
      · have hpResidual : D.vertexPlacement TailOld.farEndpoint ∈
            Residual.carrier := by
          rw [← hpFar]
          exact (Residual.relativeInterior_eq ▸ hp).1
        have hpTail : D.vertexPlacement TailOld.farEndpoint ∈
            TailOld.tailArc.carrier := by
          have ht := favorableTailFreeArcTargetMem TailOld.tailArc
          simpa [TailOld.target_eq] using ht
        have hpAtY : D.vertexPlacement TailOld.farEndpoint = y := by
          have : D.vertexPlacement TailOld.farEndpoint ∈ ({y} : Set _) :=
            hResidualTailArc ▸ ⟨hpResidual, hpTail⟩
          simpa using this
        apply favorableTailFreeArcSourceNeTarget TailOld.tailArc
        rw [TailOld.source_eq, TailOld.target_eq, hpAtY]
    · subst piece
      rw [Set.disjoint_left]
      intro p hp hpEnd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpEnd
      rcases hpEnd with hpCut | hpFar
      · subst p
        have hpResidual : y' ∈ Residual.carrier := by
          have hs := favorableTailFreeArcSourceMem Residual
          simpa [hResidualSource] using hs
        have hpTail : y' ∈ TailOld.tailArc.carrier := by
          exact (TailOld.tailArc.relativeInterior_eq ▸ hp).1
        have hy'eq : y' = y := by
          have : y' ∈ ({y} : Set _) := hResidualTailArc ▸
            ⟨hpResidual, hpTail⟩
          simpa using this
        exact hy'neY hy'eq
      · rw [TailOld.tailArc.relativeInterior_eq] at hp
        exact hp.2 (by simp [hpFar, TailOld.target_eq])
  rcases PolygonalArcFromEndpointGluedPieces
      (pieces := pieces) (source := y')
      (target := D.vertexPlacement TailOld.farEndpoint)
      (hpieces := by simp [pieces])
      (first_source := by
        intro piece hhead
        have hpiece : piece = Residual := by
          simpa [pieces] using Option.some.inj hhead.symm
        subst piece
        exact hResidualSource)
      (last_target := by
        intro piece hlast
        have hpiece : TailOld.tailArc = piece := by
          have : some TailOld.tailArc = some piece := by
            simpa [pieces] using hlast
          exact Option.some.inj this
        subst piece
        exact TailOld.target_eq)
      (successive_attach := hsuccessive)
      (glued_segment_endpoints_distinct := hnondegenerate)
      (adjacent_segment_intersections := hsegmentCerts.1)
      (nonadjacent_segment_disjoint := by
        intro k l hk hl hkl
        exact hsegmentCerts.2 hk hl hkl)
      (piece_relativeInterior_avoids_endpoints := hpieceAvoids) with
    ⟨TailArc, _hTailVertices, hTailSource, hTailTarget,
      hTailCarrierPieces, hTailInteriorPieces,
      _hPieceInterior, _hPieceSegment, _hSegmentPiece⟩
  have hPiecesUnion :
      {p | ∃ piece : PolygonalArc, piece ∈ pieces ∧ p ∈ piece.carrier} =
        segment ℝ y' y ∪ TailOld.tailArc.carrier := by
    ext p
    simp [pieces, hResidualCarrier]
  refine ⟨TailArc, hTailSource, hTailTarget, ?_, ?_⟩
  · exact hTailCarrierPieces.trans hPiecesUnion
  · rw [hTailInteriorPieces, hPiecesUnion]

private lemma favorableTailFreeDisjointNewTail
    {FirstCutArc OutCutArc : PolygonalArc}
    {FirstCutPoint OutCutPoint : EuclideanSpace ℝ (Fin 2)}
    (A BplusOld : Set (EuclideanSpace ℝ (Fin 2)))
    (x y' y : EuclideanSpace ℝ (Fin 2))
    (FirstCut : PolygonalArcPointCutData (Q := FirstCutArc) FirstCutPoint)
    (OutCut : PolygonalArcPointCutData (Q := OutCutArc) OutCutPoint)
    (TailArc OldTail : PolygonalArc)
    (hTailCarrier : TailArc.carrier = segment ℝ y' y ∪ OldTail.carrier)
    (hAInterOld : A ∩ BplusOld = ({x} : Set _))
    (hresidualSubsetOld : segment ℝ y' y ⊆ BplusOld)
    (hxNotResidual : x ∉ segment ℝ y' y)
    (hOldTailOut : OldTail.carrier = OutCut.suffixArc.carrier)
    (hFirstTail : Disjoint FirstCut.prefixArc.carrier OutCut.suffixArc.carrier)
    (hA : A = FirstCut.prefixArc.carrier) :
    Disjoint A TailArc.carrier := by
  rw [Set.disjoint_left]
  intro p hpA hpTail
  rw [hTailCarrier] at hpTail
  rcases hpTail with hpResidual | hpOldTail
  · have hpx : p = x := by
      have : p ∈ ({x} : Set _) := hAInterOld ▸
        ⟨hpA, hresidualSubsetOld hpResidual⟩
      simpa using this
    exact hxNotResidual (hpx ▸ hpResidual)
  · have hpOut : p ∈ OutCut.suffixArc.carrier := by
      rw [← hOldTailOut]
      exact hpOldTail
    exact (Set.disjoint_left.mp
      (hFirstTail.mono_left (by simpa [hA]))) hpA hpOut


private lemma favorableTailFreeCandidateWithTransfer
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (alpha beta : G.edgeFinset) (u : V)
    (hopen : forall p : EuclideanSpace ℝ (Fin 2),
      p ∈ D.crossingSet ->
        p ∈ (D.edgeArc alpha).relativeInterior ->
          p ∈ (D.edgeArc beta).relativeInterior ->
            exists i j : ℕ,
              exists (hi : i + 1 < (D.edgeArc alpha).vertices.length)
                (hj : j + 1 < (D.edgeArc beta).vertices.length),
                p ∈ openSegment ℝ (D.edgeArc alpha).vertices[i]
                    (D.edgeArc alpha).vertices[i + 1] ∧
                  p ∈ openSegment ℝ (D.edgeArc beta).vertices[j]
                    (D.edgeArc beta).vertices[j + 1])
    (hab : alpha ≠ beta) (huAlpha : u ∈ alpha.1) (huBeta : u ∈ beta.1)
    (hcross : exists p : EuclideanSpace ℝ (Fin 2),
      p ∈ D.crossingSet ∧
        p ∈ (D.edgeArc alpha).relativeInterior ∧
          p ∈ (D.edgeArc beta).relativeInterior) :
            exists firstEdge secondEdge : G.edgeFinset,
              (firstEdge = alpha ∧ secondEdge = beta ∨
                firstEdge = beta ∧ secondEdge = alpha) ∧
              exists firstArc secondArc : PolygonalArc,
                firstArc.carrier = (D.edgeArc firstEdge).carrier ∧
                firstArc.relativeInterior =
                  (D.edgeArc firstEdge).relativeInterior ∧
                firstArc.source = D.vertexPlacement u ∧
                secondArc.carrier = (D.edgeArc secondEdge).carrier ∧
                secondArc.relativeInterior =
                  (D.edgeArc secondEdge).relativeInterior ∧
                secondArc.source = D.vertexPlacement u ∧
                exists x y : EuclideanSpace ℝ (Fin 2),
                  exists FirstCut : PolygonalArcPointCutData firstArc x,
                    exists SecondCut : PolygonalArcPointCutData secondArc x,
                      exists OutCut :
                        PolygonalArcPointCutData SecondCut.suffixArc y,
                        (forall p i
                            (hi : i + 1 <
                              (D.edgeArc firstEdge).vertices.length),
                          p ∈ openSegment ℝ
                              (D.edgeArc firstEdge).vertices[i]
                              (D.edgeArc firstEdge).vertices[i + 1] ->
                          p ∈ FirstCut.prefixArc.carrier ->
                          p ≠ x ->
                          exists j : ℕ,
                            exists hj : j + 1 <
                                FirstCut.prefixArc.vertices.length,
                              p ∈ openSegment ℝ
                                  FirstCut.prefixArc.vertices[j]
                                  FirstCut.prefixArc.vertices[j + 1] ∧
                              exists scale : ℝ,
                                scale ≠ 0 ∧
                                FirstCut.prefixArc.vertices[j + 1] -
                                    FirstCut.prefixArc.vertices[j] =
                                  scale •
                                    ((D.edgeArc firstEdge).vertices[i + 1] -
                                      (D.edgeArc firstEdge).vertices[i])) ∧
                        x ∈ D.crossingSet ∧
                        x ∈ (D.edgeArc firstEdge).relativeInterior ∧
                        x ∈ (D.edgeArc secondEdge).relativeInterior ∧
                        y ∈ (D.edgeArc secondEdge).relativeInterior ∧
                        y ≠ x ∧
                        OutCut.prefixArc.carrier = segment ℝ x y ∧
                        FirstCut.prefixArc.carrier ∩
                            SecondCut.prefixArc.carrier =
                          ({D.vertexPlacement u, x} : Set _) ∧
                        SecondCut.prefixArc.carrier ∩
                            OutCut.prefixArc.carrier = ({x} : Set _) ∧
                        Disjoint FirstCut.prefixArc.carrier
                          OutCut.suffixArc.carrier ∧
                        exists XA XB : Finset (EuclideanSpace ℝ (Fin 2)),
                          (forall p, p ∈ XA ↔
                            p ∈ FirstCut.prefixArc.carrier \
                              ({D.vertexPlacement u, x} : Set _) ∧
                            exists e : G.edgeFinset,
                              e ≠ firstEdge ∧ e ≠ secondEdge ∧
                                p ∈ (D.edgeArc e).relativeInterior) ∧
                          (forall p, p ∈ XB ↔
                            p ∈ SecondCut.prefixArc.carrier \
                              ({D.vertexPlacement u, x} : Set _) ∧
                            exists e : G.edgeFinset,
                              e ≠ firstEdge ∧ e ≠ secondEdge ∧
                                p ∈ (D.edgeArc e).relativeInterior) ∧
                          XA.card ≤ XB.card ∧
                          (exists A B Bplus Rbeta H :
                              Set (EuclideanSpace ℝ (Fin 2)),
                            A = FirstCut.prefixArc.carrier ∧
                            B = SecondCut.prefixArc.carrier ∧
                            Bplus = OutCut.prefixArc.carrier ∧
                            Rbeta =
                              (D.edgeArc secondEdge).carrier \
                                ((B ∪ Bplus) \ ({y} : Set _)) ∧
                            H =
                              (⋃ edge : G.edgeFinset,
                                if edge = firstEdge then
                                  (D.edgeArc edge).carrier \
                                    (A \ ({D.vertexPlacement u, x} : Set _))
                                else if edge = secondEdge then
                                  (D.edgeArc edge).carrier \
                                    ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
                                      (Bplus \ ({x, y} : Set _)))
                                else (D.edgeArc edge).carrier) ∪
                              {p | exists v : V,
                                v ≠ u ∧ p = D.vertexPlacement v} ∧
                            (exists Tail : BigonRerouteOrderedBetaTailData
                                G D secondEdge u y B Bplus Rbeta H,
                              (forall p, p ∈ Bplus →
                                p ∈ D.crossingSet → p = x) ∧
                              (forall v : V,
                                D.vertexPlacement v ∈ Bplus → False) ∧
                              (exists XAexact XBexact :
                                  Finset (EuclideanSpace ℝ (Fin 2)),
                                XAexact = XA ∧ XB ⊆ XBexact ∧
                                (forall p, p ∈ XAexact ↔
                                  p ∈ A \
                                    ({D.vertexPlacement u, x} : Set _) ∧
                                  p ∈ H) ∧
                                (forall p, p ∈ XBexact ↔
                                  p ∈ B \
                                    ({D.vertexPlacement u, x} : Set _) ∧
                                  p ∈ H) ∧
                                XAexact.card ≤ XBexact.card))) := by
    have endpoint_at (e : G.edgeFinset) (hu : u ∈ e.1) :
        (D.edgeArc e).source = D.vertexPlacement u ∨
          (D.edgeArc e).target = D.vertexPlacement u := by
      rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, he, hends⟩
      have huab : u = a ∨ u = b := by
        have : u ∈ (Sym2.mk a b : Sym2 V) := by simpa [he] using hu
        simpa [Sym2.mem_iff'] using this
      rcases hends with hends | hends <;> rcases huab with rfl | rfl
      · exact Or.inl hends.1
      · exact Or.inr hends.2
      · exact Or.inr hends.2
      · exact Or.inl hends.1
    let orient : G.edgeFinset → PolygonalArc := fun e =>
      if (D.edgeArc e).source = D.vertexPlacement u then
        D.edgeArc e
      else PolygonalArcReverse (D.edgeArc e)
    have orient_carrier (e : G.edgeFinset) :
        (orient e).carrier = (D.edgeArc e).carrier := by
      dsimp [orient]
      split_ifs
      · rfl
      · rfl
    have orient_relative (e : G.edgeFinset) :
        (orient e).relativeInterior = (D.edgeArc e).relativeInterior := by
      dsimp [orient]
      split_ifs
      · rfl
      · rfl
    have orient_source (e : G.edgeFinset) (hu : u ∈ e.1) :
        (orient e).source = D.vertexPlacement u := by
      dsimp [orient]
      split_ifs with h
      · exact h
      · rcases endpoint_at e hu with hs | ht
        · exact (h hs).elim
        · exact ht
    have open_not_vertex (Q : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2))
        (i : ℕ) (hi : i + 1 < Q.vertices.length)
        (hp : p ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1]) :
        p ∉ Q.vertices := by
      intro hpv
      rcases List.getElem_of_mem hpv with ⟨k, hk, hkp⟩
      by_cases hki : k = i
      · subst k
        have hne : Q.vertices[i] ≠ Q.vertices[i + 1] := by
          intro heq
          have := (Q.simple_vertices.getElem_inj_iff
            (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 heq
          omega
        exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (hkp ▸ hp))
      · by_cases hkis : k = i + 1
        · subst k
          have hne : Q.vertices[i] ≠ Q.vertices[i + 1] := by
            intro heq
            have := (Q.simple_vertices.getElem_inj_iff
              (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 heq
            omega
          exact hne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 (hkp ▸ hp))
        · exact Q.vertices_avoid_nonincident_interiors hi hk hki hkis (hkp ▸ hp)
    have orient_segment_transfer (e : G.edgeFinset)
        (p : EuclideanSpace ℝ (Fin 2)) (i : ℕ)
        (hi : i + 1 < (D.edgeArc e).vertices.length)
        (hp : p ∈ openSegment ℝ (D.edgeArc e).vertices[i]
          (D.edgeArc e).vertices[i + 1]) :
        exists j : ℕ, exists hj : j + 1 < (orient e).vertices.length,
          p ∈ openSegment ℝ (orient e).vertices[j]
              (orient e).vertices[j + 1] ∧
            exists scale : ℝ, scale ≠ 0 ∧
              (orient e).vertices[j + 1] - (orient e).vertices[j] =
                scale • ((D.edgeArc e).vertices[i + 1] -
                  (D.edgeArc e).vertices[i]) := by
      dsimp [orient]
      split_ifs with hs
      · exact ⟨i, hi, hp, 1, one_ne_zero, by simp⟩
      · let j := (D.edgeArc e).vertices.length - 2 - i
        have hj : j + 1 < (D.edgeArc e).vertices.reverse.length := by
          simp only [List.length_reverse]
          dsimp [j]
          omega
        have hjlt : j < (D.edgeArc e).vertices.reverse.length :=
          Nat.lt_trans (Nat.lt_succ_self j) hj
        have hleft : (D.edgeArc e).vertices.reverse[j] =
            (D.edgeArc e).vertices[i + 1] := by
          have hidx : (D.edgeArc e).vertices.length - 1 - j = i + 1 := by
            dsimp [j]
            omega
          simpa only [hidx] using
            (List.getElem_reverse (l := (D.edgeArc e).vertices)
              (i := j) (h := hjlt))
        have hright : (D.edgeArc e).vertices.reverse[j + 1] =
            (D.edgeArc e).vertices[i] := by
          have hidx : (D.edgeArc e).vertices.length - 1 - (j + 1) = i := by
            dsimp [j]
            omega
          simpa only [hidx] using
            (List.getElem_reverse (l := (D.edgeArc e).vertices)
              (i := j + 1) (h := hj))
        refine ⟨j, by simpa only [PolygonalArcReverse] using hj, ?_,
          -1, by norm_num, ?_⟩
        · simpa only [PolygonalArcReverse, hleft, hright,
            openSegment_symm] using hp
        · simp only [PolygonalArcReverse, hleft, hright]
          module
    have orient_prefix_segment_transfer (e : G.edgeFinset)
        (c : EuclideanSpace ℝ (Fin 2))
        (Cut : PolygonalArcPointCutData (orient e) c) :
        forall p i (hi : i + 1 < (D.edgeArc e).vertices.length),
          p ∈ openSegment ℝ (D.edgeArc e).vertices[i]
              (D.edgeArc e).vertices[i + 1] ->
          p ∈ Cut.prefixArc.carrier ->
          p ≠ c ->
          exists j : ℕ, exists hj : j + 1 < Cut.prefixArc.vertices.length,
            p ∈ openSegment ℝ Cut.prefixArc.vertices[j]
                Cut.prefixArc.vertices[j + 1] ∧
              exists scale : ℝ, scale ≠ 0 ∧
                Cut.prefixArc.vertices[j + 1] - Cut.prefixArc.vertices[j] =
                  scale • ((D.edgeArc e).vertices[i + 1] -
                    (D.edgeArc e).vertices[i]) := by
      intro p i hi hp hpcarrier hpne
      rcases orient_segment_transfer e p i hi hp with
        ⟨k, hk, hpOrient, orientScale, hOrientScale, hOrientDirection⟩
      rcases Cut.prefix_segment_transfer p k hk hpOrient hpcarrier hpne with
        ⟨j, hj, hpPrefix, prefixScale, hPrefixScale, hPrefixDirection⟩
      refine ⟨j, hj, hpPrefix, prefixScale * orientScale,
        mul_ne_zero hPrefixScale hOrientScale, ?_⟩
      rw [hPrefixDirection, hOrientDirection, smul_smul]
    let X : Finset (EuclideanSpace ℝ (Fin 2)) :=
      D.crossingSet.filter (fun p =>
        p ∈ (D.edgeArc alpha).relativeInterior ∧
          p ∈ (D.edgeArc beta).relativeInterior)
    have hXnonempty : X.Nonempty := by
      rcases hcross with ⟨p, hpD, hpA, hpB⟩
      refine ⟨p, ?_⟩
      simp [X, hpD, hpA, hpB]
    have hXalpha : ∀ p, p ∈ X → p ∈ (orient alpha).relativeInterior := by
      intro p hp
      rw [orient_relative]
      exact (Finset.mem_filter.mp hp).2.1
    have hXbeta : ∀ p, p ∈ X → p ∈ (orient beta).relativeInterior := by
      intro p hp
      rw [orient_relative]
      exact (Finset.mem_filter.mp hp).2.2
    have hXnotAlphaVertices : ∀ p, p ∈ X → p ∉ (orient alpha).vertices := by
      intro p hp
      rcases hopen p (Finset.mem_filter.mp hp).1
          (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2 with
        ⟨i, j, hi, hj, hpAi, hpBj⟩
      have hnot := open_not_vertex (D.edgeArc alpha) p i hi hpAi
      dsimp [orient]
      split_ifs
      · exact hnot
      · simpa only [PolygonalArcReverse, List.mem_reverse] using hnot
    have hXnotBetaVertices : ∀ p, p ∈ X → p ∉ (orient beta).vertices := by
      intro p hp
      rcases hopen p (Finset.mem_filter.mp hp).1
          (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2 with
        ⟨i, j, hi, hj, hpAi, hpBj⟩
      have hnot := open_not_vertex (D.edgeArc beta) p j hj hpBj
      dsimp [orient]
      split_ifs
      · exact hnot
      · simpa only [PolygonalArcReverse, List.mem_reverse] using hnot
    have first_package (Q : PolygonalArc)
        (hrel : ∀ p, p ∈ X → p ∈ Q.relativeInterior)
        (hnotverts : ∀ p, p ∈ X → p ∉ Q.vertices) :
        ∃ x : EuclideanSpace ℝ (Fin 2),
          ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
            ∃ Cut : PolygonalArcPointCutData Q x,
              x ∈ X ∧
              x ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] ∧
              Cut.cutIndex = j ∧
              (∀ z, z ∈ X → z ∈ Cut.prefixArc.carrier → z = x) ∧
              ∀ z, z ∈ X → ∀ ZCut : PolygonalArcPointCutData Q z,
                Cut.prefixArc.carrier ⊆ ZCut.prefixArc.carrier := by
      obtain ⟨x, j, hj, hxX, hxseg, hminimal⟩ :=
        PolygonalArcFiniteInteriorFirstPoint Q X hXnonempty hrel
      have hxopen : x ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] := by
        apply mem_openSegment_of_ne_left_right
        · intro h
          apply hnotverts x hxX
          rw [← h]
          exact List.getElem_mem (by omega)
        · intro h
          apply hnotverts x hxX
          rw [← h]
          exact List.getElem_mem hj
        · exact hxseg
      obtain ⟨Cut⟩ := PolygonalArcInteriorPointCutDataExists Q j hj x hxopen
      have hcut : Cut.cutIndex = j :=
        (favorableTailFreeOpenIndexUnique Q x j Cut.cutIndex hj
          Cut.cutIndex_valid hxopen
          Cut.cut_mem_segment).symm
      have hCutRegion : Cut.prefixArc.carrier =
          {z | ∃ i : ℕ, ∃ hi : i + 1 < Q.vertices.length,
            i < j ∧ z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1]} ∪
            segment ℝ Q.vertices[j] x := by
        simpa only [hcut] using Cut.prefix_carrier_region
      have hminPrefix : ∀ z, z ∈ X → z ∈ Cut.prefixArc.carrier → z = x := by
        intro z hzX hzCut
        rw [hCutRegion] at hzCut
        rcases hzCut with hzEarlier | hzLast
        · apply hminimal z hzX
          left
          rcases hzEarlier with ⟨i, hi, hij, hzi⟩
          rw [ArcCrossingEarlierPrefix]
          apply Set.mem_iUnion.mpr
          exact ⟨⟨i, hij⟩, hzi⟩
        · exact hminimal z hzX (Or.inr hzLast)
      refine ⟨x, j, hj, Cut, hxX, hxopen, hcut, hminPrefix, ?_⟩
      intro z hzX ZCut w hw
      have hk0 : ZCut.cutIndex < Q.vertices.length :=
        Nat.lt_trans (Nat.lt_succ_self _) ZCut.cutIndex_valid
      have hk1 : ZCut.cutIndex + 1 < Q.vertices.length := ZCut.cutIndex_valid
      have hzOpen : z ∈ openSegment ℝ Q.vertices[ZCut.cutIndex]
          Q.vertices[ZCut.cutIndex + 1] := by
        apply mem_openSegment_of_ne_left_right
        · intro h
          apply hnotverts z hzX
          rw [← h]
          exact List.getElem_mem (by omega)
        · intro h
          apply hnotverts z hzX
          rw [← h]
          exact List.getElem_mem ZCut.cutIndex_valid
        · exact ZCut.cut_mem_segment
      have hjle : j ≤ ZCut.cutIndex := by
        by_contra hnot
        have hlt : ZCut.cutIndex < j := by omega
        have hzEarlier : z ∈ ArcCrossingEarlierPrefix Q j hj := by
          rw [ArcCrossingEarlierPrefix]
          apply Set.mem_iUnion.mpr
          exact ⟨⟨ZCut.cutIndex, hlt⟩, ZCut.cut_mem_segment⟩
        have hzx : z = x := hminimal z hzX (Or.inl hzEarlier)
        subst z
        have := favorableTailFreeOpenIndexUnique Q x j ZCut.cutIndex hj
          ZCut.cutIndex_valid hxopen ZCut.cut_mem_segment
        omega
      rw [hCutRegion] at hw
      rw [ZCut.prefix_carrier_region]
      rcases lt_or_eq_of_le hjle with hjlt | hjeq
      · left
        rcases hw with hwEarlier | hwLast
        · rcases hwEarlier with ⟨i, hi, hij, hwi⟩
          exact ⟨i, hi, by omega, hwi⟩
        · exact ⟨j, hj, hjlt, (convex_segment Q.vertices[j]
            Q.vertices[j + 1]).segment_subset
              (left_mem_segment ℝ _ _)
              (openSegment_subset_segment ℝ _ _ hxopen) hwLast⟩
      · have hjeq' : ZCut.cutIndex = j := hjeq.symm
        simp only [hjeq']
        rcases hw with hwEarlier | hwLast
        · exact Or.inl hwEarlier
        · right
          have hxFull : x ∈ segment ℝ Q.vertices[j] Q.vertices[j + 1] :=
            openSegment_subset_segment ℝ _ _ hxopen
          have hzFull : z ∈ segment ℝ Q.vertices[j] Q.vertices[j + 1] :=
            by simpa only [hjeq'] using ZCut.cut_mem_segment
          have hbaseNe : Q.vertices[j] ≠ Q.vertices[j + 1] := by
            intro heq
            have hidx := (Q.simple_vertices.getElem_inj_iff
              (i := j) (j := j + 1) (hi := by omega) (hj := hj)).1 heq
            omega
          have hsameray : SameRay ℝ (x - Q.vertices[j]) (z - Q.vertices[j]) := by
            have hxray := (mem_segment_iff_wbtw.mp hxFull).sameRay_vsub_left
            have hzray := (mem_segment_iff_wbtw.mp hzFull).sameRay_vsub_left
            exact hxray.trans hzray.symm (by
              intro hzero
              have heq : Q.vertices[j + 1] = Q.vertices[j] := sub_eq_zero.mp hzero
              exact (hbaseNe heq.symm).elim)
          have hsameray' : SameRay ℝ (x -ᵥ Q.vertices[j])
              (z -ᵥ Q.vertices[j]) := by
            simpa only [vsub_eq_sub] using hsameray
          rcases wbtw_total_of_sameRay_vsub_left hsameray' with hxz | hzx
          · exact (convex_segment Q.vertices[j] z).segment_subset
              (left_mem_segment ℝ _ _) hxz.mem_segment hwLast
          · have hzx' : z = x := hminimal z hzX (Or.inr hzx.mem_segment)
            simpa [hzx'] using hwLast
    obtain ⟨xAlpha, jAlpha, hjAlpha, AlphaCut, hxAlphaX, hxAlphaOpen,
        hAlphaCutIndex, hAlphaMinimal, hAlphaPrefixSmall⟩ :=
      first_package (orient alpha) hXalpha hXnotAlphaVertices
    obtain ⟨xBeta, jBeta, hjBeta, BetaCut, hxBetaX, hxBetaOpen,
        hBetaCutIndex, hBetaMinimal, hBetaPrefixSmall⟩ :=
      first_package (orient beta) hXbeta hXnotBetaVertices
    obtain ⟨AlphaAtBeta⟩ := PolygonalArcPointCutDataExists (orient alpha) xBeta
      (hXalpha xBeta hxBetaX)
    obtain ⟨BetaAtAlpha⟩ := PolygonalArcPointCutDataExists (orient beta) xAlpha
      (hXbeta xAlpha hxAlphaX)
    have hAlphaPrefixInBeta := hAlphaPrefixSmall xBeta hxBetaX AlphaAtBeta
    have hBetaPrefixInAlpha := hBetaPrefixSmall xAlpha hxAlphaX BetaAtAlpha
    have orient_target_vertex (e : G.edgeFinset) :
        ∃ v : V, (orient e).target = D.vertexPlacement v := by
      rcases D.edgeArc_endpoints e with ⟨a, b, _hab, _he, hends⟩
      dsimp [orient]
      by_cases hs : (D.edgeArc e).source = D.vertexPlacement u
      · simp only [if_pos hs]
        rcases hends with hends | hends
        · exact ⟨b, hends.2⟩
        · exact ⟨a, hends.2⟩
      · simp only [if_neg hs, PolygonalArcReverse]
        rcases hends with hends | hends
        · exact ⟨a, hends.1⟩
        · exact ⟨b, hends.1⟩
    have alphaPrefixBeta :
        AlphaCut.prefixArc.carrier ∩ (orient beta).carrier =
          ({D.vertexPlacement u, xAlpha} : Set _) := by
      ext z
      constructor
      · intro hz
        have hzAlphaTarget : z ≠ (orient alpha).target := by
          intro hzt
          have htSuffix : (orient alpha).target ∈ AlphaCut.suffixArc.carrier := by
            rw [← AlphaCut.suffix_target]
            exact favorableTailFreeArcTargetMem AlphaCut.suffixArc
          have hzInter : z ∈ AlphaCut.prefixArc.carrier ∩
              AlphaCut.suffixArc.carrier := ⟨hz.1, hzt ▸ htSuffix⟩
          have hzx : z = xAlpha := by
            have : z ∈ ({xAlpha} : Set _) := AlphaCut.carrier_intersection ▸ hzInter
            simpa using this
          have hxRel := hXalpha xAlpha hxAlphaX
          rw [(orient alpha).relativeInterior_eq] at hxRel
          exact hxRel.2 (by simp [← hzx, hzt])
        by_cases hzu : z = D.vertexPlacement u
        · simp [hzu]
        have hzAlphaRel : z ∈ (orient alpha).relativeInterior := by
          rw [(orient alpha).relativeInterior_eq]
          refine ⟨AlphaCut.prefix_carrier_subset hz.1, ?_⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨fun hs => hzu (hs.trans (orient_source alpha huAlpha)), hzAlphaTarget⟩
        have hzBetaRel : z ∈ (orient beta).relativeInterior := by
          rw [(orient beta).relativeInterior_eq]
          refine ⟨hz.2, ?_⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          constructor
          · intro hs
            exact hzu (hs.trans (orient_source beta huBeta))
          · intro ht
            rcases orient_target_vertex beta with ⟨v, htv⟩
            have hzOldAlpha : z ∈ (D.edgeArc alpha).relativeInterior := by
              simpa only [orient_relative alpha] using hzAlphaRel
            exact D.no_vertex_in_edge_interior v alpha (ht.trans htv ▸ hzOldAlpha)
        have hzX : z ∈ X := by
          apply Finset.mem_filter.mpr
          refine ⟨(D.crossingSet_spec z).2 ⟨alpha, beta, hab, ?_, ?_⟩, ?_, ?_⟩
          · simpa only [orient_relative alpha] using hzAlphaRel
          · simpa only [orient_relative beta] using hzBetaRel
          · simpa only [orient_relative alpha] using hzAlphaRel
          · simpa only [orient_relative beta] using hzBetaRel
        have hzx := hAlphaMinimal z hzX hz.1
        simp [hzx]
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hzu | hzx
        · subst z
          constructor
          · have hs := favorableTailFreeArcSourceMem AlphaCut.prefixArc
            rw [AlphaCut.prefix_source, orient_source alpha huAlpha] at hs
            exact hs
          · rw [← orient_source beta huBeta]
            exact favorableTailFreeArcSourceMem (orient beta)
        · subst z
          constructor
          · have ht := favorableTailFreeArcTargetMem AlphaCut.prefixArc
            rw [AlphaCut.prefix_target] at ht
            exact ht
          · have hr := hXbeta xAlpha hxAlphaX
            rw [(orient beta).relativeInterior_eq] at hr
            exact hr.1
    have betaPrefixAlpha :
        BetaCut.prefixArc.carrier ∩ (orient alpha).carrier =
          ({D.vertexPlacement u, xBeta} : Set _) := by
      ext z
      constructor
      · intro hz
        have hzBetaTarget : z ≠ (orient beta).target := by
          intro hzt
          have htSuffix : (orient beta).target ∈ BetaCut.suffixArc.carrier := by
            rw [← BetaCut.suffix_target]
            exact favorableTailFreeArcTargetMem BetaCut.suffixArc
          have hzInter : z ∈ BetaCut.prefixArc.carrier ∩
              BetaCut.suffixArc.carrier := ⟨hz.1, hzt ▸ htSuffix⟩
          have hzx : z = xBeta := by
            have : z ∈ ({xBeta} : Set _) := BetaCut.carrier_intersection ▸ hzInter
            simpa using this
          have hxRel := hXbeta xBeta hxBetaX
          rw [(orient beta).relativeInterior_eq] at hxRel
          exact hxRel.2 (by simp [← hzx, hzt])
        by_cases hzu : z = D.vertexPlacement u
        · simp [hzu]
        have hzBetaRel : z ∈ (orient beta).relativeInterior := by
          rw [(orient beta).relativeInterior_eq]
          refine ⟨BetaCut.prefix_carrier_subset hz.1, ?_⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨fun hs => hzu (hs.trans (orient_source beta huBeta)), hzBetaTarget⟩
        have hzAlphaRel : z ∈ (orient alpha).relativeInterior := by
          rw [(orient alpha).relativeInterior_eq]
          refine ⟨hz.2, ?_⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          constructor
          · intro hs
            exact hzu (hs.trans (orient_source alpha huAlpha))
          · intro ht
            rcases orient_target_vertex alpha with ⟨v, htv⟩
            have hzOldBeta : z ∈ (D.edgeArc beta).relativeInterior := by
              simpa only [orient_relative beta] using hzBetaRel
            exact D.no_vertex_in_edge_interior v beta (ht.trans htv ▸ hzOldBeta)
        have hzX : z ∈ X := by
          apply Finset.mem_filter.mpr
          refine ⟨(D.crossingSet_spec z).2 ⟨beta, alpha, hab.symm, ?_, ?_⟩, ?_, ?_⟩
          · simpa only [orient_relative beta] using hzBetaRel
          · simpa only [orient_relative alpha] using hzAlphaRel
          · simpa only [orient_relative alpha] using hzAlphaRel
          · simpa only [orient_relative beta] using hzBetaRel
        have hzx := hBetaMinimal z hzX hz.1
        simp [hzx]
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hzu | hzx
        · subst z
          constructor
          · have hs := favorableTailFreeArcSourceMem BetaCut.prefixArc
            rw [BetaCut.prefix_source, orient_source beta huBeta] at hs
            exact hs
          · rw [← orient_source alpha huAlpha]
            exact favorableTailFreeArcSourceMem (orient alpha)
        · subst z
          constructor
          · have ht := favorableTailFreeArcTargetMem BetaCut.prefixArc
            rw [BetaCut.prefix_target] at ht
            exact ht
          · have hr := hXalpha xBeta hxBetaX
            rw [(orient alpha).relativeInterior_eq] at hr
            exact hr.1
    have outgoing_package (Q : PolygonalArc) (x : EuclideanSpace ℝ (Fin 2))
        (Cut : PolygonalArcPointCutData Q x)
        (hQsource : Q.source = D.vertexPlacement u)
        (hxrel : x ∈ Q.relativeInterior) :
        ∃ y : EuclideanSpace ℝ (Fin 2),
          ∃ OutCut : PolygonalArcPointCutData Cut.suffixArc y,
            y ∈ Q.relativeInterior ∧ y ≠ x ∧
            OutCut.prefixArc.carrier = segment ℝ x y ∧
            (∀ p, p ∈ OutCut.prefixArc.carrier → p ∈ D.crossingSet → p = x) ∧
            Cut.prefixArc.carrier ∩ OutCut.prefixArc.carrier = ({x} : Set _) ∧
            ∀ P : Set (EuclideanSpace ℝ (Fin 2)),
              P ∩ Q.carrier = ({D.vertexPlacement u, x} : Set _) →
                Disjoint P OutCut.suffixArc.carrier := by
      let S := Cut.suffixArc
      have hS0 : S.vertices[0]'(by
          have := S.length_ge_two
          omega) = x := by
        have hlen := S.length_ge_two
        have hhead := S.source_eq_head
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by
          have := S.length_ge_two
          omega)] at hhead
        exact Option.some.inj hhead |>.trans Cut.suffix_source
      have hS01 : 0 + 1 < S.vertices.length := by
        have := S.length_ge_two
        omega
      have hS01ne : S.vertices[0] ≠ S.vertices[1] := by
        intro heq
        have hidx := (S.simple_vertices.getElem_inj_iff
          (i := 0) (j := 1) (hi := by omega) (hj := hS01)).1 heq
        omega
      obtain ⟨y, hyOpen0, hshort⟩ :=
        ordinaryAdjacentEdgesChooseShort G D S x hS01 hS0 hS01ne
      have hyne : y ≠ x := by
        intro hyx
        have hleft : S.vertices[0] ∈ openSegment ℝ S.vertices[0] S.vertices[1] := by
          simpa [hS0, hyx] using hyOpen0
        exact hS01ne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hleft)
      obtain ⟨OutCut⟩ :=
        PolygonalArcInteriorPointCutDataExists S 0 hS01 y hyOpen0
      have hOutIndex : OutCut.cutIndex = 0 :=
        (favorableTailFreeOpenIndexUnique S y 0 OutCut.cutIndex hS01
          OutCut.cutIndex_valid
          hyOpen0 OutCut.cut_mem_segment).symm
      have hOutCarrier : OutCut.prefixArc.carrier = segment ℝ x y := by
        rw [OutCut.prefix_carrier_region]
        have hEarlier :
            {z | ∃ i : ℕ, ∃ hi : i + 1 < S.vertices.length,
              i < OutCut.cutIndex ∧ z ∈ segment ℝ S.vertices[i] S.vertices[i + 1]} =
              (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          ext z
          simp [hOutIndex]
        rw [hEarlier, Set.empty_union]
        simpa only [hOutIndex, hS0]
      have hOutCross : ∀ p, p ∈ OutCut.prefixArc.carrier →
          p ∈ D.crossingSet → p = x := by
        intro p hp hpCross
        apply hshort p
        · rw [hOutCarrier] at hp
          simpa only [hS0] using hp
        · exact hpCross
      have hySrel : y ∈ S.relativeInterior :=
        PolygonalArcOpenSegmentSubsetRelativeInterior S 0 hS01 hyOpen0
      have hyQcarrier : y ∈ Q.carrier :=
        Cut.suffix_carrier_subset ((S.relativeInterior_eq ▸ hySrel).1)
      have hyQsource : y ≠ Q.source := by
        intro hySource
        have hsourcePrefix : Q.source ∈ Cut.prefixArc.carrier := by
          have hs := favorableTailFreeArcSourceMem Cut.prefixArc
          rw [Cut.prefix_source] at hs
          exact hs
        have hyInter : y ∈ Cut.prefixArc.carrier ∩ S.carrier := by
          refine ⟨hySource ▸ hsourcePrefix, (S.relativeInterior_eq ▸ hySrel).1⟩
        have hyx : y = x := by
          have : y ∈ ({x} : Set _) := Cut.carrier_intersection ▸ hyInter
          simpa using this
        exact hyne hyx
      have hyQtarget : y ≠ Q.target := by
        intro hyTarget
        have hyNotSTarget : y ≠ S.target := by
          rw [S.relativeInterior_eq] at hySrel
          exact fun h => hySrel.2 (by simp [h])
        exact hyNotSTarget (hyTarget.trans Cut.suffix_target.symm)
      have hyQrel : y ∈ Q.relativeInterior := by
        rw [Q.relativeInterior_eq]
        refine ⟨hyQcarrier, ?_⟩
        simp [hyQsource, hyQtarget]
      have hPrefixOut : Cut.prefixArc.carrier ∩ OutCut.prefixArc.carrier =
          ({x} : Set _) := by
        ext z
        constructor
        · intro hz
          have hzS : z ∈ S.carrier :=
            OutCut.prefix_carrier_subset hz.2
          have hzCut : z ∈ Cut.prefixArc.carrier ∩ S.carrier := ⟨hz.1, hzS⟩
          exact Cut.carrier_intersection ▸ hzCut
        · intro hz
          have hzx : z = x := by simpa using hz
          subst z
          constructor
          · have ht := favorableTailFreeArcTargetMem Cut.prefixArc
            rw [Cut.prefix_target] at ht
            exact ht
          · have hs := favorableTailFreeArcSourceMem OutCut.prefixArc
            rw [OutCut.prefix_source, Cut.suffix_source] at hs
            exact hs
      refine ⟨y, OutCut, hyQrel, hyne, hOutCarrier, hOutCross, hPrefixOut, ?_⟩
      intro P hPQ
      rw [Set.disjoint_left]
      intro z hzP hzTail
      have hzQ : z ∈ Q.carrier :=
        Cut.suffix_carrier_subset (OutCut.suffix_carrier_subset hzTail)
      have hzPair : z ∈ ({D.vertexPlacement u, x} : Set _) := hPQ ▸ ⟨hzP, hzQ⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzPair
      rcases hzPair with hzu | hzx
      · have huPrefix : D.vertexPlacement u ∈ Cut.prefixArc.carrier := by
          have hs := favorableTailFreeArcSourceMem Cut.prefixArc
          rw [Cut.prefix_source, hQsource] at hs
          exact hs
        have huS : D.vertexPlacement u ∈ S.carrier :=
          OutCut.suffix_carrier_subset (hzu ▸ hzTail)
        have hux : D.vertexPlacement u = x := by
          have huInter : D.vertexPlacement u ∈ Cut.prefixArc.carrier ∩ S.carrier :=
            ⟨huPrefix, huS⟩
          have : D.vertexPlacement u ∈ ({x} : Set _) :=
            Cut.carrier_intersection ▸ huInter
          simpa using this
        rw [Q.relativeInterior_eq] at hxrel
        exact hxrel.2 (by simp [← hux, hQsource])
      · have hxOutPrefix : x ∈ OutCut.prefixArc.carrier := by
          have hs := favorableTailFreeArcSourceMem OutCut.prefixArc
          rw [OutCut.prefix_source, Cut.suffix_source] at hs
          exact hs
        have hxInter : x ∈ OutCut.prefixArc.carrier ∩ OutCut.suffixArc.carrier :=
          ⟨hxOutPrefix, hzx ▸ hzTail⟩
        have hxy : x = y := by
          have : x ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hxInter
          simpa using this
        exact hyne hxy.symm
    obtain ⟨yAlpha, OutAlpha, hyAlphaRel, hyAlphaNe, hOutAlphaCarrier,
        hOutAlphaCross, hBAlphaBplus, hAlphaTail⟩ :=
      outgoing_package (orient beta) xAlpha BetaAtAlpha
        (orient_source beta huBeta) (hXbeta xAlpha hxAlphaX)
    obtain ⟨yBeta, OutBeta, hyBetaRel, hyBetaNe, hOutBetaCarrier,
        hOutBetaCross, hABetaAplus, hBetaTail⟩ :=
      outgoing_package (orient alpha) xBeta AlphaAtBeta
        (orient_source alpha huAlpha) (hXalpha xBeta hxBetaX)
    have hAlphaTailDisjoint :
        Disjoint AlphaCut.prefixArc.carrier OutAlpha.suffixArc.carrier :=
      hAlphaTail AlphaCut.prefixArc.carrier alphaPrefixBeta
    have hBetaTailDisjoint :
        Disjoint BetaCut.prefixArc.carrier OutBeta.suffixArc.carrier :=
      hBetaTail BetaCut.prefixArc.carrier betaPrefixAlpha
    have hAlphaBetaPrefixes :
        AlphaCut.prefixArc.carrier ∩ BetaAtAlpha.prefixArc.carrier =
          ({D.vertexPlacement u, xAlpha} : Set _) := by
      ext z
      constructor
      · intro hz
        have hzWhole : z ∈ AlphaCut.prefixArc.carrier ∩ (orient beta).carrier :=
          ⟨hz.1, BetaAtAlpha.prefix_carrier_subset hz.2⟩
        exact alphaPrefixBeta ▸ hzWhole
      · intro hz
        have hzPair : z = D.vertexPlacement u ∨ z = xAlpha := by simpa using hz
        constructor
        · exact (alphaPrefixBeta ▸ hz).1
        · rcases hzPair with hzu | hzx
          · subst z
            have hs := favorableTailFreeArcSourceMem BetaAtAlpha.prefixArc
            rw [BetaAtAlpha.prefix_source, orient_source beta huBeta] at hs
            exact hs
          · subst z
            have ht := favorableTailFreeArcTargetMem BetaAtAlpha.prefixArc
            rw [BetaAtAlpha.prefix_target] at ht
            exact ht
    have hBetaAlphaPrefixes :
        BetaCut.prefixArc.carrier ∩ AlphaAtBeta.prefixArc.carrier =
          ({D.vertexPlacement u, xBeta} : Set _) := by
      ext z
      constructor
      · intro hz
        have hzWhole : z ∈ BetaCut.prefixArc.carrier ∩ (orient alpha).carrier :=
          ⟨hz.1, AlphaAtBeta.prefix_carrier_subset hz.2⟩
        exact betaPrefixAlpha ▸ hzWhole
      · intro hz
        have hzPair : z = D.vertexPlacement u ∨ z = xBeta := by simpa using hz
        constructor
        · exact (betaPrefixAlpha ▸ hz).1
        · rcases hzPair with hzu | hzx
          · subst z
            have hs := favorableTailFreeArcSourceMem AlphaAtBeta.prefixArc
            rw [AlphaAtBeta.prefix_source, orient_source alpha huAlpha] at hs
            exact hs
          · subst z
            have ht := favorableTailFreeArcTargetMem AlphaAtBeta.prefixArc
            rw [AlphaAtBeta.prefix_target] at ht
            exact ht
    let third : EuclideanSpace ℝ (Fin 2) → Prop := fun p =>
      ∃ e : G.edgeFinset, e ≠ alpha ∧ e ≠ beta ∧
        p ∈ (D.edgeArc e).relativeInterior
    let contacts : PolygonalArc → Finset (EuclideanSpace ℝ (Fin 2)) := fun P =>
      D.crossingSet.filter (fun p => p ∈ P.carrier ∧ third p)
    have contacts_mono : ∀ P Q : PolygonalArc,
        P.carrier ⊆ Q.carrier → contacts P ⊆ contacts Q := by
      intro P Q hPQ p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hPQ hp.2.1, hp.2.2⟩
    have hAlphaContactsMono :
        contacts AlphaCut.prefixArc ⊆ contacts AlphaAtBeta.prefixArc :=
      contacts_mono _ _ hAlphaPrefixInBeta
    have hBetaContactsMono :
        contacts BetaCut.prefixArc ⊆ contacts BetaAtAlpha.prefixArc :=
      contacts_mono _ _ hBetaPrefixInAlpha
    have hAlphaCardMono :
        (contacts AlphaCut.prefixArc).card ≤
          (contacts AlphaAtBeta.prefixArc).card :=
      Finset.card_le_card hAlphaContactsMono
    have hBetaCardMono :
        (contacts BetaCut.prefixArc).card ≤
          (contacts BetaAtAlpha.prefixArc).card :=
      Finset.card_le_card hBetaContactsMono
    have contacts_spec (e : G.edgeFinset) (hu : u ∈ e.1)
        (he : e = alpha ∨ e = beta)
        (x : EuclideanSpace ℝ (Fin 2))
        (hxA : x ∈ (D.edgeArc alpha).relativeInterior)
        (hxB : x ∈ (D.edgeArc beta).relativeInterior)
        (Cut : PolygonalArcPointCutData (orient e) x) :
        ∀ p, p ∈ contacts Cut.prefixArc ↔
          p ∈ Cut.prefixArc.carrier \
              ({D.vertexPlacement u, x} : Set _) ∧ third p := by
      intro p
      constructor
      · intro hp
        rw [Finset.mem_filter] at hp
        rcases hp.2.2 with ⟨f, hfA, hfB, hpf⟩
        have hpu : p ≠ D.vertexPlacement u := by
          intro h
          exact D.no_vertex_in_edge_interior u f (h ▸ hpf)
        have hpx : p ≠ x := by
          intro h
          exact D.no_three_edge_interiors_meet hab hfA.symm hfB.symm
            hxA hxB (h ▸ hpf)
        exact ⟨⟨hp.2.1, by simp [hpu, hpx]⟩, ⟨f, hfA, hfB, hpf⟩⟩
      · rintro ⟨⟨hpPrefix, hpEnds⟩, hpThird⟩
        have hpne : p ≠ D.vertexPlacement u ∧ p ≠ x := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hpEnds
        rcases hpThird with ⟨f, hfA, hfB, hpf⟩
        have hpe : p ∈ (D.edgeArc e).relativeInterior :=
          favorableTailFreePrefixInterior G D e u (orient e) x Cut p
            (orient_source e hu) (orient_relative e) hpPrefix hpne.1 hpne.2
        have hef : e ≠ f := by
          rcases he with rfl | rfl
          · exact hfA.symm
          · exact hfB.symm
        apply Finset.mem_filter.mpr
        exact ⟨(D.crossingSet_spec p).2 ⟨e, f, hef, hpe, hpf⟩,
          hpPrefix, ⟨f, hfA, hfB, hpf⟩⟩
    have hAlphaFirstSpec := contacts_spec alpha huAlpha (Or.inl rfl) xAlpha
      (Finset.mem_filter.mp hxAlphaX).2.1 (Finset.mem_filter.mp hxAlphaX).2.2
      AlphaCut
    have hBetaAtAlphaSpec := contacts_spec beta huBeta (Or.inr rfl) xAlpha
      (Finset.mem_filter.mp hxAlphaX).2.1 (Finset.mem_filter.mp hxAlphaX).2.2
      BetaAtAlpha
    have hBetaFirstSpec := contacts_spec beta huBeta (Or.inr rfl) xBeta
      (Finset.mem_filter.mp hxBetaX).2.1 (Finset.mem_filter.mp hxBetaX).2.2
      BetaCut
    have hAlphaAtBetaSpec := contacts_spec alpha huAlpha (Or.inl rfl) xBeta
      (Finset.mem_filter.mp hxBetaX).2.1 (Finset.mem_filter.mp hxBetaX).2.2
      AlphaAtBeta
    have geometry_package
        (firstEdge secondEdge : G.edgeFinset)
        (hpair : (firstEdge = alpha ∧ secondEdge = beta) ∨
          (firstEdge = beta ∧ secondEdge = alpha))
        (huFirst : u ∈ firstEdge.1) (huSecond : u ∈ secondEdge.1)
        (x y : EuclideanSpace ℝ (Fin 2))
        (FirstCut : PolygonalArcPointCutData (orient firstEdge) x)
        (SecondCut : PolygonalArcPointCutData (orient secondEdge) x)
        (OutCut : PolygonalArcPointCutData SecondCut.suffixArc y)
        (hxA : x ∈ (D.edgeArc alpha).relativeInterior)
        (hxB : x ∈ (D.edgeArc beta).relativeInterior)
        (hySecond : y ∈ (D.edgeArc secondEdge).relativeInterior)
        (hFirstWhole : FirstCut.prefixArc.carrier ∩
          (orient secondEdge).carrier = ({D.vertexPlacement u, x} : Set _))
        (hOutCarrier : OutCut.prefixArc.carrier = segment ℝ x y)
        (hOutCross : ∀ p, p ∈ OutCut.prefixArc.carrier →
          p ∈ D.crossingSet → p = x)
        (XAcopy XBremoved : Finset (EuclideanSpace ℝ (Fin 2)))
        (hXAcopy : ∀ p, p ∈ XAcopy ↔
          p ∈ FirstCut.prefixArc.carrier \
              ({D.vertexPlacement u, x} : Set _) ∧
            ∃ e : G.edgeFinset,
              e ≠ firstEdge ∧ e ≠ secondEdge ∧
                p ∈ (D.edgeArc e).relativeInterior)
        (hXBremoved : ∀ p, p ∈ XBremoved ↔
          p ∈ SecondCut.prefixArc.carrier \
              ({D.vertexPlacement u, x} : Set _) ∧
            ∃ e : G.edgeFinset,
              e ≠ firstEdge ∧ e ≠ secondEdge ∧
                p ∈ (D.edgeArc e).relativeInterior)
        (hcount : XAcopy.card ≤ XBremoved.card) :
        ∃ A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)),
          A = FirstCut.prefixArc.carrier ∧
          B = SecondCut.prefixArc.carrier ∧
          Bplus = OutCut.prefixArc.carrier ∧
          Rbeta = (D.edgeArc secondEdge).carrier \
            ((B ∪ Bplus) \ ({y} : Set _)) ∧
          H =
            (⋃ edge : G.edgeFinset,
              if edge = firstEdge then
                (D.edgeArc edge).carrier \
                  (A \ ({D.vertexPlacement u, x} : Set _))
              else if edge = secondEdge then
                (D.edgeArc edge).carrier \
                  ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
                    (Bplus \ ({x, y} : Set _)))
              else (D.edgeArc edge).carrier) ∪
            {p | ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v} ∧
          ∃ Tail : BigonRerouteOrderedBetaTailData
              G D secondEdge u y B Bplus Rbeta H,
            (∀ p, p ∈ Bplus → p ∈ D.crossingSet → p = x) ∧
            (∀ v : V, D.vertexPlacement v ∈ Bplus → False) ∧
            ∃ XAexact XBexact : Finset (EuclideanSpace ℝ (Fin 2)),
              XAexact = XAcopy ∧ XBremoved ⊆ XBexact ∧
              (∀ p, p ∈ XAexact ↔
                p ∈ A \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H) ∧
              (∀ p, p ∈ XBexact ↔
                p ∈ B \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H) ∧
              XAexact.card ≤ XBexact.card := by
      have hEdgesNe : firstEdge ≠ secondEdge := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hab
        · exact hab.symm
      have hxy : x ≠ y := by
        intro h
        apply favorableTailFreeArcSourceNeTarget OutCut.prefixArc
        rw [OutCut.prefix_source, OutCut.prefix_target, SecondCut.suffix_source, h]
      let A : Set (EuclideanSpace ℝ (Fin 2)) := FirstCut.prefixArc.carrier
      let B : Set (EuclideanSpace ℝ (Fin 2)) := SecondCut.prefixArc.carrier
      let Bplus : Set (EuclideanSpace ℝ (Fin 2)) := OutCut.prefixArc.carrier
      let Rbeta : Set (EuclideanSpace ℝ (Fin 2)) := OutCut.suffixArc.carrier
      let H : Set (EuclideanSpace ℝ (Fin 2)) :=
        (⋃ edge : G.edgeFinset,
          if edge = firstEdge then
            (D.edgeArc edge).carrier \
              (A \ ({D.vertexPlacement u, x} : Set _))
          else if edge = secondEdge then
            (D.edgeArc edge).carrier \
              ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
                (Bplus \ ({x, y} : Set _)))
          else (D.edgeArc edge).carrier) ∪
        {p | ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v}
      have hxBplus : x ∈ Bplus := by
        dsimp [Bplus]
        have hs := favorableTailFreeArcSourceMem OutCut.prefixArc
        rw [OutCut.prefix_source, SecondCut.suffix_source] at hs
        exact hs
      have hyBplus : y ∈ Bplus := by
        dsimp [Bplus]
        have ht := favorableTailFreeArcTargetMem OutCut.prefixArc
        rw [OutCut.prefix_target] at ht
        exact ht
      have hyTail : y ∈ Rbeta := by
        dsimp [Rbeta]
        have hs := favorableTailFreeArcSourceMem OutCut.suffixArc
        rw [OutCut.suffix_source] at hs
        exact hs
      have hxNotTail : x ∉ Rbeta := by
        intro hxTail
        have hxInter : x ∈ OutCut.prefixArc.carrier ∩ OutCut.suffixArc.carrier :=
          ⟨hxBplus, hxTail⟩
        have : x ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hxInter
        exact hxy (by simpa using this)
      have hyNotB : y ∉ B := by
        intro hyB
        have hySuffix : y ∈ SecondCut.suffixArc.carrier :=
          OutCut.prefix_carrier_subset hyBplus
        have hyInter : y ∈ SecondCut.prefixArc.carrier ∩
            SecondCut.suffixArc.carrier := ⟨hyB, hySuffix⟩
        have : y ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hyInter
        have hyx : y = x := by simpa using this
        exact hxy hyx.symm
      have hTailOld : Rbeta ⊆ (D.edgeArc secondEdge).carrier := by
        intro p hp
        have hpOrient : p ∈ (orient secondEdge).carrier :=
          SecondCut.suffix_carrier_subset (OutCut.suffix_carrier_subset hp)
        rw [orient_carrier secondEdge] at hpOrient
        exact hpOrient
      have hRbetaExact :
          Rbeta = (D.edgeArc secondEdge).carrier \
            ((B ∪ Bplus) \ ({y} : Set _)) := by
        ext p
        constructor
        · intro hp
          refine ⟨hTailOld hp, ?_⟩
          rintro ⟨hpB | hpBplus, hpy⟩
          · have hpSuffix : p ∈ SecondCut.suffixArc.carrier :=
              OutCut.suffix_carrier_subset hp
            have hpInter : p ∈ SecondCut.prefixArc.carrier ∩
                SecondCut.suffixArc.carrier := ⟨hpB, hpSuffix⟩
            have hpx : p = x := by
              have : p ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hpInter
              simpa using this
            exact hxNotTail (hpx ▸ hp)
          · have hpInter : p ∈ OutCut.prefixArc.carrier ∩
                OutCut.suffixArc.carrier := ⟨hpBplus, hp⟩
            have hpy' : p = y := by
              have : p ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hpInter
              simpa using this
            exact hpy (by simp [hpy'])
        · rintro ⟨hpOld, hpNotRemoved⟩
          have hpOrient : p ∈ (orient secondEdge).carrier := by
            rw [orient_carrier secondEdge]
            exact hpOld
          rw [SecondCut.carrier_decomposition] at hpOrient
          rcases hpOrient with hpB | hpSuffix
          · exfalso
            apply hpNotRemoved
            refine ⟨Or.inl hpB, ?_⟩
            intro hpy
            have : p = y := by simpa using hpy
            exact hyNotB (this ▸ hpB)
          · rw [OutCut.carrier_decomposition] at hpSuffix
            rcases hpSuffix with hpBplus | hpTail
            · by_cases hpy : p = y
              · simpa [hpy] using hyTail
              · exfalso
                exact hpNotRemoved ⟨Or.inr hpBplus, by simpa using hpy⟩
            · exact hpTail
      have hTailRelative : OutCut.suffixArc.relativeInterior ⊆
          (D.edgeArc secondEdge).relativeInterior := by
        intro p hp
        rw [(D.edgeArc secondEdge).relativeInterior_eq]
        refine ⟨hTailOld ((OutCut.suffixArc.relativeInterior_eq ▸ hp).1), ?_⟩
        have hpOrientTarget : p ≠ (orient secondEdge).target := by
          intro hpt
          rw [OutCut.suffixArc.relativeInterior_eq] at hp
          apply hp.2
          right
          rw [OutCut.suffix_target, SecondCut.suffix_target]
          exact hpt
        have hpOrientSource : p ≠ (orient secondEdge).source := by
          intro hps
          have huB : (orient secondEdge).source ∈ SecondCut.prefixArc.carrier := by
            have hs := favorableTailFreeArcSourceMem SecondCut.prefixArc
            rw [SecondCut.prefix_source] at hs
            exact hs
          have hpSuffix : p ∈ SecondCut.suffixArc.carrier :=
            OutCut.suffix_carrier_subset ((OutCut.suffixArc.relativeInterior_eq ▸ hp).1)
          have hpInter : p ∈ SecondCut.prefixArc.carrier ∩
              SecondCut.suffixArc.carrier := ⟨hps ▸ huB, hpSuffix⟩
          have hpx : p = x := by
            have : p ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hpInter
            simpa using this
          exact hxNotTail (hpx ▸ ((OutCut.suffixArc.relativeInterior_eq ▸ hp).1))
        by_cases hs : (D.edgeArc secondEdge).source = D.vertexPlacement u
        · simp only [orient, if_pos hs] at hpOrientSource hpOrientTarget
          simpa [hpOrientSource, hpOrientTarget]
        · simp only [orient, if_neg hs, PolygonalArcReverse] at hpOrientSource hpOrientTarget
          simpa [hpOrientSource, hpOrientTarget, and_comm]
      have hTailRemoved : OutCut.suffixArc.carrier ∩ (B ∪ Bplus) =
          ({y} : Set _) := by
        ext p
        constructor
        · rintro ⟨hpTail, hpB | hpBplus⟩
          · have hpSuffix := OutCut.suffix_carrier_subset hpTail
            have hpInter : p ∈ SecondCut.prefixArc.carrier ∩
                SecondCut.suffixArc.carrier := ⟨hpB, hpSuffix⟩
            have hpx : p = x := by
              have : p ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hpInter
              simpa using this
            exact (hxNotTail (hpx ▸ hpTail)).elim
          · have hpInter : p ∈ OutCut.prefixArc.carrier ∩
                OutCut.suffixArc.carrier := ⟨hpBplus, hpTail⟩
            exact OutCut.carrier_intersection ▸ hpInter
        · intro hp
          have hpy : p = y := by simpa using hp
          subst p
          exact ⟨hyTail, Or.inr hyBplus⟩
      have hTailH : OutCut.suffixArc.carrier ⊆ H := by
        intro p hpTail
        left
        apply Set.mem_iUnion.mpr
        refine ⟨secondEdge, ?_⟩
        rw [if_neg hEdgesNe.symm, if_pos rfl]
        refine ⟨hTailOld hpTail, ?_⟩
        rintro (hpB | hpBplus)
        · have hpSuffix := OutCut.suffix_carrier_subset hpTail
          have hpInter : p ∈ SecondCut.prefixArc.carrier ∩
              SecondCut.suffixArc.carrier := ⟨hpB.1, hpSuffix⟩
          have hpx : p = x := by
            have : p ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hpInter
            simpa using this
          exact hpB.2 (by simp [hpx])
        · have hpInter : p ∈ OutCut.prefixArc.carrier ∩
              OutCut.suffixArc.carrier := ⟨hpBplus.1, hpTail⟩
          have hpy : p = y := by
            have : p ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hpInter
            simpa using this
          exact hpBplus.2 (by simp [hpy])
      have orient_target_data (e : G.edgeFinset) :
          ∃ v : V, v ∈ e.1 ∧ (orient e).target = D.vertexPlacement v := by
        rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, he, hends⟩
        dsimp [orient]
        by_cases hs : (D.edgeArc e).source = D.vertexPlacement u
        · simp only [if_pos hs]
          rcases hends with hends | hends
          · refine ⟨b, ?_, hends.2⟩
            rw [he]
            simp [Sym2.mem_iff']
          · refine ⟨a, ?_, hends.2⟩
            rw [he]
            simp [Sym2.mem_iff']
        · simp only [if_neg hs, PolygonalArcReverse]
          rcases hends with hends | hends
          · refine ⟨a, ?_, hends.1⟩
            rw [he]
            simp [Sym2.mem_iff']
          · refine ⟨b, ?_, hends.1⟩
            rw [he]
            simp [Sym2.mem_iff']
      obtain ⟨far, hfarMem, hOrientTarget⟩ := orient_target_data secondEdge
      have hfarNe : far ≠ u := by
        intro h
        apply favorableTailFreeArcSourceNeTarget (orient secondEdge)
        rw [orient_source secondEdge huSecond, hOrientTarget, h]
      have hTailTarget : OutCut.suffixArc.target = D.vertexPlacement far := by
        rw [OutCut.suffix_target, SecondCut.suffix_target, hOrientTarget]
      have hOldOrientation :
          ((D.edgeArc secondEdge).source = D.vertexPlacement u →
              OutCut.suffixArc.target = (D.edgeArc secondEdge).target) ∧
            ((D.edgeArc secondEdge).target = D.vertexPlacement u →
              OutCut.suffixArc.target = (D.edgeArc secondEdge).source) := by
        constructor
        · intro hs
          have hOrient : orient secondEdge = D.edgeArc secondEdge := by
            simp [orient, hs]
          rw [OutCut.suffix_target, SecondCut.suffix_target, hOrient]
        · intro ht
          have hsne : (D.edgeArc secondEdge).source ≠ D.vertexPlacement u := by
            intro hs
            exact favorableTailFreeArcSourceNeTarget (D.edgeArc secondEdge)
              (hs.trans ht.symm)
          have hOrient : (orient secondEdge).target =
              (D.edgeArc secondEdge).source := by
            simp [orient, hsne, PolygonalArcReverse]
          rw [OutCut.suffix_target, SecondCut.suffix_target, hOrient]
      let Tail : BigonRerouteOrderedBetaTailData
          G D secondEdge u y B Bplus Rbeta H :=
        { tailArc := OutCut.suffixArc
          farEndpoint := far
          u_mem_beta := huSecond
          farEndpoint_mem_beta := hfarMem
          farEndpoint_ne_u := hfarNe
          source_eq := OutCut.suffix_source
          target_eq := hTailTarget
          carrier_eq := rfl
          carrier_subset_old_beta := hTailOld
          relativeInterior_subset_old_beta := hTailRelative
          meets_removed_subarc := hTailRemoved
          carrier_subset_H := hTailH
          old_orientation_compatible := hOldOrientation }
      have hxFirst : x ∈ (D.edgeArc firstEdge).relativeInterior := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxA
        · exact hxB
      have hxSecond : x ∈ (D.edgeArc secondEdge).relativeInterior := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxB
        · exact hxA
      have hBplusNoVertex : ∀ v : V,
          D.vertexPlacement v ∈ Bplus → False := by
        intro v hv
        have hvOrient : D.vertexPlacement v ∈ (orient secondEdge).carrier :=
          SecondCut.suffix_carrier_subset (OutCut.prefix_carrier_subset hv)
        have hvSource : D.vertexPlacement v ≠ (orient secondEdge).source := by
          intro hs
          have hvPrefix : D.vertexPlacement v ∈ SecondCut.prefixArc.carrier := by
            have hs' := favorableTailFreeArcSourceMem SecondCut.prefixArc
            rw [SecondCut.prefix_source] at hs'
            simpa [hs] using hs'
          have hvSuffix : D.vertexPlacement v ∈ SecondCut.suffixArc.carrier :=
            OutCut.prefix_carrier_subset hv
          have hvInter : D.vertexPlacement v ∈ SecondCut.prefixArc.carrier ∩
              SecondCut.suffixArc.carrier := ⟨hvPrefix, hvSuffix⟩
          have hvx : D.vertexPlacement v = x := by
            have : D.vertexPlacement v ∈ ({x} : Set _) :=
              SecondCut.carrier_intersection ▸ hvInter
            simpa using this
          exact D.no_vertex_in_edge_interior v secondEdge (hvx ▸ hxSecond)
        have hvTarget : D.vertexPlacement v ≠ (orient secondEdge).target := by
          intro ht
          have hvOutTail : D.vertexPlacement v ∈
              OutCut.prefixArc.carrier ∩ OutCut.suffixArc.carrier := by
            refine ⟨hv, ?_⟩
            have htargetTail := favorableTailFreeArcTargetMem OutCut.suffixArc
            rw [OutCut.suffix_target, SecondCut.suffix_target] at htargetTail
            simpa [ht] using htargetTail
          have hvy : D.vertexPlacement v = y := by
            have : D.vertexPlacement v ∈ ({y} : Set _) :=
              OutCut.carrier_intersection ▸ hvOutTail
            simpa using this
          exact D.no_vertex_in_edge_interior v secondEdge (hvy ▸ hySecond)
        have hvRel : D.vertexPlacement v ∈ (orient secondEdge).relativeInterior := by
          rw [(orient secondEdge).relativeInterior_eq]
          exact ⟨hvOrient, by simp [hvSource, hvTarget]⟩
        rw [orient_relative secondEdge] at hvRel
        exact D.no_vertex_in_edge_interior v secondEdge hvRel
      have firstContactThird : ∀ p,
          p ∈ A \ ({D.vertexPlacement u, x} : Set _) →
            (p ∈ H ↔
              ∃ e : G.edgeFinset,
                e ≠ firstEdge ∧ e ≠ secondEdge ∧
                  p ∈ (D.edgeArc e).relativeInterior) := by
        intro p hpA
        have hpEnds : p ≠ D.vertexPlacement u ∧ p ≠ x := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hpA.2
        have hpFirst : p ∈ (D.edgeArc firstEdge).relativeInterior :=
          favorableTailFreePrefixInterior G D firstEdge u (orient firstEdge)
            x FirstCut p (orient_source firstEdge huFirst)
            (orient_relative firstEdge) hpA.1 hpEnds.1 hpEnds.2
        have hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v := by
          intro v h
          exact D.no_vertex_in_edge_interior v firstEdge (h ▸ hpFirst)
        constructor
        · intro hpH
          rcases hpH with hpEdges | hpVertex
          · rcases Set.mem_iUnion.mp hpEdges with ⟨e, hpe⟩
            by_cases heFirst : e = firstEdge
            · subst e
              rw [if_pos rfl] at hpe
              exact (hpe.2 hpA).elim
            · rw [if_neg heFirst] at hpe
              by_cases heSecond : e = secondEdge
              · subst e
                rw [if_pos rfl] at hpe
                have hpOrientSecond : p ∈ (orient secondEdge).carrier := by
                  rw [orient_carrier secondEdge]
                  exact hpe.1
                have hpPair : p ∈ ({D.vertexPlacement u, x} : Set _) :=
                  hFirstWhole ▸ ⟨hpA.1, hpOrientSecond⟩
                exact (hpA.2 hpPair).elim
              · rw [if_neg heSecond] at hpe
                exact ⟨e, heFirst, heSecond,
                  favorableTailFreeCarrierRelativeOfNotVertex G D p hpNotVertex e hpe⟩
          · rcases hpVertex with ⟨v, _hv, hpv⟩
            exact (hpNotVertex v hpv).elim
        · rintro ⟨e, heFirst, heSecond, hpe⟩
          left
          apply Set.mem_iUnion.mpr
          refine ⟨e, ?_⟩
          rw [if_neg heFirst, if_neg heSecond]
          exact (D.edgeArc e).relativeInterior_eq ▸ hpe |>.1
      let XBexact : Finset (EuclideanSpace ℝ (Fin 2)) :=
        D.crossingSet.filter (fun p =>
          p ∈ B \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H)
      have secondContactCrossing : ∀ p,
          p ∈ B \ ({D.vertexPlacement u, x} : Set _) →
            p ∈ H → p ∈ D.crossingSet := by
        intro p hpB hpH
        have hpEnds : p ≠ D.vertexPlacement u ∧ p ≠ x := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hpB.2
        have hpSecond : p ∈ (D.edgeArc secondEdge).relativeInterior :=
          favorableTailFreePrefixInterior G D secondEdge u (orient secondEdge)
            x SecondCut p (orient_source secondEdge huSecond)
            (orient_relative secondEdge) hpB.1 hpEnds.1 hpEnds.2
        have hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v := by
          intro v h
          exact D.no_vertex_in_edge_interior v secondEdge (h ▸ hpSecond)
        rcases hpH with hpEdges | hpVertex
        · rcases Set.mem_iUnion.mp hpEdges with ⟨e, hpe⟩
          by_cases heFirst : e = firstEdge
          · subst e
            rw [if_pos rfl] at hpe
            have hpFirst : p ∈ (D.edgeArc firstEdge).relativeInterior :=
              favorableTailFreeCarrierRelativeOfNotVertex G D p hpNotVertex
                firstEdge hpe.1
            exact (D.crossingSet_spec p).2
              ⟨secondEdge, firstEdge, hEdgesNe.symm, hpSecond, hpFirst⟩
          · rw [if_neg heFirst] at hpe
            by_cases heSecond : e = secondEdge
            · subst e
              rw [if_pos rfl] at hpe
              exact (hpe.2 (Or.inl hpB)).elim
            · rw [if_neg heSecond] at hpe
              have hpOther : p ∈ (D.edgeArc e).relativeInterior :=
                favorableTailFreeCarrierRelativeOfNotVertex G D p hpNotVertex e hpe
              exact (D.crossingSet_spec p).2
                ⟨secondEdge, e, Ne.symm heSecond, hpSecond, hpOther⟩
        · rcases hpVertex with ⟨v, _hv, hpv⟩
          exact (hpNotVertex v hpv).elim
      have hXBexactSpec : ∀ p, p ∈ XBexact ↔
          p ∈ B \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H := by
        intro p
        rw [Finset.mem_filter]
        constructor
        · exact fun hp => hp.2
        · intro hp
          exact ⟨secondContactCrossing p hp.1 hp.2, hp⟩
      have hXBsubset : XBremoved ⊆ XBexact := by
        intro p hp
        rcases (hXBremoved p).1 hp with ⟨hpB, e, heFirst, heSecond, hpe⟩
        apply (hXBexactSpec p).2
        refine ⟨hpB, ?_⟩
        left
        apply Set.mem_iUnion.mpr
        refine ⟨e, ?_⟩
        rw [if_neg heFirst, if_neg heSecond]
        exact ((D.edgeArc e).relativeInterior_eq ▸ hpe).1
      have hXAexactSpec : ∀ p, p ∈ XAcopy ↔
          p ∈ A \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H := by
        intro p
        rw [hXAcopy p]
        constructor
        · rintro ⟨hpA, hpThird⟩
          exact ⟨hpA, (firstContactThird p hpA).2 hpThird⟩
        · rintro ⟨hpA, hpH⟩
          exact ⟨hpA, (firstContactThird p hpA).1 hpH⟩
      have hFinalCount : XAcopy.card ≤ XBexact.card :=
        le_trans hcount (Finset.card_le_card hXBsubset)
      refine ⟨A, B, Bplus, Rbeta, H, rfl, rfl, rfl, hRbetaExact, rfl,
        Tail, ?_, hBplusNoVertex, XAcopy, XBexact, rfl, hXBsubset,
        hXAexactSpec, hXBexactSpec, hFinalCount⟩
      intro p hpBplus hpCross
      exact hOutCross p hpBplus hpCross
    by_cases hFavorableAlpha :
        (contacts AlphaCut.prefixArc).card ≤
          (contacts BetaAtAlpha.prefixArc).card
    · refine ⟨alpha, beta, Or.inl ⟨rfl, rfl⟩, orient alpha, orient beta,
        orient_carrier alpha, orient_relative alpha, orient_source alpha huAlpha,
        orient_carrier beta, orient_relative beta, orient_source beta huBeta,
        xAlpha, yAlpha, AlphaCut, BetaAtAlpha, OutAlpha,
        orient_prefix_segment_transfer alpha xAlpha AlphaCut, ?_, ?_, ?_, ?_,
        hyAlphaNe, hOutAlphaCarrier, hAlphaBetaPrefixes, hBAlphaBplus,
        hAlphaTailDisjoint,
        contacts AlphaCut.prefixArc, contacts BetaAtAlpha.prefixArc,
        hAlphaFirstSpec, hBetaAtAlphaSpec, ⟨hFavorableAlpha, ?_⟩⟩
      · exact (Finset.mem_filter.mp hxAlphaX).1
      · exact (Finset.mem_filter.mp hxAlphaX).2.1
      · exact (Finset.mem_filter.mp hxAlphaX).2.2
      · simpa only [orient_relative beta] using hyAlphaRel
      · exact geometry_package alpha beta (Or.inl ⟨rfl, rfl⟩) huAlpha huBeta
          xAlpha yAlpha AlphaCut BetaAtAlpha OutAlpha
          (Finset.mem_filter.mp hxAlphaX).2.1
          (Finset.mem_filter.mp hxAlphaX).2.2
          (by simpa only [orient_relative beta] using hyAlphaRel)
          alphaPrefixBeta hOutAlphaCarrier hOutAlphaCross
          (contacts AlphaCut.prefixArc) (contacts BetaAtAlpha.prefixArc)
          hAlphaFirstSpec hBetaAtAlphaSpec hFavorableAlpha
    · have hFavorableBeta :
          (contacts BetaCut.prefixArc).card ≤
            (contacts AlphaAtBeta.prefixArc).card := by
        by_contra hnot
        push Not at hFavorableAlpha hnot
        omega
      refine ⟨beta, alpha, Or.inr ⟨rfl, rfl⟩, orient beta, orient alpha,
        orient_carrier beta, orient_relative beta, orient_source beta huBeta,
        orient_carrier alpha, orient_relative alpha, orient_source alpha huAlpha,
        xBeta, yBeta, BetaCut, AlphaAtBeta, OutBeta,
        orient_prefix_segment_transfer beta xBeta BetaCut, ?_, ?_, ?_, ?_,
        hyBetaNe, hOutBetaCarrier, hBetaAlphaPrefixes, hABetaAplus,
        hBetaTailDisjoint,
        contacts BetaCut.prefixArc, contacts AlphaAtBeta.prefixArc,
        ?_, ?_, ⟨hFavorableBeta, ?_⟩⟩
      · exact (Finset.mem_filter.mp hxBetaX).1
      · exact (Finset.mem_filter.mp hxBetaX).2.2
      · exact (Finset.mem_filter.mp hxBetaX).2.1
      · simpa only [orient_relative alpha] using hyBetaRel
      · intro p
        constructor
        · intro hp
          rcases (hBetaFirstSpec p).1 hp with ⟨hpPrefix, f, hfA, hfB, hpf⟩
          exact ⟨hpPrefix, f, hfB, hfA, hpf⟩
        · rintro ⟨hpPrefix, f, hfB, hfA, hpf⟩
          exact (hBetaFirstSpec p).2 ⟨hpPrefix, f, hfA, hfB, hpf⟩
      · intro p
        constructor
        · intro hp
          rcases (hAlphaAtBetaSpec p).1 hp with ⟨hpPrefix, f, hfA, hfB, hpf⟩
          exact ⟨hpPrefix, f, hfB, hfA, hpf⟩
        · rintro ⟨hpPrefix, f, hfB, hfA, hpf⟩
          exact (hAlphaAtBetaSpec p).2 ⟨hpPrefix, f, hfA, hfB, hpf⟩
      · apply geometry_package beta alpha (Or.inr ⟨rfl, rfl⟩) huBeta huAlpha
          xBeta yBeta BetaCut AlphaAtBeta OutBeta
          (Finset.mem_filter.mp hxBetaX).2.1
          (Finset.mem_filter.mp hxBetaX).2.2
          (by simpa only [orient_relative alpha] using hyBetaRel)
          betaPrefixAlpha hOutBetaCarrier hOutBetaCross
          (contacts BetaCut.prefixArc) (contacts AlphaAtBeta.prefixArc)
        · intro p
          constructor
          · intro hp
            rcases (hBetaFirstSpec p).1 hp with ⟨hpPrefix, f, hfA, hfB, hpf⟩
            exact ⟨hpPrefix, f, hfB, hfA, hpf⟩
          · rintro ⟨hpPrefix, f, hfB, hfA, hpf⟩
            exact (hBetaFirstSpec p).2 ⟨hpPrefix, f, hfA, hfB, hpf⟩
        · intro p
          constructor
          · intro hp
            rcases (hAlphaAtBetaSpec p).1 hp with ⟨hpPrefix, f, hfA, hfB, hpf⟩
            exact ⟨hpPrefix, f, hfB, hfA, hpf⟩
          · rintro ⟨hpPrefix, f, hfB, hfA, hpf⟩
            exact (hAlphaAtBetaSpec p).2 ⟨hpPrefix, f, hfA, hfB, hpf⟩
        · exact hFavorableBeta


lemma OrdinaryAdjacentEdgesFavorableTailFreeTerminalRefinement
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (alpha beta : G.edgeFinset) (u : V)
    (hopen : forall p : EuclideanSpace ℝ (Fin 2),
      p ∈ D.crossingSet ->
        p ∈ (D.edgeArc alpha).relativeInterior ->
          p ∈ (D.edgeArc beta).relativeInterior ->
            exists i j : ℕ,
              exists (hi : i + 1 < (D.edgeArc alpha).vertices.length)
                (hj : j + 1 < (D.edgeArc beta).vertices.length),
                p ∈ openSegment ℝ (D.edgeArc alpha).vertices[i]
                    (D.edgeArc alpha).vertices[i + 1] ∧
                  p ∈ openSegment ℝ (D.edgeArc beta).vertices[j]
                    (D.edgeArc beta).vertices[j + 1]) :
    alpha ≠ beta ->
      u ∈ alpha.1 ->
        u ∈ beta.1 ->
          (exists p : EuclideanSpace ℝ (Fin 2),
            p ∈ D.crossingSet ∧
              p ∈ (D.edgeArc alpha).relativeInterior ∧
                p ∈ (D.edgeArc beta).relativeInterior) ->
            exists firstEdge secondEdge : G.edgeFinset,
              (firstEdge = alpha ∧ secondEdge = beta ∨
                firstEdge = beta ∧ secondEdge = alpha) ∧
              exists firstArc secondArc : PolygonalArc,
                firstArc.carrier = (D.edgeArc firstEdge).carrier ∧
                firstArc.relativeInterior =
                  (D.edgeArc firstEdge).relativeInterior ∧
                firstArc.source = D.vertexPlacement u ∧
                secondArc.carrier = (D.edgeArc secondEdge).carrier ∧
                secondArc.relativeInterior =
                  (D.edgeArc secondEdge).relativeInterior ∧
                secondArc.source = D.vertexPlacement u ∧
                exists x y y' : EuclideanSpace ℝ (Fin 2),
                  exists FirstCut : PolygonalArcPointCutData firstArc x,
                    exists SecondCut : PolygonalArcPointCutData secondArc x,
                      exists OutCut :
                        PolygonalArcPointCutData SecondCut.suffixArc y,
                        x ∈ D.crossingSet ∧
                        x ∈ (D.edgeArc firstEdge).relativeInterior ∧
                        x ∈ (D.edgeArc secondEdge).relativeInterior ∧
                        y ∈ (D.edgeArc secondEdge).relativeInterior ∧
                        y ≠ x ∧
                        OutCut.prefixArc.carrier = segment ℝ x y ∧
                        FirstCut.prefixArc.carrier ∩
                            SecondCut.prefixArc.carrier =
                          ({D.vertexPlacement u, x} : Set _) ∧
                        SecondCut.prefixArc.carrier ∩
                            OutCut.prefixArc.carrier = ({x} : Set _) ∧
                        Disjoint FirstCut.prefixArc.carrier
                          OutCut.suffixArc.carrier ∧
                        exists A B BplusOld RbetaOld HOld :
                            Set (EuclideanSpace ℝ (Fin 2)),
                          A = FirstCut.prefixArc.carrier ∧
                          B = SecondCut.prefixArc.carrier ∧
                          BplusOld = OutCut.prefixArc.carrier ∧
                          RbetaOld =
                            (D.edgeArc secondEdge).carrier \
                              ((B ∪ BplusOld) \ ({y} : Set _)) ∧
                          HOld =
                            (⋃ edge : G.edgeFinset,
                              if edge = firstEdge then
                                (D.edgeArc edge).carrier \
                                  (A \
                                    ({D.vertexPlacement u, x} : Set _))
                              else if edge = secondEdge then
                                (D.edgeArc edge).carrier \
                                  ((B \
                                      ({D.vertexPlacement u, x} : Set _)) ∪
                                    (BplusOld \ ({x, y} : Set _)))
                              else (D.edgeArc edge).carrier) ∪
                            {p | exists v : V,
                              v ≠ u ∧ p = D.vertexPlacement v} ∧
                          exists TailOld : BigonRerouteOrderedBetaTailData
                              G D secondEdge u y B BplusOld RbetaOld HOld,
                            (forall p, p ∈ BplusOld ->
                              p ∈ D.crossingSet -> p = x) ∧
                            (forall v : V,
                              D.vertexPlacement v ∈ BplusOld -> False) ∧
                            exists XA XB :
                                Finset (EuclideanSpace ℝ (Fin 2)),
                              (forall p, p ∈ XA ↔
                                p ∈ A \
                                    ({D.vertexPlacement u, x} : Set _) ∧
                                  p ∈ HOld) ∧
                              (forall p, p ∈ XB ↔
                                p ∈ B \
                                    ({D.vertexPlacement u, x} : Set _) ∧
                                  p ∈ HOld) ∧
                              XA.card ≤ XB.card ∧
                              exists hxDisk : x ∈ D.crossingSet,
                                exists Disk : OrdinaryLabeledCrossingDiskData
                                  G D ⟨x, hxDisk⟩,
                                ((Disk.firstEdge = firstEdge ∧
                                    Disk.secondEdge = secondEdge) ∨
                                  (Disk.firstEdge = secondEdge ∧
                                    Disk.secondEdge = firstEdge)) ∧
                                exists i j : ℕ,
                                  exists (hi : i + 1 <
                                      (D.edgeArc firstEdge).vertices.length)
                                    (hj : j + 1 <
                                      (D.edgeArc secondEdge).vertices.length),
                                    x ∈ openSegment ℝ
                                        (D.edgeArc firstEdge).vertices[i]
                                        (D.edgeArc firstEdge).vertices[i + 1] ∧
                                    x ∈ openSegment ℝ
                                        (D.edgeArc secondEdge).vertices[j]
                                        (D.edgeArc secondEdge).vertices[j + 1] ∧
                                    (¬ ∃ c : ℝ,
                                      (D.edgeArc secondEdge).vertices[j + 1] -
                                          (D.edgeArc secondEdge).vertices[j] =
                                        c •
                                          ((D.edgeArc firstEdge).vertices[i + 1] -
                                            (D.edgeArc firstEdge).vertices[i])) ∧
                                    y' ∈ openSegment ℝ x y ∧
                                    segment ℝ x y' ⊆
                                      Metric.ball x Disk.radius ∧
                                    exists Bplus Rbeta H :
                                        Set (EuclideanSpace ℝ (Fin 2)),
                                      Bplus = segment ℝ x y' ∧
                                      Rbeta = segment ℝ y' y ∪ RbetaOld ∧
                                      Rbeta =
                                        (D.edgeArc secondEdge).carrier \
                                          ((B ∪ Bplus) \
                                            ({y'} : Set _)) ∧
                                      H =
                                        (⋃ edge : G.edgeFinset,
                                          if edge = firstEdge then
                                            (D.edgeArc edge).carrier \
                                              (A \
                                                ({D.vertexPlacement u, x} :
                                                  Set _))
                                          else if edge = secondEdge then
                                            (D.edgeArc edge).carrier \
                                              ((B \
                                                  ({D.vertexPlacement u, x} :
                                                    Set _)) ∪
                                                (Bplus \
                                                  ({x, y'} : Set _)))
                                          else (D.edgeArc edge).carrier) ∪
                                        {p | exists v : V,
                                          v ≠ u ∧
                                            p = D.vertexPlacement v} ∧
                                      exists Tail :
                                          BigonRerouteOrderedBetaTailData
                                            G D secondEdge u y' B Bplus Rbeta H,
                                        Tail.tailArc.carrier =
                                          segment ℝ y' y ∪
                                            TailOld.tailArc.carrier ∧
                                        Disjoint A Tail.tailArc.carrier ∧
                                        (forall p, p ∈ Bplus ->
                                          p ∈ D.crossingSet -> p = x) ∧
                                        (forall v : V,
                                          D.vertexPlacement v ∈ Bplus ->
                                            False) ∧
                                        (forall p, p ∈ XA ↔
                                          p ∈ A \
                                              ({D.vertexPlacement u, x} :
                                                Set _) ∧
                                            p ∈ H) ∧
                                        (forall p, p ∈ XB ↔
                                          p ∈ B \
                                              ({D.vertexPlacement u, x} :
                                                Set _) ∧
                                            p ∈ H) ∧
                                        XA.card ≤ XB.card ∧
                                        forall p i
                                            (hi : i + 1 <
                                              (D.edgeArc firstEdge).vertices.length),
                                          p ∈ openSegment ℝ
                                              (D.edgeArc firstEdge).vertices[i]
                                              (D.edgeArc firstEdge).vertices[i + 1] ->
                                          p ∈ FirstCut.prefixArc.carrier ->
                                          p ≠ x ->
                                          exists j : ℕ,
                                            exists hj : j + 1 <
                                                FirstCut.prefixArc.vertices.length,
                                              p ∈ openSegment ℝ
                                                  FirstCut.prefixArc.vertices[j]
                                                  FirstCut.prefixArc.vertices[j + 1] ∧
                                              exists scale : ℝ,
                                                scale ≠ 0 ∧
                                                FirstCut.prefixArc.vertices[j + 1] -
                                                    FirstCut.prefixArc.vertices[j] =
                                                  scale •
                                                    ((D.edgeArc firstEdge).vertices[i + 1] -
                                                      (D.edgeArc firstEdge).vertices[i]) := by
  intro hab huAlpha huBeta hcross
  have hcandidate :=
    favorableTailFreeCandidateWithTransfer G D alpha beta u hopen hab huAlpha
      huBeta hcross
  rcases hcandidate with
    ⟨firstEdge, secondEdge, hpair, firstArc, secondArc,
      hfirstCarrier, hfirstRelative, hfirstSource,
      hsecondCarrier, hsecondRelative, hsecondSource,
      x, y, FirstCut, SecondCut, OutCut, hFirstPrefixTransfer,
      hxCross, hxFirst, hxSecond, hySecond, hyx,
      hOutCarrier, hFirstSecond, hSecondOut, hFirstTail,
      _XAraw, _XBraw, _hXAraw, _hXBraw, _hrawCard,
      A, B, BplusOld, RbetaOld, HOld,
      hA, hB, hBplusOld, hRbetaOld, hHOld,
      TailOld, hBplusOldCross, hBplusOldVertex,
      XA, XB, _hXAeq, _hXBsubset, hXASpecOld, hXBSpecOld, hcard⟩
  have hedges : firstEdge ≠ secondEdge := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact hab.symm
  obtain ⟨Disk, _hDiskSmall⟩ :=
    OrdinaryLabeledCrossingDiskDataExistsBelow G D ⟨x, hxCross⟩ 1
      (by norm_num)
  have hownerFirst := Disk.owner_labels firstEdge hxFirst
  have hownerSecond := Disk.owner_labels secondEdge hxSecond
  have hDiskOwners :
      (Disk.firstEdge = firstEdge ∧ Disk.secondEdge = secondEdge) ∨
        (Disk.firstEdge = secondEdge ∧ Disk.secondEdge = firstEdge) := by
    rcases hownerFirst with hff | hfs <;>
      rcases hownerSecond with hsf | hss
    · exact False.elim (hedges (hff.trans hsf.symm))
    · exact Or.inl ⟨hff.symm, hss.symm⟩
    · exact Or.inr ⟨hsf.symm, hfs.symm⟩
    · exact False.elim (hedges (hfs.trans hss.symm))
  have hopenSelected :
      exists i j : ℕ,
        exists (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
          (hj : j + 1 < (D.edgeArc secondEdge).vertices.length),
          x ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
              (D.edgeArc firstEdge).vertices[i + 1] ∧
            x ∈ openSegment ℝ (D.edgeArc secondEdge).vertices[j]
              (D.edgeArc secondEdge).vertices[j + 1] := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hopen x hxCross hxFirst hxSecond
    · rcases hopen x hxCross hxSecond hxFirst with
        ⟨i, j, hi, hj, hxi, hxj⟩
      exact ⟨j, i, hj, hi, hxj, hxi⟩
  rcases hopenSelected with ⟨i, j, hi, hj, hxi, hxj⟩
  rcases D.transverse_intersections hedges hxFirst hxSecond with
    ⟨i0, j0, hi0, hj0, hxi0, hxj0, htrans0⟩
  have hii : i0 = i :=
    (favorableTailFreeOpenIndexUnique (D.edgeArc firstEdge) x i i0 hi hi0
      hxi hxi0).symm
  have hjj : j0 = j :=
    (favorableTailFreeOpenIndexUnique (D.edgeArc secondEdge) x j j0 hj hj0
      hxj hxj0).symm
  have htrans : ¬ ∃ c : ℝ,
      (D.edgeArc secondEdge).vertices[j + 1] -
          (D.edgeArc secondEdge).vertices[j] =
        c • ((D.edgeArc firstEdge).vertices[i + 1] -
          (D.edgeArc firstEdge).vertices[i]) := by
    simpa [hii, hjj] using htrans0
  have hxy : x ≠ y := hyx.symm
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  let t : ℝ := min (1 / 2) (Disk.radius / (2 * dist x y))
  have htpos : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num)
      (div_pos Disk.firstBranch.radius_pos (by positivity))
  have htlehalf : t ≤ 1 / 2 := by
    exact min_le_left _ _
  have htlt : t < 1 := htlehalf.trans_lt (by norm_num)
  let y' : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap x y t
  have hy'open : y' ∈ openSegment ℝ x y := by
    exact lineMap_mem_openSegment (𝕜 := ℝ) x y ⟨htpos, htlt⟩
  have hy'neX : y' ≠ x := by
    intro h
    have hxopen : x ∈ openSegment ℝ x y := h ▸ hy'open
    exact hxy ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hxopen)
  have hy'neY : y' ≠ y := by
    intro h
    have hyopen : y ∈ openSegment ℝ x y := h ▸ hy'open
    exact hxy ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hyopen)
  have hy'ball : y' ∈ Metric.ball x Disk.radius := by
    rw [Metric.mem_ball]
    dsimp [y']
    rw [dist_lineMap_left, Real.norm_of_nonneg htpos.le]
    have htbound : t ≤ Disk.radius / (2 * dist x y) := min_le_right _ _
    have hden : 0 < 2 * dist x y := by positivity
    have htwice : t * (2 * dist x y) ≤ Disk.radius :=
      (le_div_iff₀ hden).mp htbound
    nlinarith [Disk.firstBranch.radius_pos]
  have hsegmentBall : segment ℝ x y' ⊆ Metric.ball x Disk.radius :=
    (convex_ball x Disk.radius).segment_subset
      (Metric.mem_ball_self Disk.firstBranch.radius_pos) hy'ball
  have hy'seg : y' ∈ segment ℝ x y :=
    openSegment_subset_segment ℝ x y hy'open
  have hnewSubsetOld : segment ℝ x y' ⊆ BplusOld := by
    rw [hBplusOld, hOutCarrier]
    exact (convex_segment x y).segment_subset
      (left_mem_segment ℝ x y) hy'seg
  have hresidualSubsetOld : segment ℝ y' y ⊆ BplusOld := by
    rw [hBplusOld, hOutCarrier]
    exact (convex_segment x y).segment_subset hy'seg
      (right_mem_segment ℝ x y)
  let zeroParam : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let cutParam : Set.Icc (0 : ℝ) 1 := ⟨t, htpos.le, htlt.le⟩
  let oneParam : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hAdjacent :
      segment ℝ x y' ∩ segment ℝ y' y = ({y'} : Set _) := by
    have hraw := CollinearAdjacentSubsegmentsMeetAtEndpoint x y hxy
      zeroParam cutParam oneParam htpos htlt
    simpa [zeroParam, cutParam, oneParam, y'] using hraw
  have hSegmentDecomp :
      segment ℝ x y = segment ℝ x y' ∪ segment ℝ y' y := by
    apply Set.Subset.antisymm
    · intro p hp
      by_cases hpx : p = x
      · left
        simpa [hpx] using left_mem_segment ℝ x y'
      by_cases hpy : p = y
      · right
        simpa [hpy] using right_mem_segment ℝ y' y
      have hpopen : p ∈ openSegment ℝ x y :=
        mem_openSegment_of_ne_left_right (Ne.symm hpx) (Ne.symm hpy) hp
      have hy'range : y' ∈ Set.range
          (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
        exact ⟨t, rfl⟩
      have hpPieces := openSegment_subset_union x y hy'range hpopen
      rcases hpPieces with hpEq | hpLeft | hpRight
      · subst p
        exact Or.inl (right_mem_segment ℝ x y')
      · exact Or.inl (openSegment_subset_segment ℝ x y' hpLeft)
      · exact Or.inr (openSegment_subset_segment ℝ y' y hpRight)
    · intro p hp
      rcases hp with hp | hp
      · exact (convex_segment x y).segment_subset
          (left_mem_segment ℝ x y) hy'seg hp
      · exact (convex_segment x y).segment_subset hy'seg
          (right_mem_segment ℝ x y) hp
  have hBInterOld : B ∩ BplusOld = ({x} : Set _) := by
    rw [hB, hBplusOld, hSecondOut]
  have hxOld : x ∈ BplusOld := by
    rw [hBplusOld, hOutCarrier]
    exact left_mem_segment ℝ x y
  have hyOld : y ∈ BplusOld := by
    rw [hBplusOld, hOutCarrier]
    exact right_mem_segment ℝ x y
  have hy'Old : y' ∈ BplusOld := hnewSubsetOld
    (right_mem_segment ℝ x y')
  have hyNotB : y ∉ B := by
    intro hyB
    have hyx' : y = x := by
      have : y ∈ ({x} : Set _) := hBInterOld ▸ ⟨hyB, hyOld⟩
      simpa using this
    exact hyx hyx'
  have hy'NotB : y' ∉ B := by
    intro hy'B
    have hy'x : y' = x := by
      have : y' ∈ ({x} : Set _) := hBInterOld ▸ ⟨hy'B, hy'Old⟩
      simpa using this
    exact hy'neX hy'x
  have hxNotResidual : x ∉ segment ℝ y' y := by
    intro hxResidual
    have hxAtCut : x = y' := by
      have : x ∈ ({y'} : Set _) := hAdjacent ▸
        ⟨left_mem_segment ℝ x y', hxResidual⟩
      simpa using this
    exact hy'neX hxAtCut.symm
  have hyNotNew : y ∉ segment ℝ x y' := by
    intro hyNew
    have hyAtCut : y = y' := by
      have : y ∈ ({y'} : Set _) := hAdjacent ▸
        ⟨hyNew, right_mem_segment ℝ y' y⟩
      simpa using this
    exact hy'neY hyAtCut.symm
  have hOldTailCarrier : TailOld.tailArc.carrier = RbetaOld :=
    TailOld.carrier_eq
  have hOldTailInter :
      TailOld.tailArc.carrier ∩ (B ∪ BplusOld) = ({y} : Set _) :=
    TailOld.meets_removed_subarc
  have hResidualTail :
      segment ℝ y' y ∩ TailOld.tailArc.carrier = ({y} : Set _) := by
    ext p
    constructor
    · rintro ⟨hpResidual, hpTail⟩
      have hpOld : p ∈ BplusOld := hresidualSubsetOld hpResidual
      have hpAtY : p ∈ ({y} : Set _) := hOldTailInter ▸
        ⟨hpTail, Or.inr hpOld⟩
      exact hpAtY
    · intro hp
      have hpy : p = y := by simpa using hp
      subst p
      refine ⟨right_mem_segment ℝ y' y, ?_⟩
      have hs := favorableTailFreeArcSourceMem TailOld.tailArc
      simpa [TailOld.source_eq] using hs
  rcases StraightSegmentPolygonalArc y' y hy'neY with
    ⟨Residual, hResidualSource, hResidualTarget,
      hResidualCarrier, hResidualInterior⟩
  have hResidualTailArc :
      Residual.carrier ∩ TailOld.tailArc.carrier = ({y} : Set _) := by
    simpa [hResidualCarrier] using hResidualTail
  obtain ⟨TailArc, hTailSource, hTailTarget, hTailCarrier,
      hTailInteriorPieces⟩ :=
    favorableTailFreeGlueResidualTail G D secondEdge u y y'
      B BplusOld RbetaOld HOld TailOld Residual hy'neY hResidualSource
      hResidualTarget hResidualCarrier hResidualInterior hResidualTailArc
  let Bplus : Set (EuclideanSpace ℝ (Fin 2)) := segment ℝ x y'
  let Rbeta : Set (EuclideanSpace ℝ (Fin 2)) :=
    segment ℝ y' y ∪ RbetaOld
  let H : Set (EuclideanSpace ℝ (Fin 2)) :=
    (⋃ edge : G.edgeFinset,
      if edge = firstEdge then
        (D.edgeArc edge).carrier \
          (A \ ({D.vertexPlacement u, x} : Set _))
      else if edge = secondEdge then
        (D.edgeArc edge).carrier \
          ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
            (Bplus \ ({x, y'} : Set _)))
      else (D.edgeArc edge).carrier) ∪
    {p | exists v : V, v ≠ u ∧ p = D.vertexPlacement v}
  have hBplusOldCarrier : BplusOld ⊆ (D.edgeArc secondEdge).carrier := by
    intro p hp
    have hpOut : p ∈ OutCut.prefixArc.carrier := hBplusOld ▸ hp
    have hpSecondSuffix : p ∈ SecondCut.suffixArc.carrier :=
      OutCut.prefix_carrier_subset hpOut
    have hpSecond : p ∈ secondArc.carrier :=
      SecondCut.suffix_carrier_subset hpSecondSuffix
    simpa [hsecondCarrier] using hpSecond
  have hRbetaExact :
      Rbeta = (D.edgeArc secondEdge).carrier \
        ((B ∪ Bplus) \ ({y'} : Set _)) := by
    ext p
    constructor
    · intro hp
      rcases hp with hpResidual | hpOldTail
      · refine ⟨hBplusOldCarrier (hresidualSubsetOld hpResidual), ?_⟩
        rintro ⟨hpB | hpNew, hpNeCut⟩
        · have hpx : p = x := by
            have : p ∈ ({x} : Set _) := hBInterOld ▸
              ⟨hpB, hresidualSubsetOld hpResidual⟩
            simpa using this
          exact hxNotResidual (hpx ▸ hpResidual)
        · have hpAtCut : p = y' := by
            have : p ∈ ({y'} : Set _) := hAdjacent ▸
              ⟨hpNew, hpResidual⟩
            simpa using this
          exact hpNeCut (by simp [hpAtCut])
      · have hpTailCarrier : p ∈ TailOld.tailArc.carrier := by
          rw [hOldTailCarrier]
          exact hpOldTail
        refine ⟨TailOld.carrier_subset_old_beta hpTailCarrier, ?_⟩
        rintro ⟨hpB | hpNew, _hpNeCut⟩
        · have hpAtY : p = y := by
            have : p ∈ ({y} : Set _) := hOldTailInter ▸
              ⟨hpTailCarrier, Or.inl hpB⟩
            simpa using this
          exact hyNotB (hpAtY ▸ hpB)
        · have hpNewOld : p ∈ BplusOld := hnewSubsetOld hpNew
          have hpAtY : p = y := by
            have : p ∈ ({y} : Set _) := hOldTailInter ▸
              ⟨hpTailCarrier, Or.inr hpNewOld⟩
            simpa using this
          exact hyNotNew (hpAtY ▸ hpNew)
    · rintro ⟨hpOldCarrier, hpNotRemoved⟩
      by_cases hpOldTail : p ∈ RbetaOld
      · exact Or.inr hpOldTail
      have hpRemovedOld : p ∈ (B ∪ BplusOld) \ ({y} : Set _) := by
        by_contra hpNot
        apply hpOldTail
        rw [hRbetaOld]
        exact ⟨hpOldCarrier, hpNot⟩
      rcases hpRemovedOld.1 with hpB | hpBplus
      · by_cases hpCut : p = y'
        · exact False.elim (hy'NotB (hpCut ▸ hpB))
        · exact False.elim (hpNotRemoved ⟨Or.inl hpB, by simpa using hpCut⟩)
      · have hpSeg : p ∈ segment ℝ x y := by
          rw [← hOutCarrier, ← hBplusOld]
          exact hpBplus
        rw [hSegmentDecomp] at hpSeg
        rcases hpSeg with hpNew | hpResidual
        · by_cases hpCut : p = y'
          · exact Or.inl (by simpa [hpCut] using left_mem_segment ℝ y' y)
          · exact False.elim
              (hpNotRemoved ⟨Or.inr hpNew, by simpa using hpCut⟩)
        · exact Or.inl hpResidual
  have hTailCarrierRbeta : TailArc.carrier = Rbeta := by
    rw [hTailCarrier]
    simp only [Rbeta]
    rw [hOldTailCarrier]
  have hTailRelative :
      TailArc.relativeInterior ⊆ (D.edgeArc secondEdge).relativeInterior := by
    intro p hp
    have hpEnds : p ∉
        ({y', D.vertexPlacement TailOld.farEndpoint} : Set _) := by
      have hp' := hp
      rw [hTailInteriorPieces] at hp'
      exact hp'.2
    have hpCarrier : p ∈ TailArc.carrier :=
      (TailArc.relativeInterior_eq ▸ hp).1
    rw [hTailCarrier] at hpCarrier
    rcases hpCarrier with hpResidual | hpOldTail
    · apply favorableTailFreeCarrierRelativeOfNotVertex G D p
      · intro v hpv
        exact hBplusOldVertex v
          (hpv ▸ hresidualSubsetOld hpResidual)
      · exact hBplusOldCarrier (hresidualSubsetOld hpResidual)
    · by_cases hpy : p = y
      · simpa [hpy] using hySecond
      · apply TailOld.relativeInterior_subset_old_beta
        rw [TailOld.tailArc.relativeInterior_eq]
        refine ⟨hpOldTail, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨by simpa [TailOld.source_eq] using hpy, ?_⟩
        intro hpFar
        apply hpEnds
        exact Or.inr (hpFar.trans TailOld.target_eq)
  have hTailRemoved :
      TailArc.carrier ∩ (B ∪ Bplus) = ({y'} : Set _) := by
    ext p
    constructor
    · rintro ⟨hpTail, hpRemoved⟩
      rcases hpRemoved with hpB | hpNew
      · rw [hTailCarrier] at hpTail
        rcases hpTail with hpResidual | hpOldTail
        · have hpx : p = x := by
            have : p ∈ ({x} : Set _) := hBInterOld ▸
              ⟨hpB, hresidualSubsetOld hpResidual⟩
            simpa using this
          exact False.elim (hxNotResidual (hpx ▸ hpResidual))
        · have hpAtY : p = y := by
            have : p ∈ ({y} : Set _) := hOldTailInter ▸
              ⟨hpOldTail, Or.inl hpB⟩
            simpa using this
          exact False.elim (hyNotB (hpAtY ▸ hpB))
      · rw [hTailCarrier] at hpTail
        rcases hpTail with hpResidual | hpOldTail
        · have hpAtCut : p = y' := by
            have : p ∈ ({y'} : Set _) := hAdjacent ▸
              ⟨hpNew, hpResidual⟩
            simpa using this
          simpa [hpAtCut]
        · have hpAtY : p = y := by
            have : p ∈ ({y} : Set _) := hOldTailInter ▸
              ⟨hpOldTail, Or.inr (hnewSubsetOld hpNew)⟩
            simpa using this
          exact False.elim (hyNotNew (hpAtY ▸ hpNew))
    · intro hp
      have hpy' : p = y' := by simpa using hp
      subst p
      refine ⟨?_, Or.inr (right_mem_segment ℝ x y')⟩
      rw [hTailCarrier]
      exact Or.inl (left_mem_segment ℝ y' y)
  have hOutSuffixRbeta : OutCut.suffixArc.carrier = RbetaOld := by
    rw [hRbetaOld]
    ext p
    constructor
    · intro hpTail
      have hpSecondSuffix : p ∈ SecondCut.suffixArc.carrier :=
        OutCut.suffix_carrier_subset hpTail
      have hpSecond : p ∈ secondArc.carrier :=
        SecondCut.suffix_carrier_subset hpSecondSuffix
      refine ⟨by simpa [hsecondCarrier] using hpSecond, ?_⟩
      rintro ⟨hpB | hpOld, hpNeY⟩
      · have hpInter : p ∈ SecondCut.prefixArc.carrier ∩
            SecondCut.suffixArc.carrier := by
          exact ⟨hB ▸ hpB, hpSecondSuffix⟩
        have hpx : p = x := by
          have : p ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hpInter
          simpa using this
        have hxOut : x ∈ OutCut.prefixArc.carrier := by
          have hs := favorableTailFreeArcSourceMem OutCut.prefixArc
          simpa [OutCut.prefix_source, SecondCut.suffix_source] using hs
        have hxBoth : x ∈ OutCut.prefixArc.carrier ∩
            OutCut.suffixArc.carrier := ⟨hxOut, hpx ▸ hpTail⟩
        have hxy' : x = y := by
          have : x ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hxBoth
          simpa using this
        exact hxy hxy'
      · have hpInter : p ∈ OutCut.prefixArc.carrier ∩
            OutCut.suffixArc.carrier := ⟨hBplusOld ▸ hpOld, hpTail⟩
        have hpy : p = y := by
          have : p ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hpInter
          simpa using this
        exact hpNeY (by simp [hpy])
    · rintro ⟨hpOldCarrier, hpNotRemoved⟩
      have hpSecond : p ∈ secondArc.carrier := by
        simpa [hsecondCarrier] using hpOldCarrier
      rw [SecondCut.carrier_decomposition] at hpSecond
      rcases hpSecond with hpB | hpSuffix
      · exfalso
        apply hpNotRemoved
        refine ⟨Or.inl (hB ▸ hpB), ?_⟩
        intro hpy
        have : p = y := by simpa using hpy
        exact hyNotB (this ▸ (hB ▸ hpB))
      · rw [OutCut.carrier_decomposition] at hpSuffix
        rcases hpSuffix with hpOldPrefix | hpTail
        · by_cases hpy : p = y
          · subst p
            have hs := favorableTailFreeArcSourceMem OutCut.suffixArc
            simpa [OutCut.suffix_source] using hs
          · exfalso
            exact hpNotRemoved
              ⟨Or.inr (hBplusOld ▸ hpOldPrefix), by simpa using hpy⟩
        · exact hpTail
  have hOldTailOut : TailOld.tailArc.carrier = OutCut.suffixArc.carrier := by
    rw [hOldTailCarrier, hOutSuffixRbeta]
  have hAInterOld : A ∩ BplusOld = ({x} : Set _) := by
    ext p
    constructor
    · rintro ⟨hpA, hpOld⟩
      have hpNotVertex : forall v : V, p ≠ D.vertexPlacement v := by
        intro v hpv
        exact hBplusOldVertex v (hpv ▸ hpOld)
      have hpFirstCarrier : p ∈ (D.edgeArc firstEdge).carrier := by
        have hpFirstArc : p ∈ firstArc.carrier :=
          FirstCut.prefix_carrier_subset (hA ▸ hpA)
        simpa [hfirstCarrier] using hpFirstArc
      have hpFirstRel := favorableTailFreeCarrierRelativeOfNotVertex G D p
        hpNotVertex firstEdge hpFirstCarrier
      have hpSecondRel := favorableTailFreeCarrierRelativeOfNotVertex G D p
        hpNotVertex secondEdge (hBplusOldCarrier hpOld)
      have hpCross : p ∈ D.crossingSet :=
        (D.crossingSet_spec p).2
          ⟨firstEdge, secondEdge, hedges, hpFirstRel, hpSecondRel⟩
      have hpx := hBplusOldCross p hpOld hpCross
      simpa [hpx]
    · intro hp
      have hpx : p = x := by simpa using hp
      subst p
      refine ⟨?_, hxOld⟩
      rw [hA]
      have ht := favorableTailFreeArcTargetMem FirstCut.prefixArc
      simpa [FirstCut.prefix_target] using ht
  have hATail : Disjoint A TailArc.carrier :=
    favorableTailFreeDisjointNewTail A BplusOld x y' y FirstCut OutCut
      TailArc TailOld.tailArc hTailCarrier hAInterOld hresidualSubsetOld
      hxNotResidual hOldTailOut hFirstTail hA
  let Bremoved : Set (EuclideanSpace ℝ (Fin 2)) :=
    B \ ({D.vertexPlacement u, x} : Set _)
  let OldPlusRemoved : Set (EuclideanSpace ℝ (Fin 2)) :=
    BplusOld \ ({x, y} : Set _)
  let NewPlusRemoved : Set (EuclideanSpace ℝ (Fin 2)) :=
    Bplus \ ({x, y'} : Set _)
  have hSecondRetained :
      (D.edgeArc secondEdge).carrier \ (Bremoved ∪ NewPlusRemoved) =
        ((D.edgeArc secondEdge).carrier \
          (Bremoved ∪ OldPlusRemoved)) ∪ segment ℝ y' y := by
    ext p
    constructor
    · rintro ⟨hpCarrier, hpAvoidNew⟩
      by_cases hpAvoidOld : p ∉ Bremoved ∪ OldPlusRemoved
      · exact Or.inl ⟨hpCarrier, hpAvoidOld⟩
      · have hpOldRemoved : p ∈ Bremoved ∪ OldPlusRemoved :=
          Classical.byContradiction fun h => hpAvoidOld h
        rcases hpOldRemoved with hpBremoved | hpOldPlus
        · exact False.elim (hpAvoidNew (Or.inl hpBremoved))
        · have hpOld : p ∈ BplusOld := hpOldPlus.1
          have hpNotEnds : p ∉ ({x, y} : Set _) := hpOldPlus.2
          have hpSeg : p ∈ segment ℝ x y := by
            rw [← hOutCarrier, ← hBplusOld]
            exact hpOld
          rw [hSegmentDecomp] at hpSeg
          rcases hpSeg with hpNew | hpResidual
          · by_cases hpCut : p = y'
            · exact Or.inr (hpCut ▸ left_mem_segment ℝ y' y)
            · exfalso
              apply hpAvoidNew
              apply Or.inr
              refine ⟨hpNew, ?_⟩
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨by
                intro hpx
                exact hpNotEnds (by simp [hpx]), hpCut⟩
          · exact Or.inr hpResidual
    · intro hp
      rcases hp with hpOldRetained | hpResidual
      · refine ⟨hpOldRetained.1, ?_⟩
        rintro (hpBremoved | hpNewRemoved)
        · exact hpOldRetained.2 (Or.inl hpBremoved)
        · apply hpOldRetained.2
          apply Or.inr
          refine ⟨hnewSubsetOld hpNewRemoved.1, ?_⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          have hpNewEnds : p ≠ x ∧ p ≠ y' := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              using hpNewRemoved.2
          refine ⟨hpNewEnds.1, ?_⟩
          intro hpy
          exact hyNotNew (hpy ▸ hpNewRemoved.1)
      · refine ⟨hBplusOldCarrier (hresidualSubsetOld hpResidual), ?_⟩
        rintro (hpBremoved | hpNewRemoved)
        · have hpB : p ∈ B := hpBremoved.1
          have hpx : p = x := by
            have : p ∈ ({x} : Set _) := hBInterOld ▸
              ⟨hpB, hresidualSubsetOld hpResidual⟩
            simpa using this
          exact hxNotResidual (hpx ▸ hpResidual)
        · have hpAtCut : p = y' := by
            have : p ∈ ({y'} : Set _) := hAdjacent ▸
              ⟨hpNewRemoved.1, hpResidual⟩
            simpa using this
          exact hpNewRemoved.2 (by simp [hpAtCut])
  have hHDecomp : H = HOld ∪ segment ℝ y' y := by
    ext p
    constructor
    · intro hp
      rcases hp with hpEdges | hpVertex
      · rcases Set.mem_iUnion.mp hpEdges with ⟨edge, hpEdge⟩
        by_cases heFirst : edge = firstEdge
        · left
          rw [hHOld]
          left
          apply Set.mem_iUnion.mpr
          exact ⟨edge, by simpa [H, heFirst] using hpEdge⟩
        · rw [if_neg heFirst] at hpEdge
          by_cases heSecond : edge = secondEdge
          · subst edge
            rw [if_pos rfl] at hpEdge
            have hpNewSecond : p ∈
                (D.edgeArc secondEdge).carrier \
                  (Bremoved ∪ NewPlusRemoved) := by
              simpa [Bremoved, NewPlusRemoved] using hpEdge
            rw [hSecondRetained] at hpNewSecond
            rcases hpNewSecond with hpOldSecond | hpResidual
            · left
              rw [hHOld]
              left
              apply Set.mem_iUnion.mpr
              refine ⟨secondEdge, ?_⟩
              rw [if_neg hedges.symm, if_pos rfl]
              simpa [Bremoved, OldPlusRemoved] using hpOldSecond
            · exact Or.inr hpResidual
          · left
            rw [hHOld]
            left
            apply Set.mem_iUnion.mpr
            refine ⟨edge, ?_⟩
            rw [if_neg heFirst, if_neg heSecond]
            simpa [H, heFirst, heSecond] using hpEdge
      · left
        rw [hHOld]
        exact Or.inr hpVertex
    · intro hp
      rcases hp with hpOld | hpResidual
      · rw [hHOld] at hpOld
        rcases hpOld with hpEdges | hpVertex
        · rcases Set.mem_iUnion.mp hpEdges with ⟨edge, hpEdge⟩
          left
          apply Set.mem_iUnion.mpr
          by_cases heFirst : edge = firstEdge
          · exact ⟨edge, by simpa [H, heFirst] using hpEdge⟩
          · rw [if_neg heFirst] at hpEdge
            by_cases heSecond : edge = secondEdge
            · subst edge
              rw [if_pos rfl] at hpEdge
              have hpOldSecond : p ∈
                  (D.edgeArc secondEdge).carrier \
                    (Bremoved ∪ OldPlusRemoved) := by
                simpa [Bremoved, OldPlusRemoved] using hpEdge
              have hpNewSecond : p ∈
                  (D.edgeArc secondEdge).carrier \
                    (Bremoved ∪ NewPlusRemoved) := by
                rw [hSecondRetained]
                exact Or.inl hpOldSecond
              refine ⟨secondEdge, ?_⟩
              rw [if_neg hedges.symm, if_pos rfl]
              simpa [Bremoved, NewPlusRemoved] using hpNewSecond
            · refine ⟨edge, ?_⟩
              rw [if_neg heFirst, if_neg heSecond]
              simpa [H, heFirst, heSecond] using hpEdge
        · exact Or.inr hpVertex
      · left
        apply Set.mem_iUnion.mpr
        refine ⟨secondEdge, ?_⟩
        rw [if_neg hedges.symm, if_pos rfl]
        have hpNewSecond : p ∈
            (D.edgeArc secondEdge).carrier \
              (Bremoved ∪ NewPlusRemoved) := by
          rw [hSecondRetained]
          exact Or.inr hpResidual
        simpa [Bremoved, NewPlusRemoved] using hpNewSecond
  have hTailOldCarrierSubset :
      TailArc.carrier ⊆ (D.edgeArc secondEdge).carrier := by
    intro p hp
    rw [hTailCarrier] at hp
    rcases hp with hpResidual | hpOldTail
    · exact hBplusOldCarrier (hresidualSubsetOld hpResidual)
    · exact TailOld.carrier_subset_old_beta hpOldTail
  have hTailH : TailArc.carrier ⊆ H := by
    intro p hp
    rw [hHDecomp]
    rw [hTailCarrier] at hp
    rcases hp with hpResidual | hpOldTail
    · exact Or.inr hpResidual
    · exact Or.inl (TailOld.carrier_subset_H hpOldTail)
  let Tail : BigonRerouteOrderedBetaTailData
      G D secondEdge u y' B Bplus Rbeta H :=
    { tailArc := TailArc
      farEndpoint := TailOld.farEndpoint
      u_mem_beta := TailOld.u_mem_beta
      farEndpoint_mem_beta := TailOld.farEndpoint_mem_beta
      farEndpoint_ne_u := TailOld.farEndpoint_ne_u
      source_eq := hTailSource
      target_eq := hTailTarget
      carrier_eq := hTailCarrierRbeta
      carrier_subset_old_beta := hTailOldCarrierSubset
      relativeInterior_subset_old_beta := hTailRelative
      meets_removed_subarc := hTailRemoved
      carrier_subset_H := hTailH
      old_orientation_compatible := by
        constructor
        · intro hs
          rw [hTailTarget, ← TailOld.target_eq]
          exact TailOld.old_orientation_compatible.1 hs
        · intro ht
          rw [hTailTarget, ← TailOld.target_eq]
          exact TailOld.old_orientation_compatible.2 ht }
  have hBplusCross : forall p, p ∈ Bplus ->
      p ∈ D.crossingSet -> p = x := by
    intro p hp hpCross
    exact hBplusOldCross p (hnewSubsetOld hp) hpCross
  have hBplusVertex : forall v : V,
      D.vertexPlacement v ∈ Bplus -> False := by
    intro v hp
    exact hBplusOldVertex v (hnewSubsetOld hp)
  have hAResidual : Disjoint A (segment ℝ y' y) := by
    apply hATail.mono_right
    intro p hp
    rw [hTailCarrier]
    exact Or.inl hp
  have hBResidual : Disjoint B (segment ℝ y' y) := by
    rw [Set.disjoint_left]
    intro p hpB hpResidual
    have hpx : p = x := by
      have : p ∈ ({x} : Set _) := hBInterOld ▸
        ⟨hpB, hresidualSubsetOld hpResidual⟩
      simpa using this
    exact hxNotResidual (hpx ▸ hpResidual)
  have hXASpec : forall p, p ∈ XA ↔
      p ∈ A \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H := by
    intro p
    rw [hXASpecOld p]
    constructor
    · rintro ⟨hpA, hpOld⟩
      refine ⟨hpA, ?_⟩
      rw [hHDecomp]
      exact Or.inl hpOld
    · rintro ⟨hpA, hpH⟩
      refine ⟨hpA, ?_⟩
      rw [hHDecomp] at hpH
      rcases hpH with hpOld | hpResidual
      · exact hpOld
      · exact False.elim
          ((Set.disjoint_left.mp hAResidual hpA.1) hpResidual)
  have hXBSpec : forall p, p ∈ XB ↔
      p ∈ B \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H := by
    intro p
    rw [hXBSpecOld p]
    constructor
    · rintro ⟨hpB, hpOld⟩
      refine ⟨hpB, ?_⟩
      rw [hHDecomp]
      exact Or.inl hpOld
    · rintro ⟨hpB, hpH⟩
      refine ⟨hpB, ?_⟩
      rw [hHDecomp] at hpH
      rcases hpH with hpOld | hpResidual
      · exact hpOld
      · exact False.elim
          ((Set.disjoint_left.mp hBResidual hpB.1) hpResidual)
  refine ⟨firstEdge, secondEdge, hpair, firstArc, secondArc,
    hfirstCarrier, hfirstRelative, hfirstSource,
    hsecondCarrier, hsecondRelative, hsecondSource,
    x, y, y', FirstCut, SecondCut, OutCut,
    hxCross, hxFirst, hxSecond, hySecond, hyx,
    hOutCarrier, hFirstSecond, hSecondOut, hFirstTail,
    A, B, BplusOld, RbetaOld, HOld,
    hA, hB, hBplusOld, hRbetaOld, hHOld,
    TailOld, hBplusOldCross, hBplusOldVertex,
    XA, XB, hXASpecOld, hXBSpecOld, hcard,
    hxCross, Disk, hDiskOwners, i, j, hi, hj, hxi, hxj, htrans,
    hy'open, hsegmentBall, Bplus, Rbeta, H, rfl, rfl,
    hRbetaExact, rfl, Tail, ?_, hATail, hBplusCross, hBplusVertex,
    hXASpec, hXBSpec, hcard, ?_⟩
  · simpa [Tail] using hTailCarrier
  · exact hFirstPrefixTransfer
