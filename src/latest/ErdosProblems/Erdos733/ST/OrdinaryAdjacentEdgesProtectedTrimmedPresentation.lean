import ErdosProblems.Erdos733.ST.BigonRerouteFinitePresentationLocalBranch
import ErdosProblems.Erdos733.ST.BigonRerouteOrderedBetaTailData
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact
import ErdosProblems.Erdos733.ST.PolygonalArcOpenSegmentSubsetRelativeInterior
import ErdosProblems.Erdos733.ST.PolygonalArcPointCutData
import Mathlib.Tactic

open Classical
noncomputable section

private lemma polygonalArc_source_mem_carrier (Q : PolygonalArc) :
    Q.source ∈ Q.carrier := by
  rw [Q.carrier_eq]
  have hseg : 0 + 1 < Q.vertices.length := Q.length_ge_two
  refine ⟨0, hseg, ?_⟩
  have h0 : 0 < Q.vertices.length := by omega
  have hsource : Q.vertices[0]'h0 = Q.source := by
    have hhead := Q.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem h0] at hhead
    exact Option.some.inj hhead
  rw [← hsource]
  exact left_mem_segment ℝ _ _

private lemma polygonalArc_target_mem_carrier (Q : PolygonalArc) :
    Q.target ∈ Q.carrier := by
  rw [Q.carrier_eq]
  let k := Q.vertices.length - 2
  have hk : k + 1 < Q.vertices.length := by
    dsimp [k]
    have hlen := Q.length_ge_two
    omega
  refine ⟨k, hk, ?_⟩
  have hlast : Q.vertices.length - 1 < Q.vertices.length := by omega
  have htarget : Q.vertices[Q.vertices.length - 1]'hlast = Q.target := by
    have hlast' := Q.target_eq_last
    rw [List.getLast?_eq_getElem?] at hlast'
    rw [List.getElem?_eq_getElem hlast] at hlast'
    exact Option.some.inj hlast'
  have hkLast : k + 1 = Q.vertices.length - 1 := by
    dsimp [k]
    omega
  rw [← htarget]
  simpa [hkLast] using
    (right_mem_segment ℝ Q.vertices[k] Q.vertices[k + 1])

private lemma polygonalArc_vertex_mem_carrier (Q : PolygonalArc)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ Q.vertices) :
    p ∈ Q.carrier := by
  rw [Q.carrier_eq]
  rcases List.getElem_of_mem hp with ⟨k, hk, rfl⟩
  have hlen := Q.length_ge_two
  by_cases hnext : k + 1 < Q.vertices.length
  · exact ⟨k, hnext, left_mem_segment ℝ _ _⟩
  · have hkpos : 0 < k := by
      by_contra h
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos h
      subst k
      exact hnext (by omega)
    refine ⟨k - 1, by omega, ?_⟩
    simpa [Nat.sub_add_cancel hkpos] using
      (right_mem_segment ℝ Q.vertices[k - 1] Q.vertices[(k - 1) + 1])

private lemma polygonalArc_open_not_vertices (Q : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
    (hk : k + 1 < Q.vertices.length)
    (hp : p ∈ openSegment ℝ Q.vertices[k] Q.vertices[k + 1]) :
    p ∉ Q.vertices := by
  intro hpv
  rcases List.getElem_of_mem hpv with ⟨m, hm, hmp⟩
  by_cases hmk : m = k
  · subst m
    have hne : Q.vertices[k] ≠ Q.vertices[k + 1] := by
      intro heq
      have := (Q.simple_vertices.getElem_inj_iff
        (i := k) (j := k + 1) (hi := by omega) (hj := hk)).1 heq
      omega
    exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (hmp ▸ hp))
  · by_cases hmks : m = k + 1
    · subst m
      have hne : Q.vertices[k] ≠ Q.vertices[k + 1] := by
        intro heq
        have := (Q.simple_vertices.getElem_inj_iff
          (i := k) (j := k + 1) (hi := by omega) (hj := hk)).1 heq
        omega
      exact hne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 (hmp ▸ hp))
    · exact Q.vertices_avoid_nonincident_interiors hk hm hmk hmks (hmp ▸ hp)

private lemma ordinary_old_relative_of_carrier
    {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (p : EuclideanSpace ℝ (Fin 2))
    (hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v)
    (e : G.edgeFinset) (hp : p ∈ (D.edgeArc e).carrier) :
    p ∈ (D.edgeArc e).relativeInterior := by
  rw [(D.edgeArc e).relativeInterior_eq]
  refine ⟨hp, ?_⟩
  rcases D.edgeArc_endpoints e with ⟨a, b, _hab, _he, hends⟩
  rcases hends with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] <;>
    constructor
  · intro hpSource
    exact hpNotVertex a (hpSource.trans hs)
  · intro hpTarget
    exact hpNotVertex b (hpTarget.trans ht)
  · intro hpSource
    exact hpNotVertex b (hpSource.trans hs)
  · intro hpTarget
    exact hpNotVertex a (hpTarget.trans ht)

private lemma polygonalArc_same_piece_intersection_vertex
    (Q : PolygonalArc)
    (s t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
    (hs : s ∈ (Finset.univ : Finset (Fin (Q.vertices.length - 1))).image
      (fun k => (Q.vertices[k.1]'(by omega), Q.vertices[k.1 + 1]'(by omega))))
    (ht : t ∈ (Finset.univ : Finset (Fin (Q.vertices.length - 1))).image
      (fun k => (Q.vertices[k.1]'(by omega), Q.vertices[k.1 + 1]'(by omega))))
    (hst : s ≠ t) (p : EuclideanSpace ℝ (Fin 2))
    (hps : p ∈ segment ℝ s.1 s.2)
    (hpt : p ∈ segment ℝ t.1 t.2) : p ∈ Q.vertices := by
  rcases Finset.mem_image.mp hs with ⟨i, _hiMem, hsi⟩
  rcases Finset.mem_image.mp ht with ⟨j, _hjMem, htj⟩
  subst s
  subst t
  have hi : i.1 + 1 < Q.vertices.length := by omega
  have hj : j.1 + 1 < Q.vertices.length := by omega
  rcases Nat.lt_trichotomy i.1 j.1 with hij | hijeq | hji
  · have hpInter : p ∈
        segment ℝ Q.vertices[i.1] Q.vertices[i.1 + 1] ∩
          segment ℝ Q.vertices[j.1] Q.vertices[j.1 + 1] := ⟨hps, hpt⟩
    rw [Q.segment_intersections hi hj hij] at hpInter
    by_cases hadj : j.1 = i.1 + 1
    · have hpeq : p = Q.vertices[j.1] := by
        simpa [hadj] using hpInter
      simp [hpeq]
    · simpa [hadj] using hpInter
  · have hijFin : i = j := Fin.ext hijeq
    subst j
    exact (hst rfl).elim
  · have hpInter : p ∈
        segment ℝ Q.vertices[j.1] Q.vertices[j.1 + 1] ∩
          segment ℝ Q.vertices[i.1] Q.vertices[i.1 + 1] := ⟨hpt, hps⟩
    rw [Q.segment_intersections hj hi hji] at hpInter
    by_cases hadj : i.1 = j.1 + 1
    · have hpeq : p = Q.vertices[i.1] := by
        simpa [hadj] using hpInter
      simp [hpeq]
    · simpa [hadj] using hpInter


-- [TABLET NODE: OrdinaryAdjacentEdgesProtectedTrimmedPresentation]
lemma OrdinaryAdjacentEdgesProtectedTrimmedPresentation
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (u : V) (firstEdge secondEdge : G.edgeFinset)
    (firstArc : PolygonalArc) (x y' : EuclideanSpace ℝ (Fin 2))
    (FirstCut : PolygonalArcPointCutData firstArc x)
    (A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (Tail : BigonRerouteOrderedBetaTailData
      G D secondEdge u y' B Bplus Rbeta H)
    (retainedArc : G.edgeFinset → PolygonalArc)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (hclean : forall (e f : G.edgeFinset)
      (p : EuclideanSpace ℝ (Fin 2)),
      e ≠ f ->
        p ∈ (D.edgeArc e).relativeInterior ->
          p ∈ (D.edgeArc f).relativeInterior ->
            exists i j : ℕ,
              exists (hi : i + 1 < (D.edgeArc e).vertices.length)
                (hj : j + 1 < (D.edgeArc f).vertices.length),
                p ∈ openSegment ℝ (D.edgeArc e).vertices[i]
                    (D.edgeArc e).vertices[i + 1] ∧
                  p ∈ openSegment ℝ (D.edgeArc f).vertices[j]
                    (D.edgeArc f).vertices[j + 1] ∧
                    ¬ exists c : ℝ,
                      (D.edgeArc f).vertices[j + 1] -
                          (D.edgeArc f).vertices[j] =
                        c • ((D.edgeArc e).vertices[i + 1] -
                          (D.edgeArc e).vertices[i]))
    (hedges : firstEdge ≠ secondEdge)
    (hfirstCarrier : firstArc.carrier = (D.edgeArc firstEdge).carrier)
    (hfirstRelative : firstArc.relativeInterior =
      (D.edgeArc firstEdge).relativeInterior)
    (hfirstSource : firstArc.source = D.vertexPlacement u)
    (hxFirst : x ∈ (D.edgeArc firstEdge).relativeInterior)
    (hA : A = FirstCut.prefixArc.carrier)
    (hRbeta : Rbeta =
      (D.edgeArc secondEdge).carrier \ ((B ∪ Bplus) \ ({y'} : Set _)))
    (hH : H =
      (⋃ edge : G.edgeFinset,
        if edge = firstEdge then
          (D.edgeArc edge).carrier \
            (A \ ({D.vertexPlacement u, x} : Set _))
        else if edge = secondEdge then
          (D.edgeArc edge).carrier \
            ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
              (Bplus \ ({x, y'} : Set _)))
        else (D.edgeArc edge).carrier) ∪
      {p | exists v : V, v ≠ u ∧ p = D.vertexPlacement v})
    (hATail : Disjoint A Tail.tailArc.carrier)
    (hretained : retainedArc = fun e =>
      if e = firstEdge then FirstCut.suffixArc
      else if e = secondEdge then Tail.tailArc
      else D.edgeArc e)
    (hXASpec : forall p, p ∈ XA ↔
      p ∈ A \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H)
    (hFirstPrefixTransfer : forall p i
        (hi : i + 1 < (D.edgeArc firstEdge).vertices.length),
      p ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] ->
      p ∈ FirstCut.prefixArc.carrier ->
      p ≠ x ->
      exists j : ℕ,
        exists hj : j + 1 < FirstCut.prefixArc.vertices.length,
          p ∈ openSegment ℝ FirstCut.prefixArc.vertices[j]
              FirstCut.prefixArc.vertices[j + 1] ∧
          exists scale : ℝ, scale ≠ 0 ∧
            FirstCut.prefixArc.vertices[j + 1] -
                FirstCut.prefixArc.vertices[j] =
              scale • ((D.edgeArc firstEdge).vertices[i + 1] -
                (D.edgeArc firstEdge).vertices[i])) :
    exists Kclean : FinitePolygonalSet,
                            Kclean.carrier = H ∧
                            (forall s :
                                EuclideanSpace ℝ (Fin 2) ×
                                  EuclideanSpace ℝ (Fin 2),
                              s ∈ Kclean.segments ↔
                                exists e : G.edgeFinset,
                                  exists i : ℕ,
                                    exists hi : i + 1 <
                                        (retainedArc e).vertices.length,
                                      s = ((retainedArc e).vertices[i],
                                        (retainedArc e).vertices[i + 1])) ∧
                            (forall q : EuclideanSpace ℝ (Fin 2),
                              q ∈ Kclean.points ↔
                                (exists e : G.edgeFinset,
                                  q ∈ (retainedArc e).vertices) ∨
                                (exists v : V, q = D.vertexPlacement v) ∨
                                q = x ∨
                                (q ∈ D.crossingSet ∧
                                  exists s, s ∈ Kclean.segments ∧
                                    exists t, t ∈ Kclean.segments ∧
                                      s ≠ t ∧
                                      q ∈ segment ℝ s.1 s.2 ∧
                                      q ∈ segment ℝ t.1 t.2)) ∧
                            (forall v : V, v ≠ u ->
                              D.vertexPlacement v ∈
                                (Kclean.points : Set _)) ∧
                            forall p, p ∈ XA ->
                              p ∉ (Kclean.points : Set _) ∧
                              exists j : ℕ,
                                exists hj : j + 1 <
                                    FirstCut.prefixArc.vertices.length,
                                  p ∈ openSegment ℝ
                                      FirstCut.prefixArc.vertices[j]
                                      FirstCut.prefixArc.vertices[j + 1] ∧
                                  exists s :
                                      EuclideanSpace ℝ (Fin 2) ×
                                        EuclideanSpace ℝ (Fin 2),
                                    s ∈ Kclean.segments ∧
                                    p ∈ openSegment ℝ s.1 s.2 ∧
                                    (¬ exists c : ℝ, s.2 - s.1 =
                                      c •
                                        (FirstCut.prefixArc.vertices[j + 1] -
                                          FirstCut.prefixArc.vertices[j])) ∧
                                    (forall t :
                                        EuclideanSpace ℝ (Fin 2) ×
                                          EuclideanSpace ℝ (Fin 2),
                                      t ∈ Kclean.segments ->
                                        p ∈ openSegment ℝ t.1 t.2 -> t = s) ∧
                                    forall upper : ℝ, 0 < upper ->
                                      exists r : ℝ, 0 < r ∧ r < upper ∧
                                        Metric.ball p r ∩ H =
                                          Metric.ball p r ∩ segment ℝ s.1 s.2 ∧
                                        Metric.ball p r ∩ Rbeta = ∅ := by
-- BODY
  classical
  let arcSegments : PolygonalArc →
      Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    fun Q =>
      (Finset.univ : Finset (Fin (Q.vertices.length - 1))).image
        (fun k =>
          (Q.vertices[k.1]'(by omega), Q.vertices[k.1 + 1]'(by omega)))
  let segs : Finset
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset G.edgeFinset).biUnion
      (fun e => arcSegments (retainedArc e))
  let arcPts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset G.edgeFinset).biUnion
      (fun e => (retainedArc e).vertices.toFinset)
  let vertexPts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset V).image D.vertexPlacement
  let retainedCrossings : Finset (EuclideanSpace ℝ (Fin 2)) :=
    D.crossingSet.filter (fun p =>
      ∃ s ∈ segs, ∃ t ∈ segs, s ≠ t ∧
        p ∈ segment ℝ s.1 s.2 ∧ p ∈ segment ℝ t.1 t.2)
  let pts : Finset (EuclideanSpace ℝ (Fin 2)) :=
    arcPts ∪ vertexPts ∪ {x} ∪ retainedCrossings
  have arc_source_mem_carrier (Q : PolygonalArc) : Q.source ∈ Q.carrier := by
    exact polygonalArc_source_mem_carrier Q
  have arc_target_mem_carrier (Q : PolygonalArc) : Q.target ∈ Q.carrier := by
    exact polygonalArc_target_mem_carrier Q
  have arc_vertex_mem_carrier (Q : PolygonalArc)
      {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ Q.vertices) :
      p ∈ Q.carrier := by
    exact polygonalArc_vertex_mem_carrier Q hp
  have arc_segment_mem_carrier (Q : PolygonalArc)
      {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
      (hs : s ∈ arcSegments Q) : segment ℝ s.1 s.2 ⊆ Q.carrier := by
    intro p hp
    dsimp [arcSegments] at hs
    rcases Finset.mem_image.mp hs with ⟨k, _hk, rfl⟩
    rw [Q.carrier_eq]
    exact ⟨k.1, by omega, hp⟩
  have segment_owner {s :
      EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
      (hs : s ∈ segs) :
      ∃ e : G.edgeFinset, s ∈ arcSegments (retainedArc e) := by
    dsimp [segs] at hs
    rcases Finset.mem_biUnion.mp hs with ⟨e, _he, hs⟩
    exact ⟨e, hs⟩
  have segment_mem_segs {e : G.edgeFinset}
      {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
      (hs : s ∈ arcSegments (retainedArc e)) : s ∈ segs := by
    dsimp [segs]
    exact Finset.mem_biUnion.mpr ⟨e, by simp, hs⟩
  have arc_point_mem_pts {e : G.edgeFinset}
      {p : EuclideanSpace ℝ (Fin 2)}
      (hp : p ∈ (retainedArc e).vertices) : p ∈ pts := by
    dsimp [pts, arcPts]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl
      (Finset.mem_biUnion.mpr ⟨e, by simp, by simpa using hp⟩)))
  have vertex_mem_pts (v : V) : D.vertexPlacement v ∈ pts := by
    dsimp [pts, vertexPts]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr
      (Finset.mem_image.mpr ⟨v, by simp, rfl⟩)))
  have x_mem_pts : x ∈ pts := by
    simp [pts]
  have retained_crossing_mem_pts {p : EuclideanSpace ℝ (Fin 2)}
      (hp : p ∈ retainedCrossings) : p ∈ pts := by
    simp [pts, hp]
  have first_special_subset :
      FirstCut.suffixArc.carrier ⊆ H := by
    intro p hpSuffix
    rw [hH]
    left
    apply Set.mem_iUnion.mpr
    refine ⟨firstEdge, ?_⟩
    rw [if_pos rfl]
    refine ⟨?_, ?_⟩
    · have hpFirst : p ∈ firstArc.carrier :=
        FirstCut.suffix_carrier_subset hpSuffix
      simpa [hfirstCarrier] using hpFirst
    · rintro ⟨hpA, hpNotEnds⟩
      have hpBoth : p ∈ FirstCut.prefixArc.carrier ∩
          FirstCut.suffixArc.carrier := ⟨hA ▸ hpA, hpSuffix⟩
      have hpx : p = x := by
        have : p ∈ ({x} : Set _) := FirstCut.carrier_intersection ▸ hpBoth
        simpa using this
      exact hpNotEnds (by simp [hpx])
  have piece_subset_H (e : G.edgeFinset) :
      (retainedArc e).carrier ⊆ H := by
    by_cases heFirst : e = firstEdge
    · subst e
      simpa [hretained] using first_special_subset
    · by_cases heSecond : e = secondEdge
      · subst e
        simpa [hretained, hedges.symm] using Tail.carrier_subset_H
      · intro p hp
        rw [hH]
        left
        apply Set.mem_iUnion.mpr
        refine ⟨e, ?_⟩
        simpa [hretained, heFirst, heSecond] using hp
  have H_subset_pieces : H ⊆
      (vertexPts : Set (EuclideanSpace ℝ (Fin 2))) ∪ ({x} : Set _) ∪
        ⋃ e : G.edgeFinset, (retainedArc e).carrier := by
    intro p hpH
    rw [hH] at hpH
    rcases hpH with hpEdges | hpVertex
    · rcases Set.mem_iUnion.mp hpEdges with ⟨e, hpRetained⟩
      by_cases heFirst : e = firstEdge
      · subst e
        rw [if_pos rfl] at hpRetained
        have hpFirstArc : p ∈ firstArc.carrier := by
          simpa [hfirstCarrier] using hpRetained.1
        rw [FirstCut.carrier_decomposition] at hpFirstArc
        rcases hpFirstArc with hpPrefix | hpSuffix
        · by_cases hpDu : p = D.vertexPlacement u
          · left
            simpa [vertexPts, hpDu]
          · by_cases hpx : p = x
            · exact Or.inl (Or.inr (by simpa [hpx]))
            · exfalso
              exact hpRetained.2 ⟨hA ▸ hpPrefix, by simp [hpDu, hpx]⟩
        · exact Or.inr
            (Set.mem_iUnion.mpr ⟨firstEdge, by simpa [hretained] using hpSuffix⟩)
      · rw [if_neg heFirst] at hpRetained
        by_cases heSecond : e = secondEdge
        · subst e
          rw [if_pos rfl] at hpRetained
          by_cases hpTail : p ∈ Rbeta
          · exact Or.inr (Set.mem_iUnion.mpr
              ⟨secondEdge, by simpa [hretained, hedges.symm, Tail.carrier_eq]
                using hpTail⟩)
          · have hpRemoved : p ∈ (B ∪ Bplus) \ ({y'} : Set _) := by
              by_contra hnot
              apply hpTail
              rw [hRbeta]
              exact ⟨hpRetained.1, hnot⟩
            rcases hpRemoved.1 with hpB | hpBplus
            · have hpEnds : p ∈ ({D.vertexPlacement u, x} : Set _) := by
                by_contra hnot
                exact hpRetained.2 (Or.inl ⟨hpB, hnot⟩)
              rcases hpEnds with hpDu | hpx
              · left
                simpa [vertexPts, hpDu]
              · exact Or.inl (Or.inr (by simpa [hpx]))
            · have hpEnds : p ∈ ({x, y'} : Set _) := by
                by_contra hnot
                exact hpRetained.2 (Or.inr ⟨hpBplus, hnot⟩)
              rcases hpEnds with hpx | hpy'
              · exact Or.inl (Or.inr (by simpa [hpx]))
              · exfalso
                apply hpTail
                rw [hRbeta]
                refine ⟨hpRetained.1, ?_⟩
                rintro ⟨_hp, hpNe⟩
                exact hpNe (by simpa [hpy'])
        · exact Or.inr (Set.mem_iUnion.mpr
            ⟨e, by simpa [hretained, heFirst, heSecond] using hpRetained⟩)
    · rcases hpVertex with ⟨v, _hv, rfl⟩
      left
      simp [vertexPts]
  have points_subset_H :
      (pts : Set (EuclideanSpace ℝ (Fin 2))) ⊆ H := by
    intro p hp
    simp only [pts, Finset.coe_union, Finset.coe_singleton,
      Set.mem_union, Set.mem_singleton_iff] at hp
    rcases hp with ((hpArc | hpVertex) | hpx) | hpCross
    · dsimp [arcPts] at hpArc
      rcases Finset.mem_biUnion.mp hpArc with ⟨e, _he, hpVertices⟩
      apply piece_subset_H e
      apply arc_vertex_mem_carrier
      simpa using hpVertices
    · dsimp [vertexPts] at hpVertex
      rcases Finset.mem_image.mp hpVertex with ⟨v, _hv, rfl⟩
      by_cases hvu : v = u
      · subst v
        rw [hH]
        left
        apply Set.mem_iUnion.mpr
        refine ⟨firstEdge, ?_⟩
        rw [if_pos rfl]
        refine ⟨?_, ?_⟩
        · have hs := arc_source_mem_carrier firstArc
          simpa [hfirstCarrier, hfirstSource] using hs
        · intro hpRemoved
          exact hpRemoved.2 (by simp)
      · rw [hH]
        exact Or.inr ⟨v, hvu, rfl⟩
    · subst p
      rw [hH]
      left
      apply Set.mem_iUnion.mpr
      refine ⟨firstEdge, ?_⟩
      rw [if_pos rfl]
      refine ⟨?_, ?_⟩
      · rw [(D.edgeArc firstEdge).relativeInterior_eq] at hxFirst
        exact hxFirst.1
      · intro hpRemoved
        exact hpRemoved.2 (by simp)
    · have hpFilter := Finset.mem_filter.mp hpCross
      rcases hpFilter.2 with ⟨s, hs, t, _ht, _hst, hps, _hpt⟩
      rcases segment_owner hs with ⟨e, hsArc⟩
      exact piece_subset_H e (arc_segment_mem_carrier _ hsArc hps)
  have second_special_cases
      {p : EuclideanSpace ℝ (Fin 2)}
      (hp : p ∈ (D.edgeArc secondEdge).carrier \
        ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
          (Bplus \ ({x, y'} : Set _)))) :
      p ∈ Tail.tailArc.carrier ∨
        p = D.vertexPlacement u ∨ p = x := by
    by_cases hpTail : p ∈ Rbeta
    · exact Or.inl (by simpa [Tail.carrier_eq] using hpTail)
    · have hpRemoved : p ∈ (B ∪ Bplus) \ ({y'} : Set _) := by
        by_contra hnot
        apply hpTail
        rw [hRbeta]
        exact ⟨hp.1, hnot⟩
      rcases hpRemoved.1 with hpB | hpBplus
      · have hpEnds : p ∈ ({D.vertexPlacement u, x} : Set _) := by
          by_contra hnot
          exact hp.2 (Or.inl ⟨hpB, hnot⟩)
        rcases hpEnds with hpDu | hpx
        · exact Or.inr (Or.inl hpDu)
        · exact Or.inr (Or.inr hpx)
      · have hpEnds : p ∈ ({x, y'} : Set _) := by
          by_contra hnot
          exact hp.2 (Or.inr ⟨hpBplus, hnot⟩)
        rcases hpEnds with hpx | hpy'
        · exact Or.inr (Or.inr hpx)
        · exfalso
          apply hpTail
          rw [hRbeta]
          refine ⟨hp.1, ?_⟩
          rintro ⟨_hp, hpNe⟩
          exact hpNe (by simpa [hpy'])
  have old_relative_of_carrier
      (p : EuclideanSpace ℝ (Fin 2))
      (hpNotVertex : forall v : V, p ≠ D.vertexPlacement v)
      (e : G.edgeFinset) (hp : p ∈ (D.edgeArc e).carrier) :
      p ∈ (D.edgeArc e).relativeInterior := by
    exact ordinary_old_relative_of_carrier G D p hpNotVertex e hp
  have open_not_vertices (Q : PolygonalArc)
      (p : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
      (hk : k + 1 < Q.vertices.length)
      (hp : p ∈ openSegment ℝ Q.vertices[k] Q.vertices[k + 1]) :
      p ∉ Q.vertices := by
    exact polygonalArc_open_not_vertices Q p k hk hp
  have open_index_unique (Q : PolygonalArc) :
      forall z a b (ha : a + 1 < Q.vertices.length)
        (hb : b + 1 < Q.vertices.length),
        z ∈ openSegment ℝ Q.vertices[a] Q.vertices[a + 1] ->
        z ∈ openSegment ℝ Q.vertices[b] Q.vertices[b + 1] -> a = b := by
    intro z a b ha hb hza hzb
    rcases lt_trichotomy a b with hab' | rfl | hba
    · have hzInter : z ∈ segment ℝ Q.vertices[a] Q.vertices[a + 1] ∩
          segment ℝ Q.vertices[b] Q.vertices[b + 1] :=
        ⟨openSegment_subset_segment ℝ _ _ hza,
          openSegment_subset_segment ℝ _ _ hzb⟩
      rw [Q.segment_intersections ha hb hab'] at hzInter
      by_cases hadj : b = a + 1
      · have hzbLeft : z ≠ Q.vertices[b] := by
          intro h
          have hne : Q.vertices[b] ≠ Q.vertices[b + 1] := by
            intro heq
            have := (Q.simple_vertices.getElem_inj_iff
              (i := b) (j := b + 1) (hi := by omega) (hj := hb)).1 heq
            omega
          exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (h ▸ hzb))
        exact False.elim (hzbLeft (by simpa [hadj] using hzInter))
      · simpa [hadj] using hzInter
    · rfl
    · have hzInter : z ∈ segment ℝ Q.vertices[b] Q.vertices[b + 1] ∩
          segment ℝ Q.vertices[a] Q.vertices[a + 1] :=
        ⟨openSegment_subset_segment ℝ _ _ hzb,
          openSegment_subset_segment ℝ _ _ hza⟩
      rw [Q.segment_intersections hb ha hba] at hzInter
      by_cases hadj : a = b + 1
      · have hzaLeft : z ≠ Q.vertices[a] := by
          intro h
          have hne : Q.vertices[a] ≠ Q.vertices[a + 1] := by
            intro heq
            have := (Q.simple_vertices.getElem_inj_iff
              (i := a) (j := a + 1) (hi := by omega) (hj := ha)).1 heq
            omega
          exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (h ▸ hza))
        exact False.elim (hzaLeft (by simpa [hadj] using hzInter))
      · simpa [hadj] using hzInter
  have same_piece_intersection_arc_point
      (e : G.edgeFinset)
      (s t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
      (hs : s ∈ arcSegments (retainedArc e))
      (ht : t ∈ arcSegments (retainedArc e))
      (hst : s ≠ t) (p : EuclideanSpace ℝ (Fin 2))
      (hps : p ∈ segment ℝ s.1 s.2)
      (hpt : p ∈ segment ℝ t.1 t.2) : p ∈ arcPts := by
    have hpv : p ∈ (retainedArc e).vertices := by
      apply polygonalArc_same_piece_intersection_vertex
        (Q := retainedArc e) (s := s) (t := t) (p := p)
      · simpa [arcSegments] using hs
      · simpa [arcSegments] using ht
      · exact hst
      · exact hps
      · exact hpt
    dsimp [arcPts]
    exact Finset.mem_biUnion.mpr ⟨e, by simp, by simpa using hpv⟩
  have segment_nondegenerate :
      ∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        s ∈ segs -> s.1 ≠ s.2 := by
    intro s hs
    rcases segment_owner hs with ⟨e, hsArc⟩
    dsimp [arcSegments] at hsArc
    rcases Finset.mem_image.mp hsArc with ⟨k, _hk, rfl⟩
    intro heq
    have hidx := ((retainedArc e).simple_vertices.getElem_inj_iff
      (i := k.1) (j := k.1 + 1) (hi := by omega) (hj := by omega)).1 heq
    omega
  have segment_endpoints_listed :
      ∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        s ∈ segs -> s.1 ∈ pts ∧ s.2 ∈ pts := by
    intro s hs
    rcases segment_owner hs with ⟨e, hsArc⟩
    dsimp [arcSegments] at hsArc
    rcases Finset.mem_image.mp hsArc with ⟨k, _hk, rfl⟩
    constructor <;> apply arc_point_mem_pts (e := e) <;> simp
  have hxu : x ≠ D.vertexPlacement u := by
    intro h
    exact D.no_vertex_in_edge_interior u firstEdge (h ▸ hxFirst)
  have piece_open_old_relative (e : G.edgeFinset)
      (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
      (hs : s ∈ arcSegments (retainedArc e))
      (p : EuclideanSpace ℝ (Fin 2))
      (hpNotVertex : forall v : V, p ≠ D.vertexPlacement v)
      (hp : p ∈ openSegment ℝ s.1 s.2) :
      p ∈ (D.edgeArc e).relativeInterior := by
    apply old_relative_of_carrier p hpNotVertex e
    have hpPiece : p ∈ (retainedArc e).carrier :=
      arc_segment_mem_carrier _ hs (openSegment_subset_segment ℝ _ _ hp)
    by_cases heFirst : e = firstEdge
    · subst e
      have hpFirst := FirstCut.suffix_carrier_subset
        (by simpa [hretained] using hpPiece)
      simpa [hfirstCarrier] using hpFirst
    · by_cases heSecond : e = secondEdge
      · subst e
        exact Tail.carrier_subset_old_beta
          (by simpa [hretained, hedges.symm] using hpPiece)
      · simpa [hretained, heFirst, heSecond] using hpPiece
  have segment_intersections_listed :
      ∀ s t : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        s ∈ segs -> t ∈ segs -> s ≠ t ->
          ∀ p : EuclideanSpace ℝ (Fin 2),
            p ∈ segment ℝ s.1 s.2 ->
              p ∈ segment ℝ t.1 t.2 -> p ∈ pts := by
    intro s t hs ht hst p hps hpt
    rcases segment_owner hs with ⟨e, hsArc⟩
    rcases segment_owner ht with ⟨f, htArc⟩
    by_cases hef : e = f
    · subst f
      dsimp [arcSegments] at hsArc htArc
      rcases Finset.mem_image.mp hsArc with ⟨i, _hiMem, hsi⟩
      rcases Finset.mem_image.mp htArc with ⟨j, _hjMem, htj⟩
      subst s
      subst t
      have hi : i.1 + 1 < (retainedArc e).vertices.length := by omega
      have hj : j.1 + 1 < (retainedArc e).vertices.length := by omega
      rcases Nat.lt_trichotomy i.1 j.1 with hij | hijeq | hji
      · have hpInter : p ∈
            segment ℝ (retainedArc e).vertices[i.1]
                (retainedArc e).vertices[i.1 + 1] ∩
              segment ℝ (retainedArc e).vertices[j.1]
                (retainedArc e).vertices[j.1 + 1] := ⟨hps, hpt⟩
        rw [(retainedArc e).segment_intersections hi hj hij] at hpInter
        by_cases hadj : j.1 = i.1 + 1
        · have hpeq : p = (retainedArc e).vertices[j.1] := by
            simpa [hadj] using hpInter
          apply arc_point_mem_pts (e := e)
          simp [hpeq]
        · simpa [hadj] using hpInter
      · have hijFin : i = j := Fin.ext hijeq
        subst j
        exact (hst rfl).elim
      · have hpInter : p ∈
            segment ℝ (retainedArc e).vertices[j.1]
                (retainedArc e).vertices[j.1 + 1] ∩
              segment ℝ (retainedArc e).vertices[i.1]
                (retainedArc e).vertices[i.1 + 1] := ⟨hpt, hps⟩
        rw [(retainedArc e).segment_intersections hj hi hji] at hpInter
        by_cases hadj : i.1 = j.1 + 1
        · have hpeq : p = (retainedArc e).vertices[i.1] := by
            simpa [hadj] using hpInter
          apply arc_point_mem_pts (e := e)
          simp [hpeq]
        · simpa [hadj] using hpInter
    · have endpoint_point (g : G.edgeFinset)
          (q : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
          (hq : q ∈ arcSegments (retainedArc g)) :
          q.1 ∈ pts ∧ q.2 ∈ pts := by
        dsimp [arcSegments] at hq
        rcases Finset.mem_image.mp hq with ⟨k, _hk, rfl⟩
        constructor <;> apply arc_point_mem_pts (e := g) <;> simp
      by_cases hps1 : p = s.1
      · simpa [hps1] using (endpoint_point e s hsArc).1
      · by_cases hps2 : p = s.2
        · simpa [hps2] using (endpoint_point e s hsArc).2
        · by_cases hpt1 : p = t.1
          · simpa [hpt1] using (endpoint_point f t htArc).1
          · by_cases hpt2 : p = t.2
            · simpa [hpt2] using (endpoint_point f t htArc).2
            · by_cases hpGraph : ∃ v : V, p = D.vertexPlacement v
              · rcases hpGraph with ⟨v, hpv⟩
                simpa [hpv] using vertex_mem_pts v
              · have hpNotVertex : forall v : V,
                    p ≠ D.vertexPlacement v := by
                  intro v hpv
                  exact hpGraph ⟨v, hpv⟩
                have hpsOpen : p ∈ openSegment ℝ s.1 s.2 :=
                  mem_openSegment_of_ne_left_right
                    (Ne.symm hps1) (Ne.symm hps2) hps
                have hptOpen : p ∈ openSegment ℝ t.1 t.2 :=
                  mem_openSegment_of_ne_left_right
                    (Ne.symm hpt1) (Ne.symm hpt2) hpt
                have hpERel := piece_open_old_relative e s hsArc p
                  hpNotVertex hpsOpen
                have hpFRel := piece_open_old_relative f t htArc p
                  hpNotVertex hptOpen
                have hpCross : p ∈ D.crossingSet :=
                  (D.crossingSet_spec p).2 ⟨e, f, hef, hpERel, hpFRel⟩
                apply retained_crossing_mem_pts
                exact Finset.mem_filter.mpr
                  ⟨hpCross, s, hs, t, ht, hst, hps, hpt⟩
  let Kclean : FinitePolygonalSet :=
    { carrier := H
      points := pts
      segments := segs
      segment_nondegenerate := segment_nondegenerate
      segment_endpoints_listed := segment_endpoints_listed
      segment_intersections_listed := segment_intersections_listed
      carrier_eq := by
        ext p
        constructor
        · intro hp
          rcases H_subset_pieces hp with hpFront | hpPiece
          · rcases hpFront with hpVertex | hpx
            · left
              dsimp [pts]
              change p ∈ arcPts ∪ vertexPts ∪ {x} ∪ retainedCrossings
              simp only [Finset.mem_union]
              exact Or.inl (Or.inl (Or.inr hpVertex))
            · left
              subst p
              exact x_mem_pts
          · right
            rcases Set.mem_iUnion.mp hpPiece with ⟨e, hpPiece⟩
            rw [(retainedArc e).carrier_eq] at hpPiece
            rcases hpPiece with ⟨k, hk, hpseg⟩
            let s : EuclideanSpace ℝ (Fin 2) ×
                EuclideanSpace ℝ (Fin 2) :=
              ((retainedArc e).vertices[k],
                (retainedArc e).vertices[k + 1])
            have hsArc : s ∈ arcSegments (retainedArc e) := by
              dsimp [arcSegments]
              refine Finset.mem_image.mpr ?_
              let q : Fin ((retainedArc e).vertices.length - 1) :=
                ⟨k, by omega⟩
              exact ⟨q, by simp, by simp [q, s]⟩
            exact Set.mem_iUnion.mpr
              ⟨⟨s, segment_mem_segs hsArc⟩, by simpa [s] using hpseg⟩
        · intro hp
          rcases hp with hpPoint | hpSegment
          · exact points_subset_H hpPoint
          · rcases Set.mem_iUnion.mp hpSegment with ⟨s, hps⟩
            rcases segment_owner s.2 with ⟨e, hsArc⟩
            exact piece_subset_H e (arc_segment_mem_carrier _ hsArc hps) }
  have hKcarrier : Kclean.carrier = H := rfl
  have hsegmentsSpec : forall s :
      EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      s ∈ Kclean.segments ↔
        exists e : G.edgeFinset,
          exists i : ℕ,
            exists hi : i + 1 < (retainedArc e).vertices.length,
              s = ((retainedArc e).vertices[i],
                (retainedArc e).vertices[i + 1]) := by
    intro s
    constructor
    · intro hs
      change s ∈ segs at hs
      rcases segment_owner hs with ⟨e, hsArc⟩
      dsimp [arcSegments] at hsArc
      rcases Finset.mem_image.mp hsArc with ⟨k, _hk, hsk⟩
      exact ⟨e, k.1, by omega, hsk.symm⟩
    · rintro ⟨e, i, hi, rfl⟩
      change ((retainedArc e).vertices[i],
        (retainedArc e).vertices[i + 1]) ∈ segs
      apply segment_mem_segs
      dsimp [arcSegments]
      let k : Fin ((retainedArc e).vertices.length - 1) := ⟨i, by omega⟩
      exact Finset.mem_image.mpr ⟨k, by simp, by simp [k]⟩
  have hpointsSpec : forall q : EuclideanSpace ℝ (Fin 2),
      q ∈ Kclean.points ↔
        (exists e : G.edgeFinset, q ∈ (retainedArc e).vertices) ∨
        (exists v : V, q = D.vertexPlacement v) ∨
        q = x ∨
        (q ∈ D.crossingSet ∧
          exists s, s ∈ Kclean.segments ∧
            exists t, t ∈ Kclean.segments ∧
              s ≠ t ∧ q ∈ segment ℝ s.1 s.2 ∧
                q ∈ segment ℝ t.1 t.2) := by
    intro q
    change q ∈ pts ↔ _
    simp only [pts, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro (((hqArc | hqVertex) | hqx) | hqCross)
      · left
        dsimp [arcPts] at hqArc
        rcases Finset.mem_biUnion.mp hqArc with ⟨e, _he, hq⟩
        exact ⟨e, by simpa using hq⟩
      · right
        left
        dsimp [vertexPts] at hqVertex
        rcases Finset.mem_image.mp hqVertex with ⟨v, _hv, hq⟩
        exact ⟨v, hq.symm⟩
      · exact Or.inr (Or.inr (Or.inl hqx))
      · right
        right
        right
        have hqFilter := Finset.mem_filter.mp hqCross
        rcases hqFilter.2 with ⟨s, hs, t, ht, hst, hqs, hqt⟩
        exact ⟨hqFilter.1, s, hs, t, ht, hst, hqs, hqt⟩
    · rintro (hqArc | hqVertex | hqx | hqCross)
      · left
        left
        left
        rcases hqArc with ⟨e, hq⟩
        dsimp [arcPts]
        exact Finset.mem_biUnion.mpr ⟨e, by simp, by simpa using hq⟩
      · left
        left
        right
        rcases hqVertex with ⟨v, rfl⟩
        simp [vertexPts]
      · exact Or.inl (Or.inr hqx)
      · right
        apply Finset.mem_filter.mpr
        rcases hqCross with ⟨hqD, s, hs, t, ht, hst, hqs, hqt⟩
        exact ⟨hqD, s, hs, t, ht, hst, hqs, hqt⟩
  have hvertices : forall v : V, v ≠ u ->
      D.vertexPlacement v ∈ (Kclean.points : Set _) := by
    intro v _hv
    exact vertex_mem_pts v
  refine ⟨Kclean, hKcarrier, hsegmentsSpec, hpointsSpec, hvertices, ?_⟩
  ·
    intro p hpXA
    have hpSpec := (hXASpec p).1 hpXA
    have hpA : p ∈ A := hpSpec.1.1
    have hpNotEnds : p ∉ ({D.vertexPlacement u, x} : Set _) := hpSpec.1.2
    have hpH : p ∈ H := hpSpec.2
    have hpNeDu : p ≠ D.vertexPlacement u := by
      intro h
      exact hpNotEnds (by simp [h])
    have hpNeX : p ≠ x := by
      intro h
      exact hpNotEnds (by simp [h])
    have hpFirstCarrier : p ∈ firstArc.carrier :=
      FirstCut.prefix_carrier_subset (hA ▸ hpA)
    have hpFirstRelArc : p ∈ firstArc.relativeInterior := by
      rw [firstArc.relativeInterior_eq]
      refine ⟨hpFirstCarrier, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hpSource
        exact hpNeDu (hpSource.trans hfirstSource)
      · intro hpTarget
        have hpSuffix : p ∈ FirstCut.suffixArc.carrier := by
          have ht := arc_target_mem_carrier FirstCut.suffixArc
          simpa [FirstCut.suffix_target, hpTarget] using ht
        have hpBoth : p ∈ FirstCut.prefixArc.carrier ∩
            FirstCut.suffixArc.carrier := ⟨hA ▸ hpA, hpSuffix⟩
        have hpx : p = x := by
          have : p ∈ ({x} : Set _) := FirstCut.carrier_intersection ▸ hpBoth
          simpa using this
        exact hpNeX hpx
    have hpFirstRel : p ∈ (D.edgeArc firstEdge).relativeInterior := by
      simpa [hfirstRelative] using hpFirstRelArc
    have hpNotVertex : forall v : V, p ≠ D.vertexPlacement v := by
      intro v hpv
      exact D.no_vertex_in_edge_interior v firstEdge (hpv ▸ hpFirstRel)
    have owner_data : ∃ e : G.edgeFinset,
        e ≠ firstEdge ∧ e ≠ secondEdge ∧
          p ∈ (D.edgeArc e).relativeInterior := by
      rw [hH] at hpH
      rcases hpH with hpEdges | hpVertex
      · rcases Set.mem_iUnion.mp hpEdges with ⟨e, hpRetained⟩
        by_cases heFirst : e = firstEdge
        · subst e
          rw [if_pos rfl] at hpRetained
          exact False.elim (hpRetained.2 hpSpec.1)
        · rw [if_neg heFirst] at hpRetained
          by_cases heSecond : e = secondEdge
          · subst e
            rw [if_pos rfl] at hpRetained
            rcases second_special_cases hpRetained with hpTail | hpEndpoint
            · exact False.elim
                ((Set.disjoint_left.mp hATail hpA)
                  (by simpa [Tail.carrier_eq] using hpTail))
            · rcases hpEndpoint with hpDu | hpx
              · exact False.elim (hpNeDu hpDu)
              · exact False.elim (hpNeX hpx)
          · rw [if_neg heSecond] at hpRetained
            exact ⟨e, heFirst, heSecond,
              old_relative_of_carrier p hpNotVertex e hpRetained⟩
      · rcases hpVertex with ⟨v, _hv, hpv⟩
        exact False.elim (hpNotVertex v hpv)
    rcases owner_data with ⟨owner, hownerFirst, hownerSecond, hpOwnerRel⟩
    rcases hclean firstEdge owner p hownerFirst.symm hpFirstRel hpOwnerRel with
      ⟨iFirst, iOwner, hiFirst, hiOwner,
        hpFirstOpenOld, hpOwnerOpen, hOldNonparallel⟩
    rcases hFirstPrefixTransfer p iFirst hiFirst
        hpFirstOpenOld (hA ▸ hpA) hpNeX with
      ⟨j, hj, hpPrefixOpen, scale, hscale, hPrefixDirection⟩
    let s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
      ((D.edgeArc owner).vertices[iOwner],
        (D.edgeArc owner).vertices[iOwner + 1])
    have hsArc : s ∈ arcSegments (retainedArc owner) := by
      have hRetainedOwner : retainedArc owner = D.edgeArc owner := by
        simp [hretained, hownerFirst, hownerSecond]
      dsimp [arcSegments]
      let k : Fin ((retainedArc owner).vertices.length - 1) :=
        ⟨iOwner, by
          simp only [hRetainedOwner]
          omega⟩
      refine Finset.mem_image.mpr ⟨k, by simp, ?_⟩
      simp [k, s, hRetainedOwner]
    have hs : s ∈ segs := segment_mem_segs hsArc
    have hpSOpen : p ∈ openSegment ℝ s.1 s.2 := by
      simpa [s] using hpOwnerOpen
    have hNonparallel : ¬ exists c : ℝ, s.2 - s.1 =
        c • (FirstCut.prefixArc.vertices[j + 1] -
          FirstCut.prefixArc.vertices[j]) := by
      rintro ⟨c, hc⟩
      apply hOldNonparallel
      refine ⟨c * scale, ?_⟩
      rw [hPrefixDirection] at hc
      simpa [s, smul_smul] using hc
    have hpNotArcPts : p ∉ (arcPts : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hpArc
      dsimp [arcPts] at hpArc
      rcases Finset.mem_biUnion.mp hpArc with ⟨e, _he, hpVerticesFin⟩
      have hpVertices : p ∈ (retainedArc e).vertices := by
        simpa using hpVerticesFin
      have hpPieceCarrier : p ∈ (retainedArc e).carrier :=
        arc_vertex_mem_carrier _ hpVertices
      by_cases heFirst : e = firstEdge
      · subst e
        have hpSuffix : p ∈ FirstCut.suffixArc.carrier := by
          simpa [hretained] using hpPieceCarrier
        have hpBoth : p ∈ FirstCut.prefixArc.carrier ∩
            FirstCut.suffixArc.carrier := ⟨hA ▸ hpA, hpSuffix⟩
        have hpx : p = x := by
          have : p ∈ ({x} : Set _) := FirstCut.carrier_intersection ▸ hpBoth
          simpa using this
        exact hpNeX hpx
      · by_cases heSecond : e = secondEdge
        · subst e
          have hpTail : p ∈ Tail.tailArc.carrier := by
            simpa [hretained, hedges.symm] using hpPieceCarrier
          exact (Set.disjoint_left.mp hATail hpA) hpTail
        · have hpOldCarrier : p ∈ (D.edgeArc e).carrier := by
            simpa [hretained, heFirst, heSecond] using hpPieceCarrier
          have hpERel := old_relative_of_carrier p hpNotVertex e hpOldCarrier
          by_cases heOwner : e = owner
          · subst e
            exact open_not_vertices (D.edgeArc owner) p iOwner hiOwner
              hpOwnerOpen (by
                simpa [hretained, hownerFirst, hownerSecond] using hpVertices)
          · exact D.no_three_edge_interiors_meet
              (Ne.symm hownerFirst) (Ne.symm heFirst) (Ne.symm heOwner)
              hpFirstRel hpOwnerRel hpERel
    have hpNotVertexPts : p ∉
        (vertexPts : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hpVertex
      dsimp [vertexPts] at hpVertex
      rcases Finset.mem_image.mp hpVertex with ⟨v, _hv, hpv⟩
      exact hpNotVertex v hpv.symm
    have hpNotRetainedCrossings : p ∉
        (retainedCrossings : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hpCrossing
      have hpFilter := Finset.mem_filter.mp hpCrossing
      rcases hpFilter.2 with
        ⟨s₁, hs₁, t₁, ht₁, hst₁, hps₁, hpt₁⟩
      rcases segment_owner hs₁ with ⟨e, hs₁Arc⟩
      rcases segment_owner ht₁ with ⟨f, ht₁Arc⟩
      by_cases hef : e = f
      · subst f
        apply hpNotArcPts
        exact same_piece_intersection_arc_point e s₁ t₁ hs₁Arc ht₁Arc
          hst₁ p hps₁ hpt₁
      · have hpNeS₁Left : p ≠ s₁.1 := by
          intro h
          apply hpNotArcPts
          dsimp [arcSegments] at hs₁Arc
          rcases Finset.mem_image.mp hs₁Arc with ⟨k, _hk, hsk⟩
          subst s₁
          dsimp [arcPts]
          exact Finset.mem_biUnion.mpr
            ⟨e, by simp, by simp [h]⟩
        have hpNeS₁Right : p ≠ s₁.2 := by
          intro h
          apply hpNotArcPts
          dsimp [arcSegments] at hs₁Arc
          rcases Finset.mem_image.mp hs₁Arc with ⟨k, _hk, hsk⟩
          subst s₁
          dsimp [arcPts]
          exact Finset.mem_biUnion.mpr
            ⟨e, by simp, by simp [h]⟩
        have hpNeT₁Left : p ≠ t₁.1 := by
          intro h
          apply hpNotArcPts
          dsimp [arcSegments] at ht₁Arc
          rcases Finset.mem_image.mp ht₁Arc with ⟨k, _hk, htk⟩
          subst t₁
          dsimp [arcPts]
          exact Finset.mem_biUnion.mpr
            ⟨f, by simp, by simp [h]⟩
        have hpNeT₁Right : p ≠ t₁.2 := by
          intro h
          apply hpNotArcPts
          dsimp [arcSegments] at ht₁Arc
          rcases Finset.mem_image.mp ht₁Arc with ⟨k, _hk, htk⟩
          subst t₁
          dsimp [arcPts]
          exact Finset.mem_biUnion.mpr
            ⟨f, by simp, by simp [h]⟩
        have hps₁Open : p ∈ openSegment ℝ s₁.1 s₁.2 :=
          mem_openSegment_of_ne_left_right
            (Ne.symm hpNeS₁Left) (Ne.symm hpNeS₁Right) hps₁
        have hpt₁Open : p ∈ openSegment ℝ t₁.1 t₁.2 :=
          mem_openSegment_of_ne_left_right
            (Ne.symm hpNeT₁Left) (Ne.symm hpNeT₁Right) hpt₁
        have hpERel := piece_open_old_relative e s₁ hs₁Arc p hpNotVertex hps₁Open
        have hpFRel := piece_open_old_relative f t₁ ht₁Arc p hpNotVertex hpt₁Open
        by_cases heFirst : e = firstEdge
        · subst e
          have hpSuffix := arc_segment_mem_carrier
            (retainedArc firstEdge) hs₁Arc
              (openSegment_subset_segment ℝ _ _ hps₁Open)
          have hpBoth : p ∈ FirstCut.prefixArc.carrier ∩
              FirstCut.suffixArc.carrier :=
            ⟨hA ▸ hpA, by simpa [hretained] using hpSuffix⟩
          have hpx : p = x := by
            have : p ∈ ({x} : Set _) :=
              FirstCut.carrier_intersection ▸ hpBoth
            simpa using this
          exact hpNeX hpx
        · by_cases heSecond : e = secondEdge
          · subst e
            have hpTail := arc_segment_mem_carrier
              (retainedArc secondEdge) hs₁Arc
                (openSegment_subset_segment ℝ _ _ hps₁Open)
            exact (Set.disjoint_left.mp hATail hpA)
              (by simpa [hretained, hedges.symm] using hpTail)
          · by_cases hfFirst : f = firstEdge
            · subst f
              have hpSuffix := arc_segment_mem_carrier
                (retainedArc firstEdge) ht₁Arc
                  (openSegment_subset_segment ℝ _ _ hpt₁Open)
              have hpBoth : p ∈ FirstCut.prefixArc.carrier ∩
                  FirstCut.suffixArc.carrier :=
                ⟨hA ▸ hpA, by simpa [hretained] using hpSuffix⟩
              have hpx : p = x := by
                have : p ∈ ({x} : Set _) :=
                  FirstCut.carrier_intersection ▸ hpBoth
                simpa using this
              exact hpNeX hpx
            · by_cases hfSecond : f = secondEdge
              · subst f
                have hpTail := arc_segment_mem_carrier
                  (retainedArc secondEdge) ht₁Arc
                    (openSegment_subset_segment ℝ _ _ hpt₁Open)
                exact (Set.disjoint_left.mp hATail hpA)
                  (by simpa [hretained, hedges.symm] using hpTail)
              · exact D.no_three_edge_interiors_meet
                  (Ne.symm heFirst) (Ne.symm hfFirst) hef
                  hpFirstRel hpERel hpFRel
    have hpNotPoints : p ∉ (Kclean.points : Set _) := by
      intro hpPoints
      change p ∈ pts at hpPoints
      simp only [pts, Finset.mem_union, Finset.mem_singleton] at hpPoints
      rcases hpPoints with ((hpArc | hpVertex) | hpx) | hpCross
      · exact hpNotArcPts hpArc
      · exact hpNotVertexPts hpVertex
      · exact hpNeX hpx
      · exact hpNotRetainedCrossings hpCross
    have hUnique : forall t :
        EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        t ∈ Kclean.segments -> p ∈ openSegment ℝ t.1 t.2 -> t = s := by
      intro t ht hpTOpen
      change t ∈ segs at ht
      rcases segment_owner ht with ⟨e, htArc⟩
      have hpERel := piece_open_old_relative e t htArc p hpNotVertex hpTOpen
      have heOwner : e = owner := by
        by_contra heOwner
        by_cases heFirst : e = firstEdge
        · subst e
          have hpSuffix := arc_segment_mem_carrier
            (retainedArc firstEdge) htArc
              (openSegment_subset_segment ℝ _ _ hpTOpen)
          have hpBoth : p ∈ FirstCut.prefixArc.carrier ∩
              FirstCut.suffixArc.carrier :=
            ⟨hA ▸ hpA, by simpa [hretained] using hpSuffix⟩
          have hpx : p = x := by
            have : p ∈ ({x} : Set _) := FirstCut.carrier_intersection ▸ hpBoth
            simpa using this
          exact hpNeX hpx
        · exact D.no_three_edge_interiors_meet
            (Ne.symm hownerFirst) (Ne.symm heFirst) (Ne.symm heOwner)
            hpFirstRel hpOwnerRel hpERel
      subst e
      dsimp [arcSegments] at htArc
      rcases Finset.mem_image.mp htArc with ⟨k, _hk, htk⟩
      have hRetainedOwner : retainedArc owner = D.edgeArc owner := by
        simp [hretained, hownerFirst, hownerSecond]
      have hkSeg : k.1 + 1 < (retainedArc owner).vertices.length := by
        have hklt := k.isLt
        omega
      have hiOwner' : iOwner + 1 < (retainedArc owner).vertices.length := by
        simpa [hRetainedOwner] using hiOwner
      have hpTOpen' : p ∈ openSegment ℝ
          (retainedArc owner).vertices[k.1]
          (retainedArc owner).vertices[k.1 + 1] := by
        simpa only [← htk] using hpTOpen
      have hpOwnerOpen' : p ∈ openSegment ℝ
          (retainedArc owner).vertices[iOwner]
          (retainedArc owner).vertices[iOwner + 1] := by
        simpa [hRetainedOwner] using hpOwnerOpen
      have hkEq : k.1 = iOwner :=
        open_index_unique (retainedArc owner) p k.1 iOwner
          hkSeg hiOwner' hpTOpen' hpOwnerOpen'
      subst t
      ext <;> simp [s, hRetainedOwner, hkEq]
    rcases BigonRerouteFinitePresentationLocalBranch
        Kclean s hs p hpNotPoints hpSOpen with
      ⟨localRadius, hLocalRadius, hLocal⟩
    have hpNotTail : p ∉ Tail.tailArc.carrier :=
      Set.disjoint_left.mp hATail hpA
    have hTailOpen : IsOpen Tail.tailArc.carrierᶜ :=
      (PolygonalArcCarrierCompact Tail.tailArc).isClosed.isOpen_compl
    rcases Metric.isOpen_iff.mp hTailOpen p hpNotTail with
      ⟨tailRadius, hTailRadius, hTailBall⟩
    refine ⟨hpNotPoints, j, hj, hpPrefixOpen, s, hs, hpSOpen,
      hNonparallel, hUnique, ?_⟩
    intro upper hUpper
    let r : ℝ := min (localRadius / 2) (min (tailRadius / 2) (upper / 2))
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min (half_pos hLocalRadius)
        (lt_min (half_pos hTailRadius) (half_pos hUpper))
    have hrLocal : r ≤ localRadius :=
      (min_le_left _ _).trans (half_le_self hLocalRadius.le)
    have hrTail : r ≤ tailRadius :=
      (min_le_right _ _).trans
        ((min_le_left _ _).trans (half_le_self hTailRadius.le))
    have hrUpper : r < upper :=
      (min_le_right _ _).trans_lt
        ((min_le_right _ _).trans_lt (half_lt_self hUpper))
    refine ⟨r, hr, hrUpper, ?_, ?_⟩
    · ext q
      constructor
      · rintro ⟨hqBall, hqH⟩
        have hqLocal : q ∈ Metric.ball p localRadius :=
          Metric.ball_subset_ball hrLocal hqBall
        have hq := (Set.ext_iff.mp hLocal q).mp ⟨hqLocal, hqH⟩
        exact ⟨hqBall, hq.2⟩
      · rintro ⟨hqBall, hqSeg⟩
        have hqLocal : q ∈ Metric.ball p localRadius :=
          Metric.ball_subset_ball hrLocal hqBall
        have hq := (Set.ext_iff.mp hLocal q).mpr ⟨hqLocal, hqSeg⟩
        exact ⟨hqBall, hq.2⟩
    · ext q
      constructor
      · rintro ⟨hqBall, hqRbeta⟩
        have hqTailBall : q ∈ Metric.ball p tailRadius :=
          Metric.ball_subset_ball hrTail hqBall
        have hqNotTail := hTailBall hqTailBall
        have hfalse : False := hqNotTail (by
          simpa [Tail.carrier_eq] using hqRbeta)
        exact hfalse.elim
      · intro hq
        simpa using hq
