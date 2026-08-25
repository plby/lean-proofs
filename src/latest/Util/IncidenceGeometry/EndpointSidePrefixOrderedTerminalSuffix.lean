import Util.IncidenceGeometry.PolygonalArcPointCutDataExists
import Util.IncidenceGeometry.PolygonalArcEndpointGluedVertices
import Util.IncidenceGeometry.PolygonalArcEndpointGluedSegmentOccurrence
import Util.IncidenceGeometry.PolygonalArcOpenSegmentSubsetRelativeInterior
import Mathlib.Tactic


open Classical
noncomputable section

private lemma endpointSideArcLastVertex (Q : PolygonalArc)
    (hi : Q.vertices.length - 1 < Q.vertices.length) :
    Q.vertices[Q.vertices.length - 1]'hi = Q.target := by
  have htarget := Q.target_eq_last
  rw [List.getLast?_eq_getElem?] at htarget
  rw [List.getElem?_eq_getElem (by omega)] at htarget
  exact Option.some.inj htarget

private lemma endpointSideCutSuffixPenultimateBefore
    (Q : PolygonalArc) (c : EuclideanSpace ℝ (Fin 2))
    (D : PolygonalArcPointCutData Q c)
    (hcut : D.cutIndex < Q.vertices.length - 2) : ∀
    (hsidx : D.suffixArc.vertices.length - 2 < D.suffixArc.vertices.length)
    (hQidx : Q.vertices.length - 2 < Q.vertices.length),
    D.suffixArc.vertices[D.suffixArc.vertices.length - 2]'hsidx =
      Q.vertices[Q.vertices.length - 2]'hQidx := by
  intro hsidx hQidx
  have hQlen := Q.length_ge_two
  rcases D.suffix_drop_index_spec with hr | hr
  · rcases hr with ⟨hr, _⟩
    have hrle : D.suffixDropIndex ≤ Q.vertices.length - 2 := by omega
    have hsLen : D.suffixArc.vertices.length =
        1 + (Q.vertices.length - D.suffixDropIndex) := by
      rw [D.suffix_vertices_exact]
      simp [List.length_drop]
      omega
    let j := Q.vertices.length - 2 - D.suffixDropIndex
    have hj : j < (Q.vertices.drop D.suffixDropIndex).length := by
      dsimp [j]
      simp [List.length_drop]
      omega
    have hidx : D.suffixArc.vertices.length - 2 = j + 1 := by
      dsimp [j]
      omega
    have hconsIdx : j + 1 <
        (c :: Q.vertices.drop D.suffixDropIndex).length := by
      simp
      omega
    have hgetCons :
        (c :: Q.vertices.drop D.suffixDropIndex)[j + 1]'hconsIdx =
          (Q.vertices.drop D.suffixDropIndex)[j]'hj := by simp
    calc
      D.suffixArc.vertices[D.suffixArc.vertices.length - 2] =
          (c :: Q.vertices.drop D.suffixDropIndex)[j + 1] :=
        getElem_congr D.suffix_vertices_exact hidx hsidx
      _ = (Q.vertices.drop D.suffixDropIndex)[j] := hgetCons
      _ = Q.vertices[D.suffixDropIndex + j] := List.getElem_drop
      _ = Q.vertices[Q.vertices.length - 2] := by
        apply getElem_congr rfl
        dsimp [j]
        omega
  · rcases hr with ⟨hr, hc⟩
    have hrle : D.suffixDropIndex ≤ Q.vertices.length - 1 := by omega
    by_cases hre : D.suffixDropIndex = Q.vertices.length - 1
    · have hcutEq : D.cutIndex = Q.vertices.length - 3 := by omega
      have hidxEq : D.cutIndex + 1 = Q.vertices.length - 2 := by omega
      have hcEq : c = Q.vertices[Q.vertices.length - 2] := by
        calc
          c = Q.vertices[D.cutIndex + 1] := hc
          _ = Q.vertices[Q.vertices.length - 2] := by congr
      have hdrop : Q.vertices.drop D.suffixDropIndex =
          [Q.vertices[Q.vertices.length - 1]] := by
        rw [hre]
        rw [List.drop_eq_getElem_cons (by omega)]
        have htail : Q.vertices.drop (Q.vertices.length - 1 + 1) = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp [Nat.sub_add_cancel (by omega : 1 ≤ Q.vertices.length)]
        rw [htail]
      have hsList : D.suffixArc.vertices =
          [c, Q.vertices[Q.vertices.length - 1]] := by
        rw [D.suffix_vertices_exact, hdrop]
      have hidx0 : D.suffixArc.vertices.length - 2 = 0 := by
        rw [hsList]
        simp
      calc
        D.suffixArc.vertices[D.suffixArc.vertices.length - 2] =
            [c, Q.vertices[Q.vertices.length - 1]][0] :=
          getElem_congr hsList hidx0 hsidx
        _ = c := rfl
        _ = Q.vertices[Q.vertices.length - 2] := hcEq
    · have hrle' : D.suffixDropIndex ≤ Q.vertices.length - 2 := by omega
      have hsLen : D.suffixArc.vertices.length =
          1 + (Q.vertices.length - D.suffixDropIndex) := by
        rw [D.suffix_vertices_exact]
        simp [List.length_drop]
        omega
      let j := Q.vertices.length - 2 - D.suffixDropIndex
      have hj : j < (Q.vertices.drop D.suffixDropIndex).length := by
        dsimp [j]
        simp [List.length_drop]
        omega
      have hidx : D.suffixArc.vertices.length - 2 = j + 1 := by
        dsimp [j]
        omega
      have hconsIdx : j + 1 <
          (c :: Q.vertices.drop D.suffixDropIndex).length := by
        simp
        omega
      have hgetCons :
          (c :: Q.vertices.drop D.suffixDropIndex)[j + 1]'hconsIdx =
            (Q.vertices.drop D.suffixDropIndex)[j]'hj := by simp
      calc
        D.suffixArc.vertices[D.suffixArc.vertices.length - 2] =
            (c :: Q.vertices.drop D.suffixDropIndex)[j + 1] :=
          getElem_congr D.suffix_vertices_exact hidx hsidx
        _ = (Q.vertices.drop D.suffixDropIndex)[j] := hgetCons
        _ = Q.vertices[D.suffixDropIndex + j] := List.getElem_drop
        _ = Q.vertices[Q.vertices.length - 2] := by
          apply getElem_congr rfl
          dsimp [j]
          omega

private lemma endpointSideCutSuffixPenultimateAtLast
    (Q : PolygonalArc) (c : EuclideanSpace ℝ (Fin 2))
    (D : PolygonalArcPointCutData Q c)
    (hcTarget : c ≠ Q.target)
    (hcut : D.cutIndex = Q.vertices.length - 2) : ∀
    (hsidx : D.suffixArc.vertices.length - 2 < D.suffixArc.vertices.length),
    D.suffixArc.vertices[D.suffixArc.vertices.length - 2]'hsidx = c := by
  intro hsidx
  have hQlen := Q.length_ge_two
  have hrightQ : Q.vertices[Q.vertices.length - 1] = Q.target :=
    endpointSideArcLastVertex Q (by omega)
  rcases D.suffix_drop_index_spec with hr | hr
  · rcases hr with ⟨hr, _⟩
    have hrEq : D.suffixDropIndex = Q.vertices.length - 1 := by omega
    have hdrop : Q.vertices.drop D.suffixDropIndex =
        [Q.vertices[Q.vertices.length - 1]] := by
      rw [hrEq]
      rw [List.drop_eq_getElem_cons (by omega)]
      have htail : Q.vertices.drop (Q.vertices.length - 1 + 1) = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp [Nat.sub_add_cancel (by omega : 1 ≤ Q.vertices.length)]
      rw [htail]
    have hsList : D.suffixArc.vertices =
        [c, Q.vertices[Q.vertices.length - 1]] := by
      rw [D.suffix_vertices_exact, hdrop]
    have hidx0 : D.suffixArc.vertices.length - 2 = 0 := by
      rw [hsList]
      simp
    calc
      D.suffixArc.vertices[D.suffixArc.vertices.length - 2] =
          [c, Q.vertices[Q.vertices.length - 1]][0] :=
        getElem_congr hsList hidx0 hsidx
      _ = c := rfl
  · rcases hr with ⟨_, hc⟩
    apply False.elim
    apply hcTarget
    calc
      c = Q.vertices[D.cutIndex + 1] := hc
      _ = Q.vertices[Q.vertices.length - 1] := by
        congr 1
        omega
      _ = Q.target := hrightQ

lemma EndpointSidePrefixOrderedTerminalSuffix
    (Pq chain predecessor approach terminalSegment : PolygonalArc)
    (SelectedSide Vin : Set (EuclideanSpace ℝ (Fin 2)))
    (xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (q lastGate h terminalGate : EuclideanSpace ℝ (Fin 2)) :
    chain.source = predecessor.source →
      chain.target = terminalGate →
        terminalSegment.source = h →
          terminalSegment.target = terminalGate →
            terminalSegment.carrier = segment ℝ h terminalGate →
              chain.vertices =
                PolygonalArcEndpointGluedVertices
                  [predecessor, approach, terminalSegment] →
                chain.carrier =
                  predecessor.carrier ∪ approach.carrier ∪
                    terminalSegment.carrier →
                  predecessor.carrier ∩ approach.carrier =
                    ({lastGate} : Set (EuclideanSpace ℝ (Fin 2))) →
                    approach.carrier ∩ terminalSegment.carrier =
                      ({h} : Set (EuclideanSpace ℝ (Fin 2))) →
                      Disjoint predecessor.carrier terminalSegment.carrier →
                        Pq.target = q →
            q ∈ chain.carrier →
              q ≠ terminalGate →
                Pq.carrier ∩ chain.carrier =
                  ({q} : Set (EuclideanSpace ℝ (Fin 2))) →
                  predecessor.carrier ⊆ SelectedSide ∩ Vin →
                    approach.carrier ⊆ SelectedSide ∩ Vin →
                      predecessor.target = lastGate →
                        approach.source = lastGate →
                          approach.target = h →
                            segment ℝ h terminalGate ⊆
                              Vin ∪
                                ({terminalGate} :
                                  Set (EuclideanSpace ℝ (Fin 2))) →
                              openSegment ℝ h terminalGate ⊆ Vin →
                                Vin ⊆ SelectedSide →
                                  terminalGate ∉ SelectedSide →
                                    ∃ lastGate' h' :
                                        EuclideanSpace ℝ (Fin 2),
                                      ∃ suffix Cprev' approach' final' : PolygonalArc,
                                        lastGate' ∉ xClean ∧
                                          h' ∉ xClean ∧
                                            suffix.source = q ∧
                                              suffix.target = terminalGate ∧
                                                suffix.carrier =
                                                  Cprev'.carrier ∪
                                                    approach'.carrier ∪
                                                      final'.carrier ∧
                                                  ((q = chain.source ∧
                                                      suffix = chain) ∨
                                                    ∃ D :
                                                        PolygonalArcPointCutData chain q,
                                                      suffix = D.suffixArc) ∧
                                                    Cprev'.source = q ∧
                                                      Cprev'.target = lastGate' ∧
                                                        approach'.source = lastGate' ∧
                                                          approach'.target = h' ∧
                                                            final'.source = h' ∧
                                                              final'.target = terminalGate ∧
                                                                Cprev'.carrier ⊆
                                                                  SelectedSide ∩ Vin ∧
                                                                  approach'.carrier ⊆
                                                                    SelectedSide ∩ Vin ∧
                                                                    final'.carrier =
                                                                      segment ℝ h' terminalGate ∧
                                                                      final'.carrier ⊆
                                                                        Vin ∪
                                                                          ({terminalGate} :
                                                                            Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                        final'.relativeInterior ⊆ Vin ∧
                                                                          Cprev'.carrier ⊆ chain.carrier ∧
                                                                            approach'.carrier ⊆ chain.carrier ∧
                                                                              final'.carrier ⊆ chain.carrier ∧
                                                                        Pq.carrier ∩ Cprev'.carrier =
                                                                          ({q} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                          Disjoint Pq.carrier approach'.carrier ∧
                                                                            Disjoint Pq.carrier final'.carrier ∧
                                                                              Cprev'.carrier ∩ approach'.carrier =
                                                                                ({lastGate'} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                approach'.carrier ∩ final'.carrier =
                                                                                  ({h'} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                                                  Disjoint Cprev'.carrier final'.carrier ∧
                                                                                    ∀ piece : PolygonalArc,
                                                                                      piece ∈ [Cprev', approach', final'] →
                                                                                        ∀ z i
                                                                                          (hi : i + 1 < chain.vertices.length),
                                                                                          z ∈ openSegment ℝ
                                                                                              chain.vertices[i]
                                                                                              chain.vertices[i + 1] →
                                                                                            z ∈ piece.carrier →
                                                                                              z ∉
                                                                                                ({q, lastGate', h', terminalGate} :
                                                                                                  Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                                ∃ j : ℕ,
                                                                                                  ∃ hj : j + 1 <
                                                                                                      piece.vertices.length,
                                                                                                    z ∈ openSegment ℝ
                                                                                                        piece.vertices[j]
                                                                                                        piece.vertices[j + 1] ∧
                                                                                                      ∃ c : ℝ, c ≠ 0 ∧
                                                                                                        piece.vertices[j + 1] -
                                                                                                            piece.vertices[j] =
                                                                                                          c •
                                                                                                            (chain.vertices[i + 1] -
                                                                                                              chain.vertices[i]) := by
  intro hchain_source hchain_target hterminal_source hterminal_target
    hterminal_carrier hchain_vertices hchain_carrier
    hpredecessor_approach happ_terminal hpredecessor_terminal
    hPq_target hq_chain hq_ne_terminal hPq_chain
    hpredecessor_side happ_side hpredecessor_target happ_source happ_target
    hterminal_Vin hopen_terminal hVin_side hterminal_not_side
  have arc_source_mem (Q : PolygonalArc) : Q.source ∈ Q.carrier := by
    have hlen := Q.length_ge_two
    rw [Q.carrier_eq]
    refine ⟨0, by omega, ?_⟩
    have hfirst : Q.vertices[0] = Q.source := by
      have hhead := Q.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    rw [hfirst]
    exact left_mem_segment ℝ Q.source Q.vertices[1]
  have arc_target_mem (Q : PolygonalArc) : Q.target ∈ Q.carrier := by
    have hlen := Q.length_ge_two
    rw [Q.carrier_eq]
    let k := Q.vertices.length - 2
    have hk : k + 1 < Q.vertices.length := by
      dsimp [k]
      omega
    refine ⟨k, hk, ?_⟩
    have hlast : Q.vertices[k + 1] = Q.target := by
      have htarget := Q.target_eq_last
      rw [List.getLast?_eq_getElem?] at htarget
      rw [List.getElem?_eq_getElem (by omega)] at htarget
      have hidx : k + 1 = Q.vertices.length - 1 := by
        dsimp [k]
        omega
      simpa [hidx] using Option.some.inj htarget
    rw [hlast]
    exact right_mem_segment ℝ Q.vertices[k] Q.target
  have arc_last_vertex (Q : PolygonalArc)
      (hi : Q.vertices.length - 1 < Q.vertices.length) :
      Q.vertices[Q.vertices.length - 1]'hi = Q.target := by
    have htarget := Q.target_eq_last
    rw [List.getLast?_eq_getElem?] at htarget
    rw [List.getElem?_eq_getElem (by omega)] at htarget
    exact Option.some.inj htarget
  have lineMap_mem_segment_right
      (A B : EuclideanSpace ℝ (Fin 2)) (s t : ℝ)
      (hs : s < 1) (hst : s ≤ t) (ht : t ≤ 1) :
      AffineMap.lineMap A B t ∈
        segment ℝ (AffineMap.lineMap A B s) B := by
    rw [segment_eq_image_lineMap]
    let theta : ℝ := (t - s) / (1 - s)
    have hden : 0 < 1 - s := sub_pos.mpr hs
    have htheta0 : 0 ≤ theta :=
      div_nonneg (sub_nonneg.mpr hst) hden.le
    have htheta1 : theta ≤ 1 := by
      dsimp [theta]
      apply (div_le_one hden).2
      linarith
    refine ⟨theta, ⟨htheta0, htheta1⟩, ?_⟩
    have hdenne : 1 - s ≠ 0 := ne_of_gt hden
    have hcoeffA : (1 - theta) * (1 - s) = 1 - t := by
      dsimp [theta]
      field_simp
      ring
    have hcoeffB : (1 - theta) * s + theta = t := by
      dsimp [theta]
      field_simp
      ring
    simp only [AffineMap.lineMap_apply_module, smul_add, smul_smul]
    rw [hcoeffA, add_assoc, ← add_smul, hcoeffB]
  have lineMap_mem_segment_left
      (A B : EuclideanSpace ℝ (Fin 2)) (s t : ℝ)
      (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
      AffineMap.lineMap A B s ∈
        segment ℝ A (AffineMap.lineMap A B t) := by
    by_cases ht0 : t = 0
    · have hs0 : s = 0 := by linarith
      subst s
      subst t
      simp
    · rw [segment_eq_image_lineMap]
      let theta : ℝ := s / t
      have htpos : 0 < t := lt_of_le_of_ne (hs.trans hst) (Ne.symm ht0)
      have htheta0 : 0 ≤ theta := div_nonneg hs htpos.le
      have htheta1 : theta ≤ 1 := (div_le_one htpos).2 hst
      refine ⟨theta, ⟨htheta0, htheta1⟩, ?_⟩
      have hcoeffA : (1 - theta) + theta * (1 - t) = 1 - s := by
        dsimp [theta]
        field_simp
        ring
      have hcoeffB : theta * t = s := by
        dsimp [theta]
        field_simp
      simp only [AffineMap.lineMap_apply_module, smul_add, smul_smul]
      rw [← add_assoc, ← add_smul, hcoeffA, hcoeffB]
  have lineMap_mem_segment_interval
      (A B : EuclideanSpace ℝ (Fin 2)) (r s t : ℝ)
      (hrt : r < t) (hrs : r ≤ s) (hst : s ≤ t) :
      AffineMap.lineMap A B s ∈
        segment ℝ (AffineMap.lineMap A B r) (AffineMap.lineMap A B t) := by
    rw [segment_eq_image_lineMap]
    let theta : ℝ := (s - r) / (t - r)
    have hden : 0 < t - r := sub_pos.mpr hrt
    have htheta0 : 0 ≤ theta :=
      div_nonneg (sub_nonneg.mpr hrs) hden.le
    have htheta1 : theta ≤ 1 := by
      dsimp [theta]
      apply (div_le_one hden).2
      linarith
    refine ⟨theta, ⟨htheta0, htheta1⟩, ?_⟩
    have hcoeffA :
        (1 - theta) * (1 - r) + theta * (1 - t) = 1 - s := by
      dsimp [theta]
      field_simp
      ring
    have hcoeffB : (1 - theta) * r + theta * t = s := by
      dsimp [theta]
      field_simp
      ring
    simp only [AffineMap.lineMap_apply_module, smul_add, smul_smul]
    rw [← hcoeffA, ← hcoeffB]
    module
  have hchainLen := chain.length_ge_two
  let n := chain.vertices.length - 2
  have hn : n + 1 < chain.vertices.length := by
    dsimp [n]
    omega
  have hsuccessive :
      ∀ k (hk : k + 1 < [predecessor, approach, terminalSegment].length),
        ([predecessor, approach, terminalSegment][k]).target =
          ([predecessor, approach, terminalSegment][k + 1]).source := by
    intro k hk
    have hkCases : k = 0 ∨ k = 1 := by
      simp at hk
      omega
    rcases hkCases with rfl | rfl
    · simpa [hpredecessor_target] using happ_source.symm
    · simpa using happ_target.trans hterminal_source.symm
  have hnG : n + 1 <
      (PolygonalArcEndpointGluedVertices
        [predecessor, approach, terminalSegment]).length := by
    rw [← hchain_vertices]
    exact hn
  obtain ⟨k, hk, m, hm, hindex, hleft, hright⟩ :=
    PolygonalArcEndpointGluedSegmentOccurrence
      [predecessor, approach, terminalSegment] hsuccessive n hnG
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 := by
    simp at hk
    omega
  have hterminalLen := terminalSegment.length_ge_two
  have hpredecessorLen := predecessor.length_ge_two
  have happLen := approach.length_ge_two
  have hgluedLen : chain.vertices.length = predecessor.vertices.length +
      (approach.vertices.length - 1) +
        (terminalSegment.vertices.length - 1) := by
    rw [hchain_vertices]
    simp [PolygonalArcEndpointGluedVertices, List.length_append,
      List.length_tail, Nat.add_assoc]
  have hchain_last_pair :
      chain.vertices[n] =
          terminalSegment.vertices[terminalSegment.vertices.length - 2] ∧
        chain.vertices[n + 1] = terminalGate := by
    rcases hkCases with rfl | rfl | rfl
    · simp at hm hindex
      dsimp [n] at hindex
      omega
    · simp at hm hindex
      dsimp [n] at hindex
      omega
    · simp at hm hindex hleft hright
      have hmEq : m = terminalSegment.vertices.length - 2 := by
        dsimp [n] at hindex
        omega
      subst m
      constructor
      · simpa [n, hchain_vertices] using hleft
      · have hright' :
            chain.vertices[n + 1] =
              terminalSegment.vertices[terminalSegment.vertices.length - 2 + 1] := by
            simpa [hchain_vertices] using hright
        have hidx : terminalSegment.vertices.length - 2 + 1 =
            terminalSegment.vertices.length - 1 := by omega
        calc
          chain.vertices[n + 1] =
              terminalSegment.vertices[terminalSegment.vertices.length - 2 + 1] :=
            hright'
          _ = terminalSegment.vertices[terminalSegment.vertices.length - 1] :=
            getElem_congr rfl hidx hm
          _ = terminalSegment.target := arc_last_vertex terminalSegment (by omega)
          _ = terminalGate := hterminal_target
  let A := chain.vertices[n]
  have hAg : A ≠ terminalGate := by
    intro heq
    have hvertexEq : chain.vertices[n] = chain.vertices[n + 1] := by
      simpa [A, hchain_last_pair.2] using heq
    have hidxEq : n = n + 1 :=
      chain.simple_vertices.getElem_inj_iff.mp hvertexEq
    omega
  have hlast_segment_terminal :
      segment ℝ A terminalGate ⊆ terminalSegment.carrier := by
    intro z hz
    rw [terminalSegment.carrier_eq]
    refine ⟨terminalSegment.vertices.length - 2, by omega, ?_⟩
    have hlastTerm :
        terminalSegment.vertices[terminalSegment.vertices.length - 2 + 1] =
          terminalGate := by
      have hidx : terminalSegment.vertices.length - 2 + 1 =
          terminalSegment.vertices.length - 1 := by omega
      calc
        terminalSegment.vertices[terminalSegment.vertices.length - 2 + 1] =
            terminalSegment.vertices[terminalSegment.vertices.length - 1] :=
          getElem_congr rfl hidx (by omega)
        _ = terminalSegment.target := arc_last_vertex terminalSegment (by omega)
        _ = terminalGate := hterminal_target
    simpa [A, hchain_last_pair.1, hlastTerm] using hz
  have hlast_open_terminal :
      openSegment ℝ A terminalGate ⊆ openSegment ℝ h terminalGate := by
    intro z hz
    have hzterm : z ∈ terminalSegment.relativeInterior := by
      apply PolygonalArcOpenSegmentSubsetRelativeInterior terminalSegment
        (terminalSegment.vertices.length - 2) (by omega)
      have hlastTerm :
          terminalSegment.vertices[terminalSegment.vertices.length - 2 + 1] =
            terminalGate := by
        have hidx : terminalSegment.vertices.length - 2 + 1 =
            terminalSegment.vertices.length - 1 := by omega
        calc
          terminalSegment.vertices[terminalSegment.vertices.length - 2 + 1] =
              terminalSegment.vertices[terminalSegment.vertices.length - 1] :=
            getElem_congr rfl hidx (by omega)
          _ = terminalSegment.target := arc_last_vertex terminalSegment (by omega)
          _ = terminalGate := hterminal_target
      simpa [A, hchain_last_pair.1, hlastTerm] using hz
    rw [terminalSegment.relativeInterior_eq, hterminal_carrier,
      hterminal_source, hterminal_target] at hzterm
    have hzends := hzterm.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzends
    exact mem_openSegment_of_ne_left_right (Ne.symm hzends.1)
      (Ne.symm hzends.2) hzterm.1
  let f : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun t => AffineMap.lineMap A terminalGate t
  obtain ⟨tq, htq, hq_param⟩ :
      ∃ tq : ℝ, tq ∈ Set.Icc (0 : ℝ) 1 ∧
        ((q ∈ segment ℝ A terminalGate ∧ q = f tq) ∨
          (q ∉ segment ℝ A terminalGate ∧ tq = 0)) := by
    by_cases hqLast : q ∈ segment ℝ A terminalGate
    · rw [segment_eq_image_lineMap] at hqLast
      rcases hqLast with ⟨tq, htq, hqtq⟩
      refine ⟨tq, htq, Or.inl ⟨?_, ?_⟩⟩
      · rw [segment_eq_image_lineMap]
        exact ⟨tq, htq, hqtq⟩
      · simpa [f] using hqtq.symm
    · exact ⟨0, by norm_num, Or.inr ⟨hqLast, rfl⟩⟩
  have htq_lt : tq < 1 := by
    rcases hq_param with hq_param | hq_param
    · apply lt_of_le_of_ne htq.2
      intro htq1
      apply hq_ne_terminal
      simpa [f, htq1] using hq_param.2
    · rw [hq_param.2]
      norm_num
  have hsuffix_package :
      ∃ suffix : PolygonalArc,
        suffix.source = q ∧
          suffix.target = terminalGate ∧
            suffix.carrier ⊆ chain.carrier ∧
              ((q = chain.source ∧ suffix = chain) ∨
                ∃ D : PolygonalArcPointCutData chain q,
                  suffix = D.suffixArc) ∧
                (∀ t : ℝ, tq < t → t ≤ 1 → f t ∈ suffix.carrier) ∧
                  ∀ z i (hi : i + 1 < chain.vertices.length),
                    z ∈ openSegment ℝ chain.vertices[i] chain.vertices[i + 1] →
                      z ∈ suffix.carrier →
                        z ≠ q →
                          ∃ j : ℕ, ∃ hj : j + 1 < suffix.vertices.length,
                            z ∈ openSegment ℝ suffix.vertices[j]
                                suffix.vertices[j + 1] ∧
                              ∃ c : ℝ, c ≠ 0 ∧
                                suffix.vertices[j + 1] - suffix.vertices[j] =
                                  c • (chain.vertices[i + 1] - chain.vertices[i]) := by
    by_cases hqSource : q = chain.source
    · refine ⟨chain, hqSource.symm, hchain_target, Set.Subset.rfl,
        Or.inl ⟨hqSource, rfl⟩, ?_, ?_⟩
      · intro t htqt ht1
        rw [chain.carrier_eq]
        refine ⟨n, hn, ?_⟩
        rw [segment_eq_image_lineMap]
        refine ⟨t, ⟨htq.1.trans htqt.le, ht1⟩, ?_⟩
        simp [f, A, hchain_last_pair.2]
      · intro z i hi hz _hzCarrier _hzq
        refine ⟨i, hi, hz, 1, one_ne_zero, ?_⟩
        simp
    · have hqInterior : q ∈ chain.relativeInterior := by
        rw [chain.relativeInterior_eq]
        refine ⟨hq_chain, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hqSource, fun hqt => hq_ne_terminal (hqt.trans hchain_target)⟩
      obtain ⟨D⟩ := PolygonalArcPointCutDataExists chain q hqInterior
      refine ⟨D.suffixArc, D.suffix_source, D.suffix_target.trans hchain_target,
        D.suffix_carrier_subset, Or.inr ⟨D, rfl⟩, ?_, ?_⟩
      · intro t htqt ht1
        rw [D.suffix_carrier_region]
        have hcutLe : D.cutIndex ≤ n := by
          dsimp [n]
          apply Nat.le_sub_of_add_le
          exact Nat.succ_le_of_lt D.cutIndex_valid
        by_cases hcutLt : D.cutIndex < n
        · exact Or.inr ⟨n, hn, hcutLt, by
            rw [segment_eq_image_lineMap]
            refine ⟨t, ⟨htq.1.trans htqt.le, ht1⟩, ?_⟩
            simp [f, A, hchain_last_pair.2]⟩
        · have hcutEq : D.cutIndex = n := by omega
          have hqLast : q ∈ segment ℝ A terminalGate := by
            simpa [hcutEq, A, hchain_last_pair.2] using D.cut_mem_segment
          have hqf : q = f tq := by
            rcases hq_param with hq_param | hq_param
            · exact hq_param.2
            · exact False.elim (hq_param.1 hqLast)
          exact Or.inl (by
            simpa [hcutEq, hchain_last_pair.2, hqf, f] using
              lineMap_mem_segment_right A terminalGate tq t htq_lt htqt.le ht1)
      · intro z i hi hz hzCarrier hzq
        exact D.suffix_segment_transfer z i hi hz hzCarrier hzq
  rcases hsuffix_package with
    ⟨suffix, hsuffix_source, hsuffix_target, hsuffix_subset,
      hsuffix_alternative, hsuffix_after, hsuffix_transfer⟩
  have hsuffixLen := suffix.length_ge_two
  let ns := suffix.vertices.length - 2
  have hns : ns + 1 < suffix.vertices.length := by
    dsimp [ns]
    omega
  obtain ⟨s0, hs0_nonneg, hs0_le_tq, hsuffix_penultimate⟩ :
      ∃ s0 : ℝ, 0 ≤ s0 ∧ s0 ≤ tq ∧ suffix.vertices[ns] = f s0 := by
    rcases hsuffix_alternative with hs | ⟨D, hs⟩
    · rcases hs with ⟨_, rfl⟩
      refine ⟨0, le_rfl, htq.1, ?_⟩
      simp [ns, n, f, A]
    · subst suffix
      have hcutLe : D.cutIndex ≤ n := by
        dsimp [n]
        apply Nat.le_sub_of_add_le
        exact Nat.succ_le_of_lt D.cutIndex_valid
      by_cases hcutLt : D.cutIndex < n
      · refine ⟨0, le_rfl, htq.1, ?_⟩
        have hp := endpointSideCutSuffixPenultimateBefore chain q D (by
          simpa [n] using hcutLt) (by omega) (by omega)
        simpa [ns, n, f, A] using hp
      · have hcutEq : D.cutIndex = n := by omega
        refine ⟨tq, htq.1, le_rfl, ?_⟩
        have hp := endpointSideCutSuffixPenultimateAtLast chain q D
          (fun hqt => hq_ne_terminal (hqt.trans hchain_target))
          (by simpa [n] using hcutEq) (by omega)
        have hqf : q = f tq := by
          have hqLast : q ∈ segment ℝ A terminalGate := by
            simpa [hcutEq, A, hchain_last_pair.2] using D.cut_mem_segment
          rcases hq_param with hq_param | hq_param
          · exact hq_param.2
          · exact False.elim (hq_param.1 hqLast)
        simpa [ns, hqf] using hp
  have hsuffix_last : suffix.vertices[ns + 1] = terminalGate := by
    have hidx : ns + 1 = suffix.vertices.length - 1 := by
      dsimp [ns]
      omega
    calc
      suffix.vertices[ns + 1] =
          suffix.vertices[suffix.vertices.length - 1] :=
        getElem_congr rfl hidx hns
      _ = suffix.target := arc_last_vertex suffix (by omega)
      _ = terminalGate := hsuffix_target
  let forbidden : Finset (EuclideanSpace ℝ (Fin 2)) :=
    xClean ∪ suffix.vertices.toFinset
  let bad : Finset ℝ :=
    forbidden.preimage f (AffineMap.lineMap_injective ℝ hAg).injOn
  obtain ⟨tb, htb, htb_bad⟩ :=
    (Set.Ioo_infinite htq_lt).exists_notMem_finset bad
  obtain ⟨ta, hta, hta_bad⟩ :=
    (Set.Ioo_infinite htb.1).exists_notMem_finset bad
  let lastGate' := f ta
  let h' := f tb
  have hlastGate_clean : lastGate' ∉ xClean := by
    intro hmem
    apply hta_bad
    apply Finset.mem_preimage.mpr
    exact Finset.mem_union_left _ hmem
  have hh_clean : h' ∉ xClean := by
    intro hmem
    apply htb_bad
    apply Finset.mem_preimage.mpr
    exact Finset.mem_union_left _ hmem
  have hlastGate_open : lastGate' ∈ openSegment ℝ A terminalGate := by
    apply lineMap_mem_openSegment
    exact ⟨htq.1.trans_lt hta.1, hta.2.trans htb.2⟩
  have hh_open : h' ∈ openSegment ℝ A terminalGate := by
    apply lineMap_mem_openSegment
    exact ⟨htq.1.trans_lt htb.1, htb.2⟩
  have hlastGate_suffix : lastGate' ∈ suffix.carrier :=
    hsuffix_after ta hta.1 (hta.2.trans htb.2).le
  have hh_suffix : h' ∈ suffix.carrier :=
    hsuffix_after tb htb.1 htb.2.le
  have hq_ne_lastGate : q ≠ lastGate' := by
    rcases hq_param with hq_param | hq_param
    · intro heq
      apply (ne_of_lt hta.1)
      apply AffineMap.lineMap_injective ℝ hAg
      simpa [lastGate', hq_param.2, f] using heq
    · intro heq
      apply hq_param.1
      rw [heq]
      exact openSegment_subset_segment ℝ A terminalGate hlastGate_open
  have hq_ne_h : q ≠ h' := by
    rcases hq_param with hq_param | hq_param
    · intro heq
      apply (ne_of_lt htb.1)
      apply AffineMap.lineMap_injective ℝ hAg
      simpa [h', hq_param.2, f] using heq
    · intro heq
      apply hq_param.1
      rw [heq]
      exact openSegment_subset_segment ℝ A terminalGate hh_open
  have hlastGate_ne_h : lastGate' ≠ h' := by
    intro heq
    apply (ne_of_lt hta.2)
    apply AffineMap.lineMap_injective ℝ hAg
    simpa [lastGate', h', f] using heq
  have hh_ne_terminal : h' ≠ terminalGate := by
    intro heq
    apply (ne_of_lt htb.2)
    apply AffineMap.lineMap_injective ℝ hAg
    simpa [h', f] using heq
  have hlastGate_ne_terminal : lastGate' ≠ terminalGate := by
    intro heq
    apply (ne_of_lt (hta.2.trans htb.2))
    apply AffineMap.lineMap_injective ℝ hAg
    simpa [lastGate', f] using heq
  have hh_interior : h' ∈ suffix.relativeInterior := by
    rw [suffix.relativeInterior_eq]
    refine ⟨hh_suffix, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun heq => hq_ne_h (heq.trans hsuffix_source).symm,
      fun heq => hh_ne_terminal (heq.trans hsuffix_target)⟩
  obtain ⟨D1⟩ := PolygonalArcPointCutDataExists suffix h' hh_interior
  let R := D1.prefixArc
  let final' := D1.suffixArc
  have hh_last_suffix_segment :
      h' ∈ openSegment ℝ suffix.vertices[ns] suffix.vertices[ns + 1] := by
    have hs0_lt_tb : s0 < tb := hs0_le_tq.trans_lt htb.1
    have hseg : f tb ∈ segment ℝ (f s0) terminalGate :=
      lineMap_mem_segment_right A terminalGate s0 tb
        (hs0_lt_tb.trans htb.2) hs0_lt_tb.le htb.2.le
    have hneLeft : f s0 ≠ f tb :=
      (AffineMap.lineMap_injective ℝ hAg).ne (ne_of_lt hs0_lt_tb)
    have hneRight : terminalGate ≠ f tb := by
      intro heq
      exact hh_ne_terminal (by simpa [h', f] using heq.symm)
    simpa [hsuffix_penultimate, hsuffix_last, h'] using
      mem_openSegment_of_ne_left_right hneLeft hneRight hseg
  have hD1cut : D1.cutIndex = ns := by
    have hcutLe : D1.cutIndex ≤ ns := by
      dsimp [ns]
      apply Nat.le_sub_of_add_le
      exact Nat.succ_le_of_lt D1.cutIndex_valid
    by_contra hne
    have hcutLt : D1.cutIndex < ns := lt_of_le_of_ne hcutLe hne
    have hinter := suffix.segment_intersections D1.cutIndex_valid hns hcutLt
    have hhinter : h' ∈
        segment ℝ suffix.vertices[D1.cutIndex] suffix.vertices[D1.cutIndex + 1] ∩
          segment ℝ suffix.vertices[ns] suffix.vertices[ns + 1] :=
      ⟨D1.cut_mem_segment,
        openSegment_subset_segment ℝ _ _ hh_last_suffix_segment⟩
    by_cases hadj : ns = D1.cutIndex + 1
    · rw [hinter, if_pos hadj] at hhinter
      have heq : h' = suffix.vertices[ns] := by simpa using hhinter
      have hleftOpen : suffix.vertices[ns] ∈
          openSegment ℝ suffix.vertices[ns] suffix.vertices[ns + 1] := by
        simpa [heq] using hh_last_suffix_segment
      have hverticesEq := left_mem_openSegment_iff.mp hleftOpen
      have hidxEq : ns = ns + 1 :=
        suffix.simple_vertices.getElem_inj_iff.mp hverticesEq
      omega
    · rw [hinter, if_neg hadj] at hhinter
      exact hhinter
  have hfinal_carrier : final'.carrier = segment ℝ h' terminalGate := by
    change D1.suffixArc.carrier = _
    rw [D1.suffix_carrier_region]
    ext z
    constructor
    · rintro (hz | ⟨i, hi, hlt, hz⟩)
      · simpa [hD1cut, hsuffix_last] using hz
      · exfalso
        dsimp [ns] at hD1cut
        omega
    · intro hz
      exact Or.inl (by simpa [hD1cut, hsuffix_last] using hz)
  have hlastGate_R : lastGate' ∈ R.carrier := by
    change lastGate' ∈ D1.prefixArc.carrier
    rw [D1.prefix_carrier_region]
    apply Or.inr
    have hseg : f ta ∈ segment ℝ (f s0) (f tb) :=
      lineMap_mem_segment_interval A terminalGate s0 ta tb
        (hs0_le_tq.trans_lt htb.1) (hs0_le_tq.trans hta.1.le) hta.2.le
    simpa [hD1cut, hsuffix_penultimate, lastGate', h'] using hseg
  have hlastGate_R_interior : lastGate' ∈ R.relativeInterior := by
    rw [R.relativeInterior_eq]
    refine ⟨hlastGate_R, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun heq => hq_ne_lastGate
        (heq.trans (D1.prefix_source.trans hsuffix_source)).symm,
      fun heq => hlastGate_ne_h (heq.trans D1.prefix_target)⟩
  obtain ⟨D2⟩ := PolygonalArcPointCutDataExists R lastGate'
    hlastGate_R_interior
  let Cprev' := D2.prefixArc
  let approach' := D2.suffixArc
  have hR_subset_suffix : R.carrier ⊆ suffix.carrier :=
    D1.prefix_carrier_subset
  have hfinal_subset_suffix : final'.carrier ⊆ suffix.carrier :=
    D1.suffix_carrier_subset
  have hCprev_subset_R : Cprev'.carrier ⊆ R.carrier :=
    D2.prefix_carrier_subset
  have happ_subset_R : approach'.carrier ⊆ R.carrier :=
    D2.suffix_carrier_subset
  have hCprev_subset_chain : Cprev'.carrier ⊆ chain.carrier :=
    hCprev_subset_R.trans (hR_subset_suffix.trans hsuffix_subset)
  have happ_subset_chain : approach'.carrier ⊆ chain.carrier :=
    happ_subset_R.trans (hR_subset_suffix.trans hsuffix_subset)
  have hfinal_subset_chain : final'.carrier ⊆ chain.carrier :=
    hfinal_subset_suffix.trans hsuffix_subset
  have hq_Cprev : q ∈ Cprev'.carrier := by
    have hs : Cprev'.source = q := by
      exact D2.prefix_source.trans (D1.prefix_source.trans hsuffix_source)
    rw [← hs]
    exact arc_source_mem Cprev'
  have hlastGate_approach : lastGate' ∈ approach'.carrier := by
    rw [← D2.suffix_source]
    exact arc_source_mem approach'
  have hh_approach : h' ∈ approach'.carrier := by
    have ht : approach'.target = h' :=
      D2.suffix_target.trans D1.prefix_target
    rw [← ht]
    exact arc_target_mem approach'
  have hh_final : h' ∈ final'.carrier := by
    rw [← D1.suffix_source]
    exact arc_source_mem final'
  have hterminal_final : terminalGate ∈ final'.carrier := by
    have ht : final'.target = terminalGate :=
      D1.suffix_target.trans hsuffix_target
    rw [← ht]
    exact arc_target_mem final'
  have hq_not_approach : q ∉ approach'.carrier := by
    intro hqapp
    have hboth : q ∈ Cprev'.carrier ∩ approach'.carrier :=
      ⟨hq_Cprev, hqapp⟩
    have heq : q = lastGate' := by
      have : q ∈ ({lastGate'} :
          Set (EuclideanSpace ℝ (Fin 2))) := D2.carrier_intersection ▸ hboth
      simpa using this
    exact hq_ne_lastGate heq
  have hq_R : q ∈ R.carrier := hCprev_subset_R hq_Cprev
  have hq_not_final : q ∉ final'.carrier := by
    intro hqfinal
    have hboth : q ∈ R.carrier ∩ final'.carrier := ⟨hq_R, hqfinal⟩
    have heq : q = h' := by
      have : q ∈ ({h'} : Set (EuclideanSpace ℝ (Fin 2))) :=
        D1.carrier_intersection ▸ hboth
      simpa using this
    exact hq_ne_h heq
  have hh_not_Cprev : h' ∉ Cprev'.carrier := by
    intro hhC
    have hboth : h' ∈ Cprev'.carrier ∩ approach'.carrier :=
      ⟨hhC, hh_approach⟩
    have heq : h' = lastGate' := by
      have : h' ∈ ({lastGate'} :
          Set (EuclideanSpace ℝ (Fin 2))) := D2.carrier_intersection ▸ hboth
      simpa using this
    exact hlastGate_ne_h heq.symm
  have hterminal_not_R : terminalGate ∉ R.carrier := by
    intro hgR
    have hboth : terminalGate ∈ R.carrier ∩ final'.carrier :=
      ⟨hgR, hterminal_final⟩
    have heq : terminalGate = h' := by
      have : terminalGate ∈ ({h'} :
          Set (EuclideanSpace ℝ (Fin 2))) := D1.carrier_intersection ▸ hboth
      simpa using this
    exact hh_ne_terminal heq.symm
  have hchain_before_terminal :
      ∀ z, z ∈ chain.carrier → z ≠ terminalGate →
        z ∈ SelectedSide ∩ Vin := by
    intro z hz hzGate
    rw [hchain_carrier] at hz
    rcases hz with (hz | hz) | hz
    · exact hpredecessor_side hz
    · exact happ_side hz
    · by_cases hzh : z = h
      · apply happ_side
        have htargetMem := arc_target_mem approach
        simpa [happ_target, hzh] using htargetMem
      · have hzseg : z ∈ segment ℝ h terminalGate := by
          rw [← hterminal_carrier]
          exact hz
        have hzopen : z ∈ openSegment ℝ h terminalGate :=
          mem_openSegment_of_ne_left_right (Ne.symm hzh) (Ne.symm hzGate) hzseg
        have hzVin := hopen_terminal hzopen
        exact ⟨hVin_side hzVin, hzVin⟩
  have hCprev_side : Cprev'.carrier ⊆ SelectedSide ∩ Vin := by
    intro z hz
    apply hchain_before_terminal z (hCprev_subset_chain hz)
    intro hzGate
    exact hterminal_not_R (hzGate ▸ hCprev_subset_R hz)
  have happ_prime_side : approach'.carrier ⊆ SelectedSide ∩ Vin := by
    intro z hz
    apply hchain_before_terminal z (happ_subset_chain hz)
    intro hzGate
    exact hterminal_not_R (hzGate ▸ happ_subset_R hz)
  have hfinal_Vin : final'.carrier ⊆
      Vin ∪ ({terminalGate} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hfinal_carrier]
    intro z hz
    apply hterminal_Vin
    have hzterm := hlast_segment_terminal
      (openSegment_subset_segment ℝ A terminalGate hh_open)
    rw [hterminal_carrier] at hzterm
    have hhSeg : h' ∈ segment ℝ h terminalGate := hzterm
    exact (convex_segment h terminalGate).segment_subset hhSeg
      (right_mem_segment ℝ h terminalGate) hz
  have hfinal_interior_Vin : final'.relativeInterior ⊆ Vin := by
    intro z hz
    have hzOwn := hz
    rw [final'.relativeInterior_eq] at hzOwn
    have hzUnion := hfinal_Vin hzOwn.1
    rcases hzUnion with hzVin | hzGate
    · exact hzVin
    · have heq : z = terminalGate := by simpa using hzGate
      have hnot := hzOwn.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
      exact False.elim (hnot.2 (by
        have ht : final'.target = terminalGate :=
          D1.suffix_target.trans hsuffix_target
        simpa [heq] using ht.symm))
  have hPq_Cprev : Pq.carrier ∩ Cprev'.carrier =
      ({q} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext z
    constructor
    · rintro ⟨hzPq, hzC⟩
      have hzChain := hCprev_subset_chain hzC
      have hzSingleton : z ∈ ({q} :
          Set (EuclideanSpace ℝ (Fin 2))) := hPq_chain ▸ ⟨hzPq, hzChain⟩
      exact hzSingleton
    · intro hz
      have heq : z = q := by simpa using hz
      subst z
      refine ⟨?_, hq_Cprev⟩
      rw [← hPq_target]
      exact arc_target_mem Pq
  have hPq_approach : Disjoint Pq.carrier approach'.carrier := by
    rw [Set.disjoint_left]
    intro z hzPq hzapp
    have hzChain := happ_subset_chain hzapp
    have hzSingleton : z ∈ ({q} :
        Set (EuclideanSpace ℝ (Fin 2))) := hPq_chain ▸ ⟨hzPq, hzChain⟩
    have heq : z = q := by simpa using hzSingleton
    exact hq_not_approach (heq ▸ hzapp)
  have hPq_final : Disjoint Pq.carrier final'.carrier := by
    rw [Set.disjoint_left]
    intro z hzPq hzfinal
    have hzChain := hfinal_subset_chain hzfinal
    have hzSingleton : z ∈ ({q} :
        Set (EuclideanSpace ℝ (Fin 2))) := hPq_chain ▸ ⟨hzPq, hzChain⟩
    have heq : z = q := by simpa using hzSingleton
    exact hq_not_final (heq ▸ hzfinal)
  have hCprev_approach : Cprev'.carrier ∩ approach'.carrier =
      ({lastGate'} : Set (EuclideanSpace ℝ (Fin 2))) := by
    exact D2.carrier_intersection
  have happ_final : approach'.carrier ∩ final'.carrier =
      ({h'} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext z
    constructor
    · rintro ⟨hzapp, hzfinal⟩
      have hzR := happ_subset_R hzapp
      have hzSingleton : z ∈ ({h'} :
          Set (EuclideanSpace ℝ (Fin 2))) :=
        D1.carrier_intersection ▸ ⟨hzR, hzfinal⟩
      exact hzSingleton
    · intro hz
      have heq : z = h' := by simpa using hz
      subst z
      exact ⟨hh_approach, hh_final⟩
  have hCprev_final : Disjoint Cprev'.carrier final'.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzfinal
    have hzR := hCprev_subset_R hzC
    have hzSingleton : z ∈ ({h'} :
        Set (EuclideanSpace ℝ (Fin 2))) :=
      D1.carrier_intersection ▸ ⟨hzR, hzfinal⟩
    have heq : z = h' := by simpa using hzSingleton
    exact hh_not_Cprev (heq ▸ hzC)
  have hsuffix_decomposition : suffix.carrier =
      Cprev'.carrier ∪ approach'.carrier ∪ final'.carrier := by
    calc
      suffix.carrier = R.carrier ∪ final'.carrier := D1.carrier_decomposition
      _ = (Cprev'.carrier ∪ approach'.carrier) ∪ final'.carrier := by
        rw [D2.carrier_decomposition]
      _ = Cprev'.carrier ∪ approach'.carrier ∪ final'.carrier := rfl
  refine ⟨lastGate', h', suffix, Cprev', approach', final',
    hlastGate_clean, hh_clean, hsuffix_source, hsuffix_target,
    hsuffix_decomposition, hsuffix_alternative,
    D2.prefix_source.trans (D1.prefix_source.trans hsuffix_source),
    D2.prefix_target, D2.suffix_source,
    D2.suffix_target.trans D1.prefix_target,
    D1.suffix_source, D1.suffix_target.trans hsuffix_target,
    hCprev_side, happ_prime_side, hfinal_carrier, hfinal_Vin,
    hfinal_interior_Vin, hCprev_subset_chain, happ_subset_chain,
    hfinal_subset_chain, hPq_Cprev, hPq_approach, hPq_final,
    hCprev_approach, happ_final, hCprev_final, ?_⟩
  intro piece hpiece z i hi hzChain hzPiece hzAvoid
  have hpieceCases :
      piece = Cprev' ∨ piece = approach' ∨ piece = final' := by
    simpa using hpiece
  have hzNe : z ≠ q ∧ z ≠ lastGate' ∧ z ≠ h' ∧
      z ≠ terminalGate := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hzAvoid
  have hzSuffix : z ∈ suffix.carrier := by
    rcases hpieceCases with rfl | rfl | rfl
    · exact hR_subset_suffix (hCprev_subset_R hzPiece)
    · exact hR_subset_suffix (happ_subset_R hzPiece)
    · exact hfinal_subset_suffix hzPiece
  obtain ⟨j0, hj0, hzSuffixOpen, c0, hc0, hdir0⟩ :=
    hsuffix_transfer z i hi hzChain hzSuffix hzNe.1
  rcases hpieceCases with rfl | rfl | rfl
  · have hzR : z ∈ R.carrier := hCprev_subset_R hzPiece
    obtain ⟨j1, hj1, hzROpen, c1, hc1, hdir1⟩ :=
      D1.prefix_segment_transfer z j0 hj0 hzSuffixOpen hzR hzNe.2.2.1
    obtain ⟨j2, hj2, hzOpen, c2, hc2, hdir2⟩ :=
      D2.prefix_segment_transfer z j1 hj1 hzROpen hzPiece hzNe.2.1
    refine ⟨j2, hj2, hzOpen, c2 * c1 * c0,
      mul_ne_zero (mul_ne_zero hc2 hc1) hc0, ?_⟩
    rw [hdir2, hdir1, hdir0, smul_smul, smul_smul]
  · have hzR : z ∈ R.carrier := happ_subset_R hzPiece
    obtain ⟨j1, hj1, hzROpen, c1, hc1, hdir1⟩ :=
      D1.prefix_segment_transfer z j0 hj0 hzSuffixOpen hzR hzNe.2.2.1
    obtain ⟨j2, hj2, hzOpen, c2, hc2, hdir2⟩ :=
      D2.suffix_segment_transfer z j1 hj1 hzROpen hzPiece hzNe.2.1
    refine ⟨j2, hj2, hzOpen, c2 * c1 * c0,
      mul_ne_zero (mul_ne_zero hc2 hc1) hc0, ?_⟩
    rw [hdir2, hdir1, hdir0, smul_smul, smul_smul]
  · obtain ⟨j1, hj1, hzOpen, c1, hc1, hdir1⟩ :=
      D1.suffix_segment_transfer z j0 hj0 hzSuffixOpen hzPiece hzNe.2.2.1
    refine ⟨j1, hj1, hzOpen, c1 * c0, mul_ne_zero hc1 hc0, ?_⟩
    rw [hdir1, hdir0, smul_smul]
