import Util.IncidenceGeometry.PolygonalArcPointCutDataExists
import Util.IncidenceGeometry.PolygonalArcFiniteInteriorFirstPoint
import Util.IncidenceGeometry.PolygonalArcOpenSegmentSubsetRelativeInterior
import Mathlib.Tactic

open Classical
noncomputable section

lemma PolygonalArcFiniteFirstContactPrefix
    (P T : PolygonalArc)
    (X : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set.Finite (P.carrier ∩ T.carrier) →
      P.target ∈ T.carrier →
        P.source ∉ T.carrier →
          ∃ q : EuclideanSpace ℝ (Fin 2),
              ∃ Pq : PolygonalArc,
                q ∈ P.carrier ∩ T.carrier ∧
                  q ≠ P.source ∧
                    Pq.source = P.source ∧
                      Pq.target = q ∧
                        Pq.carrier ⊆ P.carrier ∧
                          Pq.relativeInterior ⊆ P.relativeInterior ∧
                            Pq.carrier ∩ T.carrier =
                              ({q} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                              Pq.relativeInterior ∩ T.carrier =
                                (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                ((q = P.target ∧ Pq = P) ∨
                                  ∃ D : PolygonalArcPointCutData P q,
                                    Pq = D.prefixArc) ∧
                                  ∃ hfirstq : 0 + 1 < Pq.vertices.length,
                                    segment ℝ (Pq.vertices[0]'(by omega))
                                        (Pq.vertices[1]'(by omega)) ⊆
                                      segment ℝ
                                          (P.vertices[0]'(by
                                            have := P.length_ge_two
                                            omega))
                                          (P.vertices[1]'(by
                                            have := P.length_ge_two
                                            omega)) ∧
                                      openSegment ℝ (Pq.vertices[0]'(by omega))
                                          (Pq.vertices[1]'(by omega)) ⊆
                                        openSegment ℝ
                                          (P.vertices[0]'(by
                                            have := P.length_ge_two
                                            omega))
                                          (P.vertices[1]'(by
                                            have := P.length_ge_two
                                            omega)) ∧
                                      (∀ z i (hi : i + 1 < P.vertices.length),
                                        z ∈ openSegment ℝ
                                            P.vertices[i] P.vertices[i + 1] →
                                          z ∈ Pq.carrier →
                                            z ≠ q →
                                              ∃ j : ℕ,
                                                ∃ hj : j + 1 <
                                                    Pq.vertices.length,
                                                  z ∈ openSegment ℝ
                                                      Pq.vertices[j]
                                                      Pq.vertices[j + 1] ∧
                                                    ∃ c : ℝ, c ≠ 0 ∧
                                                      Pq.vertices[j + 1] -
                                                          Pq.vertices[j] =
                                                        c •
                                                          (P.vertices[i + 1] -
                                                            P.vertices[i])) ∧
                                        ∃ cut : EuclideanSpace ℝ (Fin 2),
                                          ∃ firstPiece remainder : PolygonalArc,
                                            cut ∉ X ∧
                                              cut ∈ Pq.relativeInterior ∧
                                              firstPiece.source = P.source ∧
                                                firstPiece.target = cut ∧
                                                  remainder.source = cut ∧
                                                    remainder.target = q ∧
                                                      Pq.carrier =
                                                        firstPiece.carrier ∪
                                                          remainder.carrier ∧
                                                        firstPiece.carrier ∩
                                                            remainder.carrier =
                                                          ({cut} :
                                                            Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                          Disjoint firstPiece.carrier
                                                            T.carrier ∧
                                                            remainder.carrier ∩
                                                                T.carrier =
                                                              ({q} :
                                                                Set (EuclideanSpace ℝ (Fin 2))) ∧
                                                              firstPiece.carrier ⊆
                                                                segment ℝ
                                                                  (P.vertices[0]'(by
                                                                    have := P.length_ge_two
                                                                    omega))
                                                                  (P.vertices[1]'(by
                                                                    have := P.length_ge_two
                                                                    omega)) ∧
                                                              firstPiece.relativeInterior ⊆
                                                                  openSegment ℝ
                                                                    (P.vertices[0]'(by
                                                                      have := P.length_ge_two
                                                                      omega))
                                                                    (P.vertices[1]'(by
                                                                      have := P.length_ge_two
                                                                      omega)) ∧
                                                                  firstPiece.relativeInterior ⊆
                                                                    Pq.relativeInterior ∧
                                                                    remainder.relativeInterior ⊆
                                                                      Pq.relativeInterior ∧
                                                                  ∀ piece : PolygonalArc,
                                                                    piece ∈
                                                                        [firstPiece,
                                                                          remainder] →
                                                                      ∀ z i
                                                                        (hi : i + 1 <
                                                                          P.vertices.length),
                                                                        z ∈ openSegment ℝ
                                                                            P.vertices[i]
                                                                            P.vertices[i + 1] →
                                                                          z ∈ piece.carrier →
                                                                            z ≠ cut →
                                                                              z ≠ q →
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
                                                                                          (P.vertices[i + 1] -
                                                                                            P.vertices[i]) := by
  intro hfinite htargetT hsourceT
  let E := EuclideanSpace ℝ (Fin 2)
  have arc_source_mem (Q : PolygonalArc) : Q.source ∈ Q.carrier := by
    rw [Q.carrier_eq]
    have hlen := Q.length_ge_two
    have hzero : Q.vertices[0]'(by omega) = Q.source := by
      have hhead := Q.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    exact ⟨0, by omega, by
      rw [hzero]
      exact left_mem_segment ℝ Q.source Q.vertices[1]⟩
  have arc_target_mem (Q : PolygonalArc) : Q.target ∈ Q.carrier := by
    rw [Q.carrier_eq]
    have hlen := Q.length_ge_two
    let i := Q.vertices.length - 2
    have hi : i + 1 < Q.vertices.length := by
      dsimp [i]
      omega
    refine ⟨i, hi, ?_⟩
    have hlast : Q.vertices[i + 1] = Q.target := by
      have hlast' := Q.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlast'
      have hidx : Q.vertices.length - 1 < Q.vertices.length := by omega
      rw [List.getElem?_eq_getElem hidx] at hlast'
      have hiEq : i + 1 = Q.vertices.length - 1 := by
        dsimp [i]
        omega
      simpa [hiEq] using Option.some.inj hlast'
    rw [hlast]
    exact right_mem_segment ℝ Q.vertices[i] Q.target
  have arc_first_vertex (Q : PolygonalArc) :
      Q.vertices[0]'(by
        have := Q.length_ge_two
        omega) = Q.source := by
    have hlen := Q.length_ge_two
    have hhead := Q.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem (by omega)] at hhead
    exact Option.some.inj hhead
  have arc_last_vertex (Q : PolygonalArc) :
      Q.vertices[Q.vertices.length - 1]'(by
        have := Q.length_ge_two
        omega) = Q.target := by
    have hlast := Q.target_eq_last
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getElem?_eq_getElem (by
      have := Q.length_ge_two
      omega)] at hlast
    exact Option.some.inj hlast
  have getElem_eq {α : Type} (l : List α) (i j : ℕ)
      (hi : i < l.length) (hj : j < l.length) (hij : i = j) :
      l[i]'hi = l[j]'hj := by
    subst j
    rfl
  have open_of_segment_subset :
      ∀ {u v s t x : E}, u ≠ v →
        segment ℝ u v ⊆ segment ℝ s t →
          x ∈ openSegment ℝ u v → x ∈ openSegment ℝ s t := by
    intro u v s t x huv hsub hx
    rw [openSegment_eq_image_lineMap] at hx ⊢
    rcases hx with ⟨r, hr, rfl⟩
    have hu : u ∈ segment ℝ s t := hsub (left_mem_segment ℝ u v)
    have hv : v ∈ segment ℝ s t := hsub (right_mem_segment ℝ u v)
    rw [segment_eq_image_lineMap] at hu hv
    rcases hu with ⟨a, ha, hu_eq⟩
    rcases hv with ⟨b, hb, hv_eq⟩
    have hab : a ≠ b := by
      intro hab
      apply huv
      calc
        u = AffineMap.lineMap s t a := hu_eq.symm
        _ = AffineMap.lineMap s t b := by rw [hab]
        _ = v := hv_eq
    refine ⟨(1 - r) * a + r * b, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hab with hablt | hblt
      · constructor <;> nlinarith [hr.1, hr.2, ha.1, ha.2, hb.1, hb.2, hablt]
      · constructor <;> nlinarith [hr.1, hr.2, ha.1, ha.2, hb.1, hb.2, hblt]
    · rw [← hu_eq, ← hv_eq]
      simp only [AffineMap.lineMap_apply_module]
      module
  let contacts : Finset E := hfinite.toFinset.erase P.target
  have hcontact_mem (z : E) :
      z ∈ contacts ↔ z ∈ P.carrier ∩ T.carrier ∧ z ≠ P.target := by
    simp only [contacts, Finset.mem_erase, Set.Finite.mem_toFinset hfinite,
      Set.mem_inter_iff]
    aesop
  have hcontact_relative (z : E) (hz : z ∈ contacts) :
      z ∈ P.relativeInterior := by
    rw [P.relativeInterior_eq]
    have hz' := (hcontact_mem z).1 hz
    refine ⟨hz'.1.1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hzs => hsourceT (hzs ▸ hz'.1.2), hz'.2⟩
  have hfirstContact :
      ∃ q : E, ∃ Pq : PolygonalArc,
        q ∈ P.carrier ∩ T.carrier ∧
          q ≠ P.source ∧
            Pq.source = P.source ∧
              Pq.target = q ∧
                Pq.carrier ⊆ P.carrier ∧
                  Pq.relativeInterior ⊆ P.relativeInterior ∧
                    Pq.carrier ∩ T.carrier = ({q} : Set E) ∧
                      Pq.relativeInterior ∩ T.carrier = (∅ : Set E) ∧
                        ((q = P.target ∧ Pq = P) ∨
                          ∃ D : PolygonalArcPointCutData P q,
                            Pq = D.prefixArc) ∧
                          ∃ hfirstq : 0 + 1 < Pq.vertices.length,
                            segment ℝ (Pq.vertices[0]'(by omega))
                                (Pq.vertices[1]'(by omega)) ⊆
                              segment ℝ (P.vertices[0]'(by
                                  have := P.length_ge_two
                                  omega))
                                (P.vertices[1]'(by
                                  have := P.length_ge_two
                                  omega)) ∧
                              openSegment ℝ (Pq.vertices[0]'(by omega))
                                  (Pq.vertices[1]'(by omega)) ⊆
                                openSegment ℝ (P.vertices[0]'(by
                                    have := P.length_ge_two
                                    omega))
                                  (P.vertices[1]'(by
                                    have := P.length_ge_two
                                    omega)) ∧
                                ∀ z i (hi : i + 1 < P.vertices.length),
                                  z ∈ openSegment ℝ P.vertices[i] P.vertices[i + 1] →
                                    z ∈ Pq.carrier → z ≠ q →
                                      ∃ j : ℕ, ∃ hj : j + 1 < Pq.vertices.length,
                                        z ∈ openSegment ℝ Pq.vertices[j]
                                            Pq.vertices[j + 1] ∧
                                          ∃ c : ℝ, c ≠ 0 ∧
                                            Pq.vertices[j + 1] - Pq.vertices[j] =
                                              c • (P.vertices[i + 1] - P.vertices[i]) := by
    by_cases hempty : contacts = ∅
    · have hinter : P.carrier ∩ T.carrier = ({P.target} : Set E) := by
        ext z
        constructor
        · intro hz
          by_contra hztarget
          have hzcontacts : z ∈ contacts := (hcontact_mem z).2 ⟨hz, hztarget⟩
          simpa [hempty] using hzcontacts
        · intro hz
          have hzEq : z = P.target := by simpa using hz
          subst z
          exact ⟨arc_target_mem P, htargetT⟩
      have hinterior : P.relativeInterior ∩ T.carrier = (∅ : Set E) := by
        rw [P.relativeInterior_eq]
        ext z
        constructor
        · rintro ⟨⟨hzP, hzends⟩, hzT⟩
          have hzEq : z = P.target := by
            have : z ∈ ({P.target} : Set E) := hinter ▸ ⟨hzP, hzT⟩
            simpa using this
          exact False.elim (hzends (by simp [hzEq]))
        · exact False.elim
      have htargetNeSource : P.target ≠ P.source := by
        intro hEq
        exact hsourceT (hEq ▸ htargetT)
      refine ⟨P.target, P, ⟨arc_target_mem P, htargetT⟩, htargetNeSource, rfl, rfl,
        Set.Subset.rfl, Set.Subset.rfl, hinter, hinterior, Or.inl ⟨rfl, rfl⟩,
        P.length_ge_two, Set.Subset.rfl, Set.Subset.rfl, ?_⟩
      intro z i hi hzopen hzP _hzq
      exact ⟨i, hi, hzopen, 1, one_ne_zero, by simp⟩
    · have hnonempty : contacts.Nonempty := Finset.nonempty_iff_ne_empty.2 hempty
      obtain ⟨q, j, hj, hqcontacts, hqseg, hminimal⟩ :=
        PolygonalArcFiniteInteriorFirstPoint P contacts hnonempty hcontact_relative
      have hqrelative : q ∈ P.relativeInterior := hcontact_relative q hqcontacts
      obtain ⟨D⟩ := PolygonalArcPointCutDataExists P q hqrelative
      have hDcutLt : D.cutIndex < P.vertices.length :=
        Nat.lt_of_succ_lt D.cutIndex_valid
      have hDcutSucc : D.cutIndex + 1 < P.vertices.length :=
        D.cutIndex_valid
      have hqcontact : q ∈ P.carrier ∩ T.carrier :=
        (hcontact_mem q).1 hqcontacts |>.1
      have hqNeTarget : q ≠ P.target := (hcontact_mem q).1 hqcontacts |>.2
      have hqNeSource : q ≠ P.source := by
        intro hEq
        exact hsourceT (hEq ▸ hqcontact.2)
      have hcutNotLeft : q ≠ P.vertices[D.cutIndex] := by
        intro hleft
        have hnodup : (P.vertices.take (D.cutIndex + 1) ++ [q]).Nodup := by
          rw [← D.prefix_vertices_exact]
          exact D.prefixArc.simple_vertices
        rw [List.nodup_append] at hnodup
        have hmemTake : P.vertices[D.cutIndex] ∈
            P.vertices.take (D.cutIndex + 1) := by
          have hbound : D.cutIndex < (P.vertices.take (D.cutIndex + 1)).length := by
            simp [List.length_take]
            omega
          have hmem := List.getElem_mem hbound
          simpa only [List.getElem_take] using hmem
        exact hnodup.2.2 P.vertices[D.cutIndex] hmemTake q (by simp) hleft.symm
      have hcutLe : D.cutIndex ≤ j := by
        by_contra hnot
        have hjcut : j < D.cutIndex := by omega
        have hinterRaw := P.segment_intersections hj D.cutIndex_valid hjcut
        have hqinter : q ∈
            segment ℝ P.vertices[j] P.vertices[j + 1] ∩
              segment ℝ P.vertices[D.cutIndex] P.vertices[D.cutIndex + 1] :=
          ⟨hqseg, D.cut_mem_segment⟩
        by_cases hadj : D.cutIndex = j + 1
        · rw [hinterRaw, if_pos hadj] at hqinter
          have hqleft : q = P.vertices[D.cutIndex] := by simpa [hadj] using hqinter
          exact hcutNotLeft hqleft
        · rw [hinterRaw, if_neg hadj] at hqinter
          exact hqinter
      have hprefixMinimal :
          D.prefixArc.carrier ∩ T.carrier = ({q} : Set E) := by
        ext z
        constructor
        · rintro ⟨hzPrefix, hzT⟩
          have hzP : z ∈ P.carrier := D.prefix_carrier_subset hzPrefix
          have hzNeTarget : z ≠ P.target := by
            intro hzTarget
            have htargetSuffix : P.target ∈ D.suffixArc.carrier := by
              rw [← D.suffix_target]
              exact arc_target_mem D.suffixArc
            have hzCut : z = q := by
              have hzBoth : z ∈ D.prefixArc.carrier ∩ D.suffixArc.carrier :=
                ⟨hzPrefix, hzTarget ▸ htargetSuffix⟩
              have : z ∈ ({q} : Set E) := D.carrier_intersection ▸ hzBoth
              simpa using this
            exact hqNeTarget (hzCut.symm.trans hzTarget)
          have hzContacts : z ∈ contacts :=
            (hcontact_mem z).2 ⟨⟨hzP, hzT⟩, hzNeTarget⟩
          have hzEarly : z ∈
              ArcCrossingEarlierPrefix P j hj ∪ segment ℝ P.vertices[j] q := by
            rw [D.prefix_carrier_region] at hzPrefix
            rcases hzPrefix with ⟨i, hi, hiCut, hzseg⟩ | hzseg
            · left
              rw [ArcCrossingEarlierPrefix]
              exact Set.mem_iUnion.2 ⟨⟨i, hiCut.trans_le hcutLe⟩, hzseg⟩
            · by_cases hcutEq : D.cutIndex = j
              · right
                simpa [hcutEq] using hzseg
              · have hcutLt : D.cutIndex < j := lt_of_le_of_ne hcutLe hcutEq
                left
                rw [ArcCrossingEarlierPrefix]
                exact Set.mem_iUnion.2 ⟨⟨D.cutIndex, hcutLt⟩,
                  (convex_segment P.vertices[D.cutIndex]
                    P.vertices[D.cutIndex + 1]).segment_subset
                      (left_mem_segment ℝ _ _)
                      D.cut_mem_segment hzseg⟩
          exact Set.mem_singleton_iff.2 (hminimal z hzContacts hzEarly)
        · intro hz
          have hzEq : z = q := by simpa using hz
          subst z
          exact ⟨by
            rw [D.prefix_carrier_region]
            exact Or.inr (right_mem_segment ℝ P.vertices[D.cutIndex] q), hqcontact.2⟩
      have hprefixInterior :
          D.prefixArc.relativeInterior ⊆ P.relativeInterior := by
        intro z hz
        rw [D.prefixArc.relativeInterior_eq] at hz
        rw [P.relativeInterior_eq]
        refine ⟨D.prefix_carrier_subset hz.1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        constructor
        · intro hzSource
          have hnotOwn := hz.2
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotOwn
          have : z ≠ D.prefixArc.source := hnotOwn.1
          exact this (by simpa [D.prefix_source] using hzSource)
        · intro hzTarget
          have htargetSuffix : P.target ∈ D.suffixArc.carrier := by
            rw [← D.suffix_target]
            exact arc_target_mem D.suffixArc
          have hzCut : z = q := by
            have hzBoth : z ∈ D.prefixArc.carrier ∩ D.suffixArc.carrier :=
              ⟨hz.1, hzTarget ▸ htargetSuffix⟩
            have : z ∈ ({q} : Set E) := D.carrier_intersection ▸ hzBoth
            simpa using this
          exact hqNeTarget (hzCut.symm.trans hzTarget)
      have hprefixInteriorT :
          D.prefixArc.relativeInterior ∩ T.carrier = (∅ : Set E) := by
        ext z
        constructor
        · rintro ⟨hzInterior, hzT⟩
          have hzCarrier : z ∈ D.prefixArc.carrier := by
            rw [D.prefixArc.relativeInterior_eq] at hzInterior
            exact hzInterior.1
          have hzEq : z = q := by
            have : z ∈ ({q} : Set E) := hprefixMinimal ▸ ⟨hzCarrier, hzT⟩
            simpa using this
          have hzNotTarget : z ≠ D.prefixArc.target := by
            rw [D.prefixArc.relativeInterior_eq] at hzInterior
            have hnotOwn := hzInterior.2
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotOwn
            exact hnotOwn.2
          exact False.elim (hzNotTarget (by simpa [D.prefix_target, hzEq]))
        · exact False.elim
      have hfirst : 0 + 1 < D.prefixArc.vertices.length := by
        rw [D.prefix_vertices_exact]
        simp [List.length_take]
        omega
      have hfirstClosed :
          segment ℝ D.prefixArc.vertices[0] D.prefixArc.vertices[1] ⊆
            segment ℝ P.vertices[0] P.vertices[1] := by
        by_cases hqFirst : q ∈ segment ℝ P.vertices[0] P.vertices[1]
        · have hcutZero : D.cutIndex = 0 := by
            by_contra hne
            have hpos : 0 < D.cutIndex := Nat.pos_of_ne_zero hne
            have hinterRaw := P.segment_intersections (i := 0)
              (j := D.cutIndex) (by omega) D.cutIndex_valid hpos
            have hqinter : q ∈
                segment ℝ P.vertices[0] P.vertices[1] ∩
                  segment ℝ P.vertices[D.cutIndex] P.vertices[D.cutIndex + 1] :=
              ⟨hqFirst, D.cut_mem_segment⟩
            by_cases hone : D.cutIndex = 1
            · rw [hinterRaw, if_pos (by omega : D.cutIndex = 0 + 1)] at hqinter
              exact hcutNotLeft (by simpa [hone] using hqinter)
            · rw [hinterRaw, if_neg (by omega : D.cutIndex ≠ 0 + 1)] at hqinter
              exact hqinter
          have hverts := D.prefix_vertices_exact
          have hprefixLen : D.prefixArc.vertices.length = 2 := by
            have hPlen := P.length_ge_two
            rw [D.prefix_vertices_exact]
            simp [hcutZero]
            omega
          have hzero : D.prefixArc.vertices[0] = P.vertices[0] := by
            calc
              D.prefixArc.vertices[0] = D.prefixArc.source := arc_first_vertex _
              _ = P.source := D.prefix_source
              _ = P.vertices[0] := (arc_first_vertex P).symm
          have hone : D.prefixArc.vertices[1] = q := by
            calc
              D.prefixArc.vertices[1] =
                  D.prefixArc.vertices[D.prefixArc.vertices.length - 1] :=
                getElem_eq _ _ _ (by omega) (by omega) (by omega)
              _ = D.prefixArc.target := arc_last_vertex _
              _ = q := D.prefix_target
          simpa [hzero, hone] using
            (convex_segment P.vertices[0] P.vertices[1]).segment_subset
              (left_mem_segment ℝ _ _) hqFirst
        · obtain ⟨_, hzero, hone⟩ := D.protected_first_vertices (by omega) hqFirst
          simpa [hzero, hone]
      have hfirstOpen :
          openSegment ℝ D.prefixArc.vertices[0] D.prefixArc.vertices[1] ⊆
            openSegment ℝ P.vertices[0] P.vertices[1] := by
        have hne : D.prefixArc.vertices[0] ≠ D.prefixArc.vertices[1] := by
          intro heq
          have : (0 : ℕ) = 1 := D.prefixArc.simple_vertices.getElem_inj_iff.1 heq
          omega
        exact fun _ hz => open_of_segment_subset hne hfirstClosed hz
      refine ⟨q, D.prefixArc, hqcontact, hqNeSource, D.prefix_source,
        D.prefix_target, D.prefix_carrier_subset, hprefixInterior,
        hprefixMinimal, hprefixInteriorT, Or.inr ⟨D, rfl⟩, hfirst,
        hfirstClosed, hfirstOpen, D.prefix_segment_transfer⟩
  rcases hfirstContact with
    ⟨q, Pq, hqContact, hqNeSource, hPqSource, hPqTarget,
      hPqCarrier, hPqInterior, hPqMeetsT, hPqInteriorT,
      hPqAlternative, hfirstq, hfirstClosed, hfirstOpen, hPqTransfer⟩
  refine ⟨q, Pq, hqContact, hqNeSource, hPqSource, hPqTarget,
    hPqCarrier, hPqInterior, hPqMeetsT, hPqInteriorT,
    hPqAlternative, hfirstq, hfirstClosed, hfirstOpen, hPqTransfer, ?_⟩
  have hfirstNe : Pq.vertices[0] ≠ Pq.vertices[1] := by
    intro heq
    have : (0 : ℕ) = 1 := Pq.simple_vertices.getElem_inj_iff.1 heq
    omega
  let f : ℝ → E := fun r => AffineMap.lineMap Pq.vertices[0] Pq.vertices[1] r
  let bad : Finset ℝ := X.preimage f
    (AffineMap.lineMap_injective ℝ hfirstNe).injOn
  obtain ⟨r, hr, hrbad⟩ :=
    (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finset bad
  let cut : E := f r
  have hcutOpen : cut ∈ openSegment ℝ Pq.vertices[0] Pq.vertices[1] := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨r, hr, rfl⟩
  have hcutNotX : cut ∉ X := by
    intro hcutX
    exact hrbad (Finset.mem_preimage.2 hcutX)
  have hcutCarrier : cut ∈ Pq.carrier := by
    rw [Pq.carrier_eq]
    exact ⟨0, hfirstq, openSegment_subset_segment ℝ _ _ hcutOpen⟩
  have hcutInterior : cut ∈ Pq.relativeInterior :=
    PolygonalArcOpenSegmentSubsetRelativeInterior Pq 0 hfirstq hcutOpen
  have hcutEnds := hcutInterior
  rw [Pq.relativeInterior_eq] at hcutEnds
  have hcutNeSource : cut ≠ Pq.source := by
    have hnot := hcutEnds.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
    exact hnot.1
  have hcutNeTarget : cut ≠ Pq.target := by
    have hnot := hcutEnds.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
    exact hnot.2
  obtain ⟨D⟩ := PolygonalArcPointCutDataExists Pq cut hcutInterior
  have hDcutLt : D.cutIndex < Pq.vertices.length :=
    Nat.lt_of_succ_lt D.cutIndex_valid
  have hDcutSucc : D.cutIndex + 1 < Pq.vertices.length :=
    D.cutIndex_valid
  have hDNotLeft : cut ≠ Pq.vertices[D.cutIndex] := by
    intro hleft
    have hnodup : (Pq.vertices.take (D.cutIndex + 1) ++ [cut]).Nodup := by
      rw [← D.prefix_vertices_exact]
      exact D.prefixArc.simple_vertices
    rw [List.nodup_append] at hnodup
    have hmemTake : Pq.vertices[D.cutIndex] ∈
        Pq.vertices.take (D.cutIndex + 1) := by
      have hbound : D.cutIndex < (Pq.vertices.take (D.cutIndex + 1)).length := by
        simp [List.length_take]
        omega
      have hmem := List.getElem_mem hbound
      simpa only [List.getElem_take] using hmem
    exact hnodup.2.2 Pq.vertices[D.cutIndex] hmemTake cut (by simp) hleft.symm
  have hDzero : D.cutIndex = 0 := by
    by_contra hne
    have hpos : 0 < D.cutIndex := Nat.pos_of_ne_zero hne
    have hinterRaw := Pq.segment_intersections (i := 0) (j := D.cutIndex)
      hfirstq D.cutIndex_valid hpos
    have hcutInter : cut ∈
        segment ℝ Pq.vertices[0] Pq.vertices[1] ∩
          segment ℝ Pq.vertices[D.cutIndex] Pq.vertices[D.cutIndex + 1] :=
      ⟨openSegment_subset_segment ℝ _ _ hcutOpen, D.cut_mem_segment⟩
    by_cases hone : D.cutIndex = 1
    · rw [hinterRaw, if_pos (by omega : D.cutIndex = 0 + 1)] at hcutInter
      exact hDNotLeft (by simpa [hone] using hcutInter)
    · rw [hinterRaw, if_neg (by omega : D.cutIndex ≠ 0 + 1)] at hcutInter
      exact hcutInter
  let firstPiece := D.prefixArc
  let remainder := D.suffixArc
  have hfirstPieceCarrier : firstPiece.carrier ⊆
      segment ℝ (P.vertices[0]'(by
          have := P.length_ge_two
          omega)) (P.vertices[1]'(by
          have := P.length_ge_two
          omega)) := by
    intro z hz
    have hz' := hz
    change z ∈ D.prefixArc.carrier at hz'
    rw [D.prefix_carrier_region] at hz'
    have hzPq : z ∈ segment ℝ Pq.vertices[0] cut := by
      rcases hz' with hz' | hz'
      · rcases hz' with ⟨i, _hi, hi, _⟩
        exfalso
        omega
      · simpa only [hDzero] using hz'
    exact hfirstClosed
      ((convex_segment Pq.vertices[0] Pq.vertices[1]).segment_subset
        (left_mem_segment ℝ _ _)
        (openSegment_subset_segment ℝ _ _ hcutOpen) hzPq)
  have hqRemainder : q ∈ remainder.carrier := by
    rw [← hPqTarget, ← D.suffix_target]
    exact arc_target_mem remainder
  have hqNotFirst : q ∉ firstPiece.carrier := by
    intro hqFirst
    have hboth : q ∈ firstPiece.carrier ∩ remainder.carrier :=
      ⟨hqFirst, hqRemainder⟩
    have hqEqCut : q = cut := by
      have : q ∈ ({cut} : Set E) := D.carrier_intersection ▸ hboth
      simpa using this
    exact hcutNeTarget (hqEqCut.symm.trans hPqTarget.symm)
  have hsourceFirst : Pq.source ∈ firstPiece.carrier := by
    rw [← D.prefix_source]
    exact arc_source_mem firstPiece
  have hsourceNotRemainder : Pq.source ∉ remainder.carrier := by
    intro hsR
    have hboth : Pq.source ∈ firstPiece.carrier ∩ remainder.carrier :=
      ⟨hsourceFirst, hsR⟩
    have hsCut : Pq.source = cut := by
      have : Pq.source ∈ ({cut} : Set E) := D.carrier_intersection ▸ hboth
      simpa using this
    exact hcutNeSource hsCut.symm
  have hfirstPieceDisjointT : Disjoint firstPiece.carrier T.carrier := by
    rw [Set.disjoint_left]
    intro z hzF hzT
    have hzEq : z = q := by
      have hzPq : z ∈ Pq.carrier := D.prefix_carrier_subset hzF
      have : z ∈ ({q} : Set E) := hPqMeetsT ▸ ⟨hzPq, hzT⟩
      simpa using this
    exact hqNotFirst (hzEq ▸ hzF)
  have hremainderT : remainder.carrier ∩ T.carrier = ({q} : Set E) := by
    ext z
    constructor
    · rintro ⟨hzR, hzT⟩
      have hzPq : z ∈ Pq.carrier := D.suffix_carrier_subset hzR
      have : z ∈ ({q} : Set E) := hPqMeetsT ▸ ⟨hzPq, hzT⟩
      exact this
    · intro hz
      have hzEq : z = q := by simpa using hz
      subst z
      exact ⟨hqRemainder, hqContact.2⟩
  have hfirstInteriorPq : firstPiece.relativeInterior ⊆ Pq.relativeInterior := by
    intro z hz
    change z ∈ D.prefixArc.relativeInterior at hz
    rw [D.prefixArc.relativeInterior_eq] at hz
    rw [Pq.relativeInterior_eq]
    refine ⟨D.prefix_carrier_subset hz.1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hzSource
      have hnotOwn := hz.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotOwn
      have hzNotOwnSource : z ≠ D.prefixArc.source := hnotOwn.1
      exact hzNotOwnSource (by simpa [D.prefix_source] using hzSource)
    · intro hzTarget
      apply hqNotFirst
      have hzQ : z = q := hzTarget.trans hPqTarget
      exact hzQ ▸ hz.1
  have hremainderInteriorPq : remainder.relativeInterior ⊆ Pq.relativeInterior := by
    intro z hz
    change z ∈ D.suffixArc.relativeInterior at hz
    rw [D.suffixArc.relativeInterior_eq] at hz
    rw [Pq.relativeInterior_eq]
    refine ⟨D.suffix_carrier_subset hz.1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hzSource
      exact hsourceNotRemainder (hzSource ▸ hz.1)
    · intro hzTarget
      have hnotOwn := hz.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotOwn
      have hzNotOwnTarget : z ≠ D.suffixArc.target := hnotOwn.2
      exact hzNotOwnTarget (by simpa [D.suffix_target, hPqTarget] using hzTarget)
  have hfirstPieceInterior : firstPiece.relativeInterior ⊆
      openSegment ℝ (P.vertices[0]'(by
          have := P.length_ge_two
          omega)) (P.vertices[1]'(by
          have := P.length_ge_two
          omega)) := by
    intro z hz
    have hzOwn := hz
    change z ∈ D.prefixArc.relativeInterior at hzOwn
    rw [D.prefixArc.relativeInterior_eq] at hzOwn
    have hzSeg : z ∈ segment ℝ Pq.vertices[0] cut := by
      have hzCarrier := hzOwn.1
      rw [D.prefix_carrier_region] at hzCarrier
      rcases hzCarrier with hzCarrier | hzCarrier
      · rcases hzCarrier with ⟨i, _hi, hi, _⟩
        exfalso
        omega
      · simpa only [hDzero] using hzCarrier
    have hnotOwn := hzOwn.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotOwn
    have hzNeLeft : z ≠ Pq.vertices[0] := by
      intro hEq
      exact hnotOwn.1 (by
        calc
          z = Pq.vertices[0] := hEq
          _ = Pq.source := arc_first_vertex Pq
          _ = D.prefixArc.source := D.prefix_source.symm)
    have hzNeCut : z ≠ cut := by
      intro hEq
      exact hnotOwn.2 (hEq.trans D.prefix_target.symm)
    have hzOpenShort : z ∈ openSegment ℝ Pq.vertices[0] cut :=
      mem_openSegment_of_ne_left_right hzNeLeft.symm hzNeCut.symm hzSeg
    have hleftNeCut : Pq.vertices[0] ≠ cut := by
      intro hEq
      have : Pq.vertices[0] ∈ openSegment ℝ Pq.vertices[0] Pq.vertices[1] := by
        simpa [hEq] using hcutOpen
      exact hfirstNe (left_mem_openSegment_iff.1 this)
    apply hfirstOpen
    exact open_of_segment_subset hleftNeCut
      ((convex_segment Pq.vertices[0] Pq.vertices[1]).segment_subset
        (left_mem_segment ℝ _ _)
        (openSegment_subset_segment ℝ _ _ hcutOpen)) hzOpenShort
  refine ⟨cut, firstPiece, remainder, hcutNotX, hcutInterior,
    D.prefix_source.trans hPqSource, D.prefix_target,
    D.suffix_source, D.suffix_target.trans hPqTarget,
    D.carrier_decomposition, D.carrier_intersection,
    hfirstPieceDisjointT, hremainderT, hfirstPieceCarrier,
    hfirstPieceInterior, hfirstInteriorPq, hremainderInteriorPq, ?_⟩
  intro piece hpiece z i hi hzOld hzPiece hzNeCut hzNeQ
  have hpieceCases : piece = firstPiece ∨ piece = remainder := by
    simpa [firstPiece, remainder] using hpiece
  have hzPq : z ∈ Pq.carrier := by
    rcases hpieceCases with rfl | rfl
    · exact D.prefix_carrier_subset hzPiece
    · exact D.suffix_carrier_subset hzPiece
  obtain ⟨j, hj, hzPqOpen, c₁, hc₁, hdir₁⟩ :=
    hPqTransfer z i hi hzOld hzPq hzNeQ
  rcases hpieceCases with rfl | rfl
  · obtain ⟨k, hk, hzOpen, c₂, hc₂, hdir₂⟩ :=
      D.prefix_segment_transfer z j hj hzPqOpen hzPiece hzNeCut
    refine ⟨k, hk, hzOpen, c₂ * c₁, mul_ne_zero hc₂ hc₁, ?_⟩
    rw [hdir₂, hdir₁, smul_smul]
  · obtain ⟨k, hk, hzOpen, c₂, hc₂, hdir₂⟩ :=
      D.suffix_segment_transfer z j hj hzPqOpen hzPiece hzNeCut
    refine ⟨k, hk, hzOpen, c₂ * c₁, mul_ne_zero hc₂ hc₁, ?_⟩
    rw [hdir₂, hdir₁, smul_smul]
