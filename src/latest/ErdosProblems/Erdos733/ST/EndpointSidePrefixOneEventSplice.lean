import ErdosProblems.Erdos733.ST.EndpointSidePrefixEventBridge
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.PolygonalArcOrderedBallCutDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcOrderedThreePieceSplice

open Classical
noncomputable section

-- [TABLET NODE: EndpointSidePrefixOneEventSplice]
lemma EndpointSidePrefixOneEventSplice
    (Q : PolygonalArc)
    (SelectedSide H Bad Forbidden StartSector EndpointControl TerminalSet :
      Set (EuclideanSpace ℝ (Fin 2)))
    (K : FinitePolygonalSet)
    (p : EuclideanSpace ℝ (Fin 2))
    (radius : ℝ)
    (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    IsOpen SelectedSide →
      Q.carrier ⊆
        SelectedSide ∪ ({Q.source} : Set (EuclideanSpace ℝ (Fin 2))) →
      Q.relativeInterior ⊆ SelectedSide →
      Q.relativeInterior ∩ Forbidden =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      SelectedSide ∩ Forbidden =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      K.carrier = H →
      (K.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Bad →
      SelectedSide ∩ Bad =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      Q.source ∈ EndpointControl →
      Q.target ∈ EndpointControl →
      (∃ hfirst : 0 + 1 < Q.vertices.length,
        segment ℝ Q.vertices[0] Q.vertices[1] ⊆
            StartSector ∪ ({Q.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
          openSegment ℝ Q.vertices[0] Q.vertices[1] ⊆ StartSector ∧
          segment ℝ Q.vertices[0] Q.vertices[1] ⊆ EndpointControl) →
      TerminalSet ⊆ EndpointControl →
      Set.Finite (Q.carrier ∩ TerminalSet) →
      Disjoint (Metric.closedBall p radius) EndpointControl →
      0 < radius →
      Convex ℝ (SelectedSide ∩ Metric.ball p radius) →
      s ∈ K.segments →
      p ∈ openSegment ℝ s.1 s.2 →
      Metric.ball p radius ∩ H =
        Metric.ball p radius ∩ segment ℝ s.1 s.2 →
      ∃ Q' : PolygonalArc,
        Q'.source = Q.source ∧
          Q'.target = Q.target ∧
          Q'.carrier ⊆
            SelectedSide ∪
              ({Q'.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
          Q'.relativeInterior ⊆ SelectedSide ∧
          Q'.relativeInterior ∩ Forbidden =
            (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
          Set.Finite (Q'.carrier ∩ TerminalSet) ∧
          (∃ hfirst : 0 + 1 < Q'.vertices.length,
            segment ℝ Q'.vertices[0] Q'.vertices[1] ⊆
                StartSector ∪
                  ({Q'.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
              openSegment ℝ Q'.vertices[0] Q'.vertices[1] ⊆ StartSector ∧
              segment ℝ Q'.vertices[0] Q'.vertices[1] ⊆ EndpointControl) ∧
          (Q'.relativeInterior ∩ H ∩ Metric.ball p radius).Subsingleton ∧
          (∀ z, z ∈ Q'.relativeInterior → z ∈ H →
            z ∈ Metric.ball p radius →
              ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
                z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                  z ∈ openSegment ℝ s.1 s.2 ∧
                  ¬ ∃ c : ℝ,
                    s.2 - s.1 =
                      c • (Q'.vertices[j + 1] - Q'.vertices[j])) ∧
          Q'.carrier \ Metric.ball p radius ⊆
            Q.carrier \ Metric.ball p radius ∧
          (∀ z i (hi : i + 1 < Q.vertices.length),
            z ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] →
            z ∈ Q'.carrier →
            z ∉ Metric.closedBall p radius →
            ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
              z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                ∃ c : ℝ, c ≠ 0 ∧
                  Q'.vertices[j + 1] - Q'.vertices[j] =
                    c • (Q.vertices[i + 1] - Q.vertices[i])) ∧
          ((Q.carrier ∩ Metric.ball p radius = ∅ ∧ Q' = Q) ∨
            ∃ (D : PolygonalArcOrderedBallCutData Q p radius)
                (bridge : PolygonalArc)
                (rminus rplus : EuclideanSpace ℝ (Fin 2)),
              bridge.vertices = [D.qminus, rminus, rplus, D.qplus] ∧
                bridge.source = D.qminus ∧
                bridge.target = D.qplus ∧
                rminus ∈ SelectedSide ∩ Metric.ball p radius ∧
                rplus ∈ SelectedSide ∩ Metric.ball p radius ∧
                bridge.carrier =
                  segment ℝ D.qminus rminus ∪
                    segment ℝ rminus rplus ∪
                    segment ℝ rplus D.qplus ∧
                bridge.relativeInterior ⊆
                  SelectedSide ∩ Metric.ball p radius ∧
                D.prefixArc.carrier ∩ bridge.carrier = {D.qminus} ∧
                bridge.carrier ∩ D.suffixArc.carrier = {D.qplus} ∧
                Q'.vertices =
                  PolygonalArcEndpointGluedVertices
                    [D.prefixArc, bridge, D.suffixArc] ∧
                Q'.carrier =
                  D.prefixArc.carrier ∪ bridge.carrier ∪
                    D.suffixArc.carrier ∧
                (bridge.relativeInterior ∩ H).Subsingleton ∧
                ∀ z, z ∈ bridge.relativeInterior → z ∈ H →
                  ∃ j : ℕ, ∃ hj : j + 1 < bridge.vertices.length,
                    z ∈ openSegment ℝ
                        bridge.vertices[j] bridge.vertices[j + 1] ∧
                      z ∈ openSegment ℝ s.1 s.2 ∧
                      ¬ ∃ c : ℝ,
                        s.2 - s.1 =
                          c • (bridge.vertices[j + 1] -
                            bridge.vertices[j])) := by
-- BODY
  intro hSelectedOpen hQcarrier hQinterior hQForbidden
    hSelectedForbidden hKcarrier hKpoints hSelectedBad hQsourceControl
    hQtargetControl hfirst hTerminalControl hTerminalFinite hBallControl
    hRadius hConvex hsSegment hpSegment hBallModel
  rcases hfirst with
    ⟨hfirstIndex, hfirstStart, hfirstOpen, hfirstControl⟩
  by_cases hQBall : Q.carrier ∩ Metric.ball p radius = ∅
  · refine ⟨Q, rfl, rfl, hQcarrier, hQinterior, hQForbidden,
      hTerminalFinite, ⟨hfirstIndex, hfirstStart, hfirstOpen,
        hfirstControl⟩, ?_, ?_, ?_, ?_, Or.inl ⟨hQBall, rfl⟩⟩
    · intro z hz w hw
      have hzEmpty : z ∈ Q.carrier ∩ Metric.ball p radius := by
        refine ⟨?_, hz.2⟩
        have hzInterior := hz.1.1
        rw [Q.relativeInterior_eq] at hzInterior
        exact hzInterior.1
      rw [hQBall] at hzEmpty
      exact False.elim hzEmpty
    · intro z hzInterior hzH hzBall
      have hzEmpty : z ∈ Q.carrier ∩ Metric.ball p radius := by
        rw [Q.relativeInterior_eq] at hzInterior
        exact ⟨hzInterior.1, hzBall⟩
      rw [hQBall] at hzEmpty
      exact False.elim hzEmpty
    · intro z hz
      exact hz
    · intro z i hi hzOpenSegment hzCarrier hzClosed
      exact ⟨i, hi, hzOpenSegment, 1, one_ne_zero, by simp⟩
  · have hQBallNonempty :
        (Q.carrier ∩ Metric.ball p radius).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hQBall
    have hQsourceOutside : Q.source ∉ Metric.closedBall p radius := by
      intro hsourceBall
      exact (Set.disjoint_left.mp hBallControl hsourceBall) hQsourceControl
    have hQtargetOutside : Q.target ∉ Metric.closedBall p radius := by
      intro htargetBall
      exact (Set.disjoint_left.mp hBallControl htargetBall) hQtargetControl
    have hfirstDisjoint :
        Disjoint
          (segment ℝ Q.vertices[0] Q.vertices[1])
          (Metric.closedBall p radius) := by
      rw [Set.disjoint_left]
      intro z hzFirst hzBall
      exact (Set.disjoint_left.mp hBallControl hzBall)
        (hfirstControl hzFirst)
    obtain ⟨D⟩ := PolygonalArcOrderedBallCutDataExists Q p radius
      hQsourceOutside hQtargetOutside hQBallNonempty
    have hqminusSelected : D.qminus ∈ SelectedSide :=
      hQinterior D.qminus_mem_relativeInterior
    have hqplusSelected : D.qplus ∈ SelectedSide :=
      hQinterior D.qplus_mem_relativeInterior
    rcases EndpointSidePrefixEventBridge Q SelectedSide H Bad K p radius s D
        hSelectedOpen hqminusSelected hqplusSelected hConvex hKcarrier
        hKpoints hSelectedBad hsSegment hpSegment hBallModel with
      ⟨bridge, rminus, rplus, hbridgeVertices, hbridgeSource,
        hbridgeTarget, hrminus, hrplus, hbridgeCarrier, hbridgeInterior,
        hprefixBridge, hbridgeSuffix, hbridgeContacts,
        hbridgeContactCertificate⟩
    rcases PolygonalArcOrderedThreePieceSplice Q bridge p radius D
        hbridgeSource hbridgeTarget (fun z hz => (hbridgeInterior hz).2)
        hprefixBridge hbridgeSuffix with
      ⟨Q', hQ'vertices, hQ'source, hQ'target, hQ'carrier,
        hQ'interior, hprefixInterior, hbridgeInteriorQ',
        hsuffixInterior, hbridgeTransfer, holdTransfer⟩
    have hbridgeCarrierSelected : bridge.carrier ⊆ SelectedSide := by
      intro z hzBridge
      by_cases hzEnds :
          z ∈ ({bridge.source, bridge.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzEnds
        rcases hzEnds with hzSource | hzTarget
        · rw [hzSource, hbridgeSource]
          exact hqminusSelected
        · rw [hzTarget, hbridgeTarget]
          exact hqplusSelected
      · exact (hbridgeInterior (by
          rw [bridge.relativeInterior_eq]
          exact ⟨hzBridge, hzEnds⟩)).1
    have hQ'carrierSelected :
        Q'.carrier ⊆
          SelectedSide ∪
            ({Q'.source} : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro z hzQ'
      rw [hQ'carrier] at hzQ'
      rcases hzQ' with (hzPrefix | hzBridge) | hzSuffix
      · have hzOld := hQcarrier (D.prefix_carrier_subset hzPrefix)
        simpa only [hQ'source] using hzOld
      · exact Or.inl (hbridgeCarrierSelected hzBridge)
      · have hzOld := hQcarrier (D.suffix_carrier_subset hzSuffix)
        simpa only [hQ'source] using hzOld
    have hQ'interiorSelected : Q'.relativeInterior ⊆ SelectedSide := by
      intro z hzQ'
      rw [hQ'interior] at hzQ'
      rcases hzQ'.1 with (hzPrefix | hzBridge) | hzSuffix
      · apply hQinterior
        rw [Q.relativeInterior_eq]
        refine ⟨D.prefix_carrier_subset hzPrefix, ?_⟩
        simpa only [hQ'source, hQ'target] using hzQ'.2
      · exact hbridgeCarrierSelected hzBridge
      · apply hQinterior
        rw [Q.relativeInterior_eq]
        refine ⟨D.suffix_carrier_subset hzSuffix, ?_⟩
        simpa only [hQ'source, hQ'target] using hzQ'.2
    have hQ'Forbidden :
        Q'.relativeInterior ∩ Forbidden =
          (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [← Set.subset_empty_iff]
      intro z hz
      have hzBad : z ∈ SelectedSide ∩ Forbidden :=
        ⟨hQ'interiorSelected hz.1, hz.2⟩
      rw [hSelectedForbidden] at hzBad
      exact hzBad
    have hbridgeClosedBall : bridge.carrier ⊆ Metric.closedBall p radius := by
      intro z hzBridge
      by_cases hzEnds :
          z ∈ ({bridge.source, bridge.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzEnds
        rcases hzEnds with hzSource | hzTarget
        · rw [hzSource, hbridgeSource]
          exact Metric.sphere_subset_closedBall D.qminus_mem_sphere
        · rw [hzTarget, hbridgeTarget]
          exact Metric.sphere_subset_closedBall D.qplus_mem_sphere
      · exact Metric.ball_subset_closedBall
          (hbridgeInterior (by
            rw [bridge.relativeInterior_eq]
            exact ⟨hzBridge, hzEnds⟩)).2
    have hbridgeTerminalDisjoint :
        Disjoint bridge.carrier TerminalSet := by
      rw [Set.disjoint_left]
      intro z hzBridge hzTerminal
      exact (Set.disjoint_left.mp hBallControl
        (hbridgeClosedBall hzBridge)) (hTerminalControl hzTerminal)
    have hQ'TerminalFinite : Set.Finite (Q'.carrier ∩ TerminalSet) := by
      apply hTerminalFinite.subset
      intro z hz
      refine ⟨?_, hz.2⟩
      rw [hQ'carrier] at hz
      rcases hz.1 with (hzPrefix | hzBridge) | hzSuffix
      · exact D.prefix_carrier_subset hzPrefix
      · exact False.elim
          ((Set.disjoint_left.mp hbridgeTerminalDisjoint hzBridge) hz.2)
      · exact D.suffix_carrier_subset hzSuffix
    obtain ⟨hprefixFirstIndex, hprefixZero, hprefixOne⟩ :=
      D.protected_first_vertices hfirstIndex hfirstDisjoint
    have hQ'firstIndex : 0 + 1 < Q'.vertices.length := by
      have := Q'.length_ge_two
      omega
    have hQ'zero : Q'.vertices[0] = Q.vertices[0] := by
      have hopt := congrArg
        (fun V : List (EuclideanSpace ℝ (Fin 2)) => V[0]?) hQ'vertices
      change Q'.vertices[0]? =
        (PolygonalArcEndpointGluedVertices
          [D.prefixArc, bridge, D.suffixArc])[0]? at hopt
      rw [List.getElem?_eq_getElem (by
        have := Q'.length_ge_two
        omega)] at hopt
      simp [PolygonalArcEndpointGluedVertices,
        show 0 < D.prefixArc.vertices.length by
          have := D.prefixArc.length_ge_two
          omega] at hopt
      exact hopt.trans hprefixZero
    have hQ'one : Q'.vertices[1] = Q.vertices[1] := by
      have hopt := congrArg
        (fun V : List (EuclideanSpace ℝ (Fin 2)) => V[1]?) hQ'vertices
      change Q'.vertices[1]? =
        (PolygonalArcEndpointGluedVertices
          [D.prefixArc, bridge, D.suffixArc])[1]? at hopt
      rw [List.getElem?_eq_getElem (by
        have := Q'.length_ge_two
        omega)] at hopt
      rw [PolygonalArcEndpointGluedVertices] at hopt
      rw [List.getElem?_append_left (by
        have := D.prefixArc.length_ge_two
        omega)] at hopt
      rw [List.getElem?_eq_getElem (by
        have := D.prefixArc.length_ge_two
        omega)] at hopt
      exact (Option.some.inj hopt).trans hprefixOne
    have hQ'first :
        ∃ hfirst' : 0 + 1 < Q'.vertices.length,
          segment ℝ Q'.vertices[0] Q'.vertices[1] ⊆
              StartSector ∪
                ({Q'.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
            openSegment ℝ Q'.vertices[0] Q'.vertices[1] ⊆
              StartSector ∧
            segment ℝ Q'.vertices[0] Q'.vertices[1] ⊆
              EndpointControl := by
      refine ⟨hQ'firstIndex, ?_, ?_, ?_⟩
      · simpa only [hQ'zero, hQ'one, hQ'source] using hfirstStart
      · simpa only [hQ'zero, hQ'one] using hfirstOpen
      · simpa only [hQ'zero, hQ'one] using hfirstControl
    have hQ'BallToBridge :
        Q'.relativeInterior ∩ H ∩ Metric.ball p radius ⊆
          bridge.relativeInterior ∩ H := by
      intro z hz
      have hzCarrier : z ∈ Q'.carrier := by
        have hzInterior := hz.1.1
        rw [Q'.relativeInterior_eq] at hzInterior
        exact hzInterior.1
      rw [hQ'carrier] at hzCarrier
      have hzBridge : z ∈ bridge.carrier := by
        rcases hzCarrier with (hzPrefix | hzBridge) | hzSuffix
        · exact False.elim
            ((Set.disjoint_left.mp D.prefix_avoids_ball hzPrefix) hz.2)
        · exact hzBridge
        · exact False.elim
            ((Set.disjoint_left.mp D.suffix_avoids_ball hzSuffix) hz.2)
      have hzNotEnds :
          z ∉ ({bridge.source, bridge.target} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
        intro hzEnds
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzEnds
        rcases hzEnds with hzSource | hzTarget
        · have hzSphere : z ∈ Metric.sphere p radius := by
            simpa only [hzSource, hbridgeSource] using D.qminus_mem_sphere
          rw [Metric.mem_sphere] at hzSphere
          have hzBall := hz.2
          rw [Metric.mem_ball] at hzBall
          linarith
        · have hzSphere : z ∈ Metric.sphere p radius := by
            simpa only [hzTarget, hbridgeTarget] using D.qplus_mem_sphere
          rw [Metric.mem_sphere] at hzSphere
          have hzBall := hz.2
          rw [Metric.mem_ball] at hzBall
          linarith
      refine ⟨?_, hz.1.2⟩
      rw [bridge.relativeInterior_eq]
      exact ⟨hzBridge, hzNotEnds⟩
    have hQ'Contacts :
        (Q'.relativeInterior ∩ H ∩ Metric.ball p radius).Subsingleton := by
      intro z hz w hw
      exact hbridgeContacts (hQ'BallToBridge hz) (hQ'BallToBridge hw)
    have hQ'ContactCertificate :
        ∀ z, z ∈ Q'.relativeInterior → z ∈ H →
          z ∈ Metric.ball p radius →
            ∃ j : ℕ, ∃ hj : j + 1 < Q'.vertices.length,
              z ∈ openSegment ℝ Q'.vertices[j] Q'.vertices[j + 1] ∧
                z ∈ openSegment ℝ s.1 s.2 ∧
                ¬ ∃ c : ℝ,
                  s.2 - s.1 =
                    c • (Q'.vertices[j + 1] - Q'.vertices[j]) := by
      intro z hzInterior hzH hzBall
      have hzBridge := hQ'BallToBridge ⟨⟨hzInterior, hzH⟩, hzBall⟩
      rcases hbridgeContactCertificate z hzBridge.1 hzBridge.2 with
        ⟨m, hm, hzOpenBridge, hzOpenS, hNonparallel⟩
      rcases hbridgeTransfer z m hm hzOpenBridge with
        ⟨j, hj, hzOpenQ', c, hc, hDirection⟩
      refine ⟨j, hj, hzOpenQ', hzOpenS, ?_⟩
      rintro ⟨d, hd⟩
      apply hNonparallel
      refine ⟨d * c, ?_⟩
      rw [hDirection] at hd
      simpa only [smul_smul] using hd
    have hbridgeOutsideOld :
        bridge.carrier \ Metric.ball p radius ⊆ Q.carrier := by
      intro z hz
      by_cases hzEnds :
          z ∈ ({bridge.source, bridge.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzEnds
        rcases hzEnds with hzSource | hzTarget
        · have hzRelative := D.qminus_mem_relativeInterior
          rw [Q.relativeInterior_eq] at hzRelative
          simpa only [hzSource, hbridgeSource] using hzRelative.1
        · have hzRelative := D.qplus_mem_relativeInterior
          rw [Q.relativeInterior_eq] at hzRelative
          simpa only [hzTarget, hbridgeTarget] using hzRelative.1
      · have hzBall : z ∈ Metric.ball p radius :=
          (hbridgeInterior (by
            rw [bridge.relativeInterior_eq]
            exact ⟨hz.1, hzEnds⟩)).2
        exact False.elim (hz.2 hzBall)
    have hQ'Outside :
        Q'.carrier \ Metric.ball p radius ⊆
          Q.carrier \ Metric.ball p radius := by
      intro z hz
      refine ⟨?_, hz.2⟩
      rw [hQ'carrier] at hz
      rcases hz.1 with (hzPrefix | hzBridge) | hzSuffix
      · exact D.prefix_carrier_subset hzPrefix
      · exact hbridgeOutsideOld ⟨hzBridge, hz.2⟩
      · exact D.suffix_carrier_subset hzSuffix
    refine ⟨Q', hQ'source, hQ'target, hQ'carrierSelected,
      hQ'interiorSelected, hQ'Forbidden, hQ'TerminalFinite, hQ'first,
      hQ'Contacts, hQ'ContactCertificate, hQ'Outside, holdTransfer,
      Or.inr ?_⟩
    exact ⟨D, bridge, rminus, rplus, hbridgeVertices, hbridgeSource,
      hbridgeTarget, hrminus, hrplus, hbridgeCarrier, hbridgeInterior,
      hprefixBridge, hbridgeSuffix, hQ'vertices, hQ'carrier,
      hbridgeContacts, hbridgeContactCertificate⟩
