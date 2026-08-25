import Util.IncidenceGeometry.EndpointSidePrefixOneEventSplice

open Classical
noncomputable section

lemma EndpointSidePrefixFiniteEventSplice
    (P predecessor approach : PolygonalArc)
    (SelectedSide H Bad Forbidden StartSector EndpointControl :
      Set (EuclideanSpace ℝ (Fin 2)))
    (h terminalGate : EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (eventRadius : EuclideanSpace ℝ (Fin 2) → ℝ) :
    IsOpen SelectedSide →
      P.carrier ⊆
        SelectedSide ∪ ({P.source} : Set (EuclideanSpace ℝ (Fin 2))) →
      P.relativeInterior ⊆ SelectedSide →
      P.relativeInterior ∩ Forbidden =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      SelectedSide ∩ Forbidden =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      K.carrier = H →
      Set.Finite
        (P.carrier ∩
          (predecessor.carrier ∪ approach.carrier ∪
            segment ℝ h terminalGate)) →
      P.source ∈ EndpointControl →
      P.target ∈ EndpointControl →
      (∃ hfirst : 0 + 1 < P.vertices.length,
        segment ℝ P.vertices[0] P.vertices[1] ⊆
            StartSector ∪ ({P.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
          openSegment ℝ P.vertices[0] P.vertices[1] ⊆ StartSector ∧
          segment ℝ P.vertices[0] P.vertices[1] ⊆ EndpointControl) →
      predecessor.carrier ∪ approach.carrier ∪
          segment ℝ h terminalGate ⊆ EndpointControl →
      (K.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Bad →
      SelectedSide ∩ Bad =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      SelectedSide ∩ H ⊆
        ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
          Metric.ball p (eventRadius p) →
      (∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ XA →
          0 < eventRadius p ∧
            Convex ℝ (SelectedSide ∩ Metric.ball p (eventRadius p)) ∧
            ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
              s ∈ K.segments ∧
                p ∈ openSegment ℝ s.1 s.2 ∧
                Metric.ball p (eventRadius p) ∩ H =
                  Metric.ball p (eventRadius p) ∩ segment ℝ s.1 s.2) →
      (∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ XA →
          Disjoint
            (Metric.closedBall p (eventRadius p)) EndpointControl) →
      (∀ p q : EuclideanSpace ℝ (Fin 2),
        p ∈ XA → q ∈ XA → p ≠ q →
          Disjoint
            (Metric.closedBall p (eventRadius p))
            (Metric.closedBall q (eventRadius q))) →
      ∃ Pclean : PolygonalArc,
        Pclean.source = P.source ∧
          Pclean.target = P.target ∧
          Pclean.carrier ⊆
            SelectedSide ∪
              ({Pclean.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
          Pclean.relativeInterior ⊆ SelectedSide ∧
          Pclean.relativeInterior ∩ Forbidden =
            (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
          Set.Finite
            (Pclean.carrier ∩
              (predecessor.carrier ∪ approach.carrier ∪
                segment ℝ h terminalGate)) ∧
          (∃ hfirst : 0 + 1 < Pclean.vertices.length,
            segment ℝ Pclean.vertices[0] Pclean.vertices[1] ⊆
                StartSector ∪
                  ({Pclean.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
              openSegment ℝ Pclean.vertices[0] Pclean.vertices[1] ⊆
                StartSector ∧
              segment ℝ Pclean.vertices[0] Pclean.vertices[1] ⊆
                EndpointControl) ∧
          (∀ p, p ∈ XA →
            (Pclean.relativeInterior ∩ H ∩
              Metric.ball p (eventRadius p)).Subsingleton) ∧
          (∀ z, z ∈ Pclean.relativeInterior → z ∈ H →
            ∃ j : ℕ, ∃ hj : j + 1 < Pclean.vertices.length,
              z ∈ openSegment ℝ
                  Pclean.vertices[j] Pclean.vertices[j + 1] ∧
                ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
                  s ∈ K.segments ∧
                    z ∈ openSegment ℝ s.1 s.2 ∧
                    ¬ ∃ c : ℝ,
                      s.2 - s.1 =
                        c • (Pclean.vertices[j + 1] - Pclean.vertices[j])) ∧
          Pclean.carrier \
              (⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
                Metric.ball p (eventRadius p)) ⊆
            P.carrier \
              (⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
                Metric.ball p (eventRadius p)) := by
  intro hSelectedOpen hPcarrier hPinterior hPForbidden
    hSelectedForbidden hKcarrier hTerminalFinite hPsourceControl
    hPtargetControl hfirst hTerminalControl hKpoints hSelectedBad
    hEventCover hEventData hBallControl hBallPairwise
  have hInduction :
      ∀ Xproc : Finset (EuclideanSpace ℝ (Fin 2)),
        Xproc ⊆ XA →
          ∃ Q : PolygonalArc,
            Q.source = P.source ∧
              Q.target = P.target ∧
              Q.carrier ⊆
                SelectedSide ∪
                  ({Q.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
              Q.relativeInterior ⊆ SelectedSide ∧
              Q.relativeInterior ∩ Forbidden =
                (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
              Set.Finite
                (Q.carrier ∩
                  (predecessor.carrier ∪ approach.carrier ∪
                    segment ℝ h terminalGate)) ∧
              (∃ hfirstQ : 0 + 1 < Q.vertices.length,
                segment ℝ Q.vertices[0] Q.vertices[1] ⊆
                    StartSector ∪
                      ({Q.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                  openSegment ℝ Q.vertices[0] Q.vertices[1] ⊆
                    StartSector ∧
                  segment ℝ Q.vertices[0] Q.vertices[1] ⊆
                    EndpointControl) ∧
              (∀ p, p ∈ Xproc →
                (Q.relativeInterior ∩ H ∩
                  Metric.ball p (eventRadius p)).Subsingleton) ∧
              (∀ p, p ∈ Xproc →
                ∀ z, z ∈ Q.relativeInterior → z ∈ H →
                  z ∈ Metric.ball p (eventRadius p) →
                    ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
                      z ∈ openSegment ℝ
                          Q.vertices[j] Q.vertices[j + 1] ∧
                        ∃ s : EuclideanSpace ℝ (Fin 2) ×
                            EuclideanSpace ℝ (Fin 2),
                          s ∈ K.segments ∧
                            z ∈ openSegment ℝ s.1 s.2 ∧
                            ¬ ∃ c : ℝ,
                              s.2 - s.1 =
                                c • (Q.vertices[j + 1] - Q.vertices[j])) ∧
              Q.carrier \
                  (⋃ p ∈ (Xproc : Set (EuclideanSpace ℝ (Fin 2))),
                    Metric.ball p (eventRadius p)) ⊆
                P.carrier \
                  (⋃ p ∈ (Xproc : Set (EuclideanSpace ℝ (Fin 2))),
                    Metric.ball p (eventRadius p)) := by
    intro Xproc
    induction Xproc using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨P, rfl, rfl, hPcarrier, hPinterior, hPForbidden,
          hTerminalFinite, hfirst, ?_, ?_, ?_⟩
        · intro p hp
          simp at hp
        · intro p hp
          simp at hp
        · intro z hz
          exact hz
    | @insert p Xproc hpNotProcessed ih =>
        intro hInsertSubset
        have hpXA : p ∈ XA := hInsertSubset (by simp)
        have hXprocSubset : Xproc ⊆ XA := by
          intro q hq
          exact hInsertSubset (by simp [hq])
        rcases ih hXprocSubset with
          ⟨Q, hQsource, hQtarget, hQcarrier, hQinterior,
            hQForbidden, hQTerminalFinite, hQfirst, hQSubsingleton,
            hQCertificate, hQLocalization⟩
        rcases hEventData p hpXA with
          ⟨hRadius, hConvex, s, hsSegment, hpSegment, hBallModel⟩
        have hQsourceControl : Q.source ∈ EndpointControl := by
          simpa only [hQsource] using hPsourceControl
        have hQtargetControl : Q.target ∈ EndpointControl := by
          simpa only [hQtarget] using hPtargetControl
        rcases EndpointSidePrefixOneEventSplice Q SelectedSide H Bad
            Forbidden StartSector EndpointControl
            (predecessor.carrier ∪ approach.carrier ∪
              segment ℝ h terminalGate)
            K p (eventRadius p) s hSelectedOpen hQcarrier hQinterior
            hQForbidden hSelectedForbidden hKcarrier hKpoints
            hSelectedBad hQsourceControl hQtargetControl hQfirst
            hTerminalControl hQTerminalFinite (hBallControl p hpXA)
            hRadius hConvex hsSegment hpSegment hBallModel with
          ⟨Q', hQ'source, hQ'target, hQ'carrier, hQ'interior,
            hQ'Forbidden, hQ'TerminalFinite, hQ'first,
            hNewSubsingleton, hNewCertificate, hQ'Outside,
            hRetainedSegment, _⟩
        refine ⟨Q', hQ'source.trans hQsource, hQ'target.trans hQtarget,
          hQ'carrier, hQ'interior, hQ'Forbidden, hQ'TerminalFinite,
          hQ'first, ?_, ?_, ?_⟩
        · intro q hq
          rw [Finset.mem_insert] at hq
          rcases hq with hqp | hqProcessed
          · subst q
            exact hNewSubsingleton
          · have hqXA : q ∈ XA := hXprocSubset hqProcessed
            have hqp : q ≠ p := by
              intro h
              subst q
              exact hpNotProcessed hqProcessed
            have hDisjoint :=
              hBallPairwise q p hqXA hpXA hqp
            have hContactSubset :
                Q'.relativeInterior ∩ H ∩
                    Metric.ball q (eventRadius q) ⊆
                  Q.relativeInterior ∩ H ∩
                    Metric.ball q (eventRadius q) := by
              intro z hz
              have hzQ'Carrier : z ∈ Q'.carrier := by
                have hzInterior := hz.1.1
                rw [Q'.relativeInterior_eq] at hzInterior
                exact hzInterior.1
              have hzOutsideClosed :
                  z ∉ Metric.closedBall p (eventRadius p) := by
                intro hzClosed
                exact (Set.disjoint_left.mp hDisjoint
                  (Metric.ball_subset_closedBall hz.2)) hzClosed
              have hzQCarrier : z ∈ Q.carrier :=
                (hQ'Outside
                  ⟨hzQ'Carrier, fun hzBall =>
                    hzOutsideClosed
                      (Metric.ball_subset_closedBall hzBall)⟩).1
              have hzNotEndpointsQ' :
                  z ∉ ({Q'.source, Q'.target} :
                    Set (EuclideanSpace ℝ (Fin 2))) := by
                have hzInterior := hz.1.1
                rw [Q'.relativeInterior_eq] at hzInterior
                exact hzInterior.2
              have hzQInterior : z ∈ Q.relativeInterior := by
                rw [Q.relativeInterior_eq]
                refine ⟨hzQCarrier, ?_⟩
                simpa only [hQ'source, hQ'target] using hzNotEndpointsQ'
              exact ⟨⟨hzQInterior, hz.1.2⟩, hz.2⟩
            intro z hz w hw
            exact hQSubsingleton q hqProcessed
              (hContactSubset hz) (hContactSubset hw)
        · intro q hq z hzQ'Interior hzH hzBallQ
          rw [Finset.mem_insert] at hq
          rcases hq with hqp | hqProcessed
          · subst q
            rcases hNewCertificate z hzQ'Interior hzH hzBallQ with
              ⟨j, hj, hzOpen, hzOpenS, hNonparallel⟩
            exact ⟨j, hj, hzOpen, s, hsSegment, hzOpenS, hNonparallel⟩
          · have hqXA : q ∈ XA := hXprocSubset hqProcessed
            have hqp : q ≠ p := by
              intro h
              subst q
              exact hpNotProcessed hqProcessed
            have hDisjoint := hBallPairwise q p hqXA hpXA hqp
            have hzOutsideClosed :
                z ∉ Metric.closedBall p (eventRadius p) := by
              intro hzClosed
              exact (Set.disjoint_left.mp hDisjoint
                (Metric.ball_subset_closedBall hzBallQ)) hzClosed
            have hzQ'Carrier : z ∈ Q'.carrier := by
              rw [Q'.relativeInterior_eq] at hzQ'Interior
              exact hzQ'Interior.1
            have hzQCarrier : z ∈ Q.carrier :=
              (hQ'Outside
                ⟨hzQ'Carrier, fun hzBall =>
                  hzOutsideClosed
                    (Metric.ball_subset_closedBall hzBall)⟩).1
            have hzNotEndpointsQ' :
                z ∉ ({Q'.source, Q'.target} :
                  Set (EuclideanSpace ℝ (Fin 2))) := by
              rw [Q'.relativeInterior_eq] at hzQ'Interior
              exact hzQ'Interior.2
            have hzQInterior : z ∈ Q.relativeInterior := by
              rw [Q.relativeInterior_eq]
              refine ⟨hzQCarrier, ?_⟩
              simpa only [hQ'source, hQ'target] using hzNotEndpointsQ'
            rcases hQCertificate q hqProcessed z hzQInterior hzH hzBallQ with
              ⟨i, hi, hzOpenQ, t, htSegment, hzOpenT, hNonparallel⟩
            rcases hRetainedSegment z i hi hzOpenQ hzQ'Carrier
                hzOutsideClosed with
              ⟨j, hj, hzOpenQ', c, hc, hDirection⟩
            refine ⟨j, hj, hzOpenQ', t, htSegment, hzOpenT, ?_⟩
            rintro ⟨d, hd⟩
            apply hNonparallel
            refine ⟨d * c, ?_⟩
            rw [hDirection] at hd
            simpa only [smul_smul] using hd
        · intro z hz
          have hzOutsideCurrent : z ∉ Metric.ball p (eventRadius p) := by
            intro hzBall
            apply hz.2
            exact Set.mem_iUnion.mpr ⟨p,
              Set.mem_iUnion.mpr ⟨by simp, hzBall⟩⟩
          have hzQ : z ∈ Q.carrier \ Metric.ball p (eventRadius p) :=
            hQ'Outside ⟨hz.1, hzOutsideCurrent⟩
          have hzOutsideProcessed :
              z ∉ ⋃ q ∈
                  (Xproc : Set (EuclideanSpace ℝ (Fin 2))),
                    Metric.ball q (eventRadius q) := by
            intro hzUnion
            rcases Set.mem_iUnion.mp hzUnion with ⟨q, hzUnion⟩
            rcases Set.mem_iUnion.mp hzUnion with ⟨hqProcessed, hzBall⟩
            apply hz.2
            exact Set.mem_iUnion.mpr ⟨q,
              Set.mem_iUnion.mpr ⟨by simp [hqProcessed], hzBall⟩⟩
          have hzP := hQLocalization ⟨hzQ.1, hzOutsideProcessed⟩
          exact ⟨hzP.1, hz.2⟩
  rcases hInduction XA (fun _ hp => hp) with
    ⟨Pclean, hPcleanSource, hPcleanTarget, hPcleanCarrier,
      hPcleanInterior, hPcleanForbidden, hPcleanTerminalFinite,
      hPcleanFirst, hPcleanSubsingleton, hPcleanCertificate,
      hPcleanLocalization⟩
  refine ⟨Pclean, hPcleanSource, hPcleanTarget, hPcleanCarrier,
    hPcleanInterior, hPcleanForbidden, hPcleanTerminalFinite,
    hPcleanFirst, hPcleanSubsingleton, ?_, hPcleanLocalization⟩
  intro z hzInterior hzH
  have hzCover := hEventCover ⟨hPcleanInterior hzInterior, hzH⟩
  rcases Set.mem_iUnion.mp hzCover with ⟨p, hzCover⟩
  rcases Set.mem_iUnion.mp hzCover with ⟨hpXA, hzBall⟩
  exact hPcleanCertificate p hpXA z hzInterior hzH hzBall
