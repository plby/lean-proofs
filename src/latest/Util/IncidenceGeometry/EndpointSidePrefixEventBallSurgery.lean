import Util.IncidenceGeometry.EndpointSidePrefixEventInjectiveCharge
import Util.IncidenceGeometry.EndpointSidePrefixFiniteEventSplice

open Classical
noncomputable section

lemma EndpointSidePrefixEventBallSurgery
    (P predecessor approach : PolygonalArc)
    (SelectedSide H Rbeta Bad Forbidden StartSector EndpointControl :
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
        h ≠ terminalGate →
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
          StartSector ∩ H =
            (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
          (K.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Bad →
            SelectedSide ∩ (Rbeta ∪ Bad) =
              (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
              SelectedSide ∩ H ⊆
                ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
                  Metric.ball p (eventRadius p) →
                (∀ p : EuclideanSpace ℝ (Fin 2),
                    p ∈ XA →
                      0 < eventRadius p ∧
                        Convex ℝ
                          (SelectedSide ∩ Metric.ball p (eventRadius p)) ∧
                        ∃ s :
                          EuclideanSpace ℝ (Fin 2) ×
                            EuclideanSpace ℝ (Fin 2),
                          s ∈ K.segments ∧
                            p ∈ openSegment ℝ s.1 s.2 ∧
                              Metric.ball p (eventRadius p) ∩ H =
                                Metric.ball p (eventRadius p) ∩
                                  segment ℝ s.1 s.2 ∧
                              Metric.ball p (eventRadius p) ∩ Rbeta =
                                (∅ : Set (EuclideanSpace ℝ (Fin 2)))) →
                    (∀ p : EuclideanSpace ℝ (Fin 2),
                      p ∈ XA →
                        Disjoint
                          (Metric.closedBall p (eventRadius p))
                          EndpointControl) →
                    (∀ p q : EuclideanSpace ℝ (Fin 2),
                      p ∈ XA → q ∈ XA → p ≠ q →
                        Disjoint
                          (Metric.closedBall p (eventRadius p))
                          (Metric.closedBall q (eventRadius q))) →
      ∃ (Pclean : PolygonalArc)
          (xClean : Finset (EuclideanSpace ℝ (Fin 2)))
          (charge :
            EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
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
                      StartSector) ∧
                Pclean.vertices.Nodup ∧
                  (∀ ⦃i j : ℕ⦄,
                    (hi : i + 1 < Pclean.vertices.length) →
                      (hj : j + 1 < Pclean.vertices.length) →
                        i < j →
                          (segment ℝ Pclean.vertices[i] Pclean.vertices[i + 1] ∩
                              segment ℝ Pclean.vertices[j] Pclean.vertices[j + 1]) =
                            if j = i + 1 then {Pclean.vertices[j]} else ∅) ∧
                    (∀ ⦃i k : ℕ⦄,
                      (hi : i + 1 < Pclean.vertices.length) →
                        (hk : k < Pclean.vertices.length) →
                          k ≠ i → k ≠ i + 1 →
                            Pclean.vertices[k] ∉
                              openSegment ℝ
                                Pclean.vertices[i] Pclean.vertices[i + 1]) ∧
                  (∀ z : EuclideanSpace ℝ (Fin 2),
                    z ∈ xClean ↔ z ∈ Pclean.relativeInterior ∧ z ∈ H) ∧
                  (∀ z : EuclideanSpace ℝ (Fin 2),
                    z ∈ xClean →
                      charge z ∈ XA ∧
                        z ∈ Metric.ball (charge z) (eventRadius (charge z))) ∧
                  (∀ z w : EuclideanSpace ℝ (Fin 2),
                    z ∈ xClean → w ∈ xClean →
                      charge z = charge w → z = w) ∧
                  (∀ z : EuclideanSpace ℝ (Fin 2),
                    z ∈ xClean →
                      z ∉ Bad ∧
                        z ∉ (K.points : Set (EuclideanSpace ℝ (Fin 2))) ∧
                          ∃ j : ℕ,
                            ∃ hj : j + 1 < Pclean.vertices.length,
                              z ∈ openSegment ℝ
                                  Pclean.vertices[j] Pclean.vertices[j + 1] ∧
                                ∃! s :
                                  EuclideanSpace ℝ (Fin 2) ×
                                    EuclideanSpace ℝ (Fin 2),
                                  s ∈ K.segments ∧
                                    z ∈ openSegment ℝ s.1 s.2 ∧
                                      ¬ ∃ c : ℝ,
                                        s.2 - s.1 =
                                          c • (Pclean.vertices[j + 1] -
                                            Pclean.vertices[j])) ∧
                  Pclean.carrier \
                      (⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
                        Metric.ball p (eventRadius p)) ⊆
                    P.carrier \
                      (⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
                        Metric.ball p (eventRadius p)) := by
  intro hSideOpen hPCarrier hPInterior hPForbidden hSideForbidden hK
    _hGateNe hFiniteTerminal hSourceControl hTargetControl hFirst
    hTerminalControl _hStartH hKpoints hSideRbetaBad hSideH hEvent
    hEventControl hClosedBalls
  have hSideBad : SelectedSide ∩ Bad =
      (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext z
    constructor
    · rintro ⟨hzSide, hzBad⟩
      have hz : z ∈ SelectedSide ∩ (Rbeta ∪ Bad) :=
        ⟨hzSide, Or.inr hzBad⟩
      rw [hSideRbetaBad] at hz
      exact hz.elim
    · intro hz
      exact hz.elim
  have hLocalEvent : ∀ p : EuclideanSpace ℝ (Fin 2),
      p ∈ XA →
        0 < eventRadius p ∧
          Convex ℝ (SelectedSide ∩ Metric.ball p (eventRadius p)) ∧
          ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
            s ∈ K.segments ∧
              p ∈ openSegment ℝ s.1 s.2 ∧
              Metric.ball p (eventRadius p) ∩ H =
                Metric.ball p (eventRadius p) ∩ segment ℝ s.1 s.2 := by
    intro p hp
    rcases hEvent p hp with ⟨hradius, hconvex, s, hsK, hps, hlocal, _⟩
    exact ⟨hradius, hconvex, s, hsK, hps, hlocal⟩
  rcases EndpointSidePrefixFiniteEventSplice
      P predecessor approach SelectedSide H Bad Forbidden StartSector
      EndpointControl h terminalGate K XA eventRadius hSideOpen hPCarrier
      hPInterior hPForbidden hSideForbidden hK hFiniteTerminal hSourceControl
      hTargetControl hFirst hTerminalControl hKpoints hSideBad hSideH
      hLocalEvent hEventControl hClosedBalls with
    ⟨Pclean, hPcleanSource, hPcleanTarget, hPcleanCarrier,
      hPcleanInterior, hPcleanForbidden, hPcleanFiniteTerminal,
      hPcleanFirst, hAtMostOne, hContactSegment, hOutside⟩
  let X : Set (EuclideanSpace ℝ (Fin 2)) :=
    Pclean.relativeInterior ∩ H
  have hContactCover : X ⊆
      ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
        Metric.ball p (eventRadius p) := by
    intro z hz
    exact hSideH ⟨hPcleanInterior hz.1, hz.2⟩
  have hContactAtMost : ∀ p, p ∈ XA →
      (X ∩ Metric.ball p (eventRadius p)).Subsingleton := by
    intro p hp
    simpa [X] using hAtMostOne p hp
  have hContactCenter : ∀ z, z ∈ X →
      ∃ p, p ∈ XA ∧ z ∈ Metric.ball p (eventRadius p) := by
    intro z hz
    have hzcover := hContactCover hz
    simp only [Set.mem_iUnion] at hzcover
    rcases hzcover with ⟨p, hpXA, hpball⟩
    exact ⟨p, hpXA, hpball⟩
  rcases EndpointSidePrefixEventInjectiveCharge X XA eventRadius
      hContactCenter hContactAtMost with
    ⟨charge, hXFinite, hCharge, hChargeInjective⟩
  let xClean : Finset (EuclideanSpace ℝ (Fin 2)) := hXFinite.toFinset
  have hxClean : ∀ z : EuclideanSpace ℝ (Fin 2),
      z ∈ xClean ↔ z ∈ Pclean.relativeInterior ∧ z ∈ H := by
    intro z
    change z ∈ hXFinite.toFinset ↔ _
    rw [Set.Finite.mem_toFinset]
    rfl
  refine
    ⟨Pclean, xClean, charge, hPcleanSource, hPcleanTarget,
      hPcleanCarrier, hPcleanInterior, hPcleanForbidden,
      hPcleanFiniteTerminal, ?_, Pclean.simple_vertices,
      Pclean.segment_intersections, Pclean.vertices_avoid_nonincident_interiors,
      hxClean, ?_, ?_, ?_, hOutside⟩
  · rcases hPcleanFirst with ⟨hfirst, hcarrier, hopen, _⟩
    exact ⟨hfirst, hcarrier, hopen⟩
  · intro z hz
    have hzX : z ∈ X := (hxClean z).mp hz
    exact hCharge z hzX
  · intro z w hz hw heq
    exact hChargeInjective z w ((hxClean z).mp hz) ((hxClean w).mp hw) heq
  · intro z hz
    have hzX : z ∈ X := (hxClean z).mp hz
    have hzSide : z ∈ SelectedSide := hPcleanInterior hzX.1
    have hzNotBad : z ∉ Bad := by
      intro hzBad
      have hzEmpty : z ∈ SelectedSide ∩ Bad := ⟨hzSide, hzBad⟩
      rw [hSideBad] at hzEmpty
      exact hzEmpty.elim
    have hzNotPoints :
        z ∉ (K.points : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hzPoints
      exact hzNotBad (hKpoints hzPoints)
    rcases hContactSegment z hzX.1 hzX.2 with
      ⟨j, hj, hzPclean, s, hsK, hzs, hsDirection⟩
    refine ⟨hzNotBad, hzNotPoints, j, hj, hzPclean, ?_⟩
    refine ⟨s, ⟨hsK, hzs, hsDirection⟩, ?_⟩
    intro t ht
    by_contra hst
    have hzlisted := K.segment_intersections_listed s t hsK ht.1
        (Ne.symm hst) z
        (openSegment_subset_segment ℝ s.1 s.2 hzs)
        (openSegment_subset_segment ℝ t.1 t.2 ht.2.1)
    exact hzNotPoints hzlisted
