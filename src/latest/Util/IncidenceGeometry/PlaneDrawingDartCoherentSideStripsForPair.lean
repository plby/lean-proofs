import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.OrdinaryDrawingImageWithoutEdge
import Util.IncidenceGeometry.PlaneDrawingDartArcData
import Util.IncidenceGeometry.PlaneDrawingDartArcEndpointAwaySeparation
import Util.IncidenceGeometry.PlaneDrawingDartVertexSectorGeometry
import Util.IncidenceGeometry.PlaneDrawingDartVertexStarData
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeData
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import Util.IncidenceGeometry.PolygonalArcCollarControlRadiiExistsBelow
import Util.IncidenceGeometry.PolygonalArcInitialEndpointDiskCappedTaperSideLabelling
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideData
import Util.IncidenceGeometry.PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones
import Util.IncidenceGeometry.PolygonalArcCollarMiddleForbiddenMarginsExists
import Util.IncidenceGeometry.PolygonalArcCollarMiddleSegmentDataExists
import Util.IncidenceGeometry.PolygonalArcCollarVertexLocalPieceData
import Util.IncidenceGeometry.PolygonalArcEndpointIsolation
import Util.IncidenceGeometry.PolygonalArcEndpointIsolationExists
import Util.IncidenceGeometry.PolygonalArcEndpointLeftHalfTubeSubsetLeftCones
import Util.IncidenceGeometry.PolygonalArcInitialEndpointLeftCone
import Util.IncidenceGeometry.PolygonalArcSideStripAssembly
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointLeftCone
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.PolygonalSideStripsReverseOfSameCarrier
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Classical
noncomputable section


lemma PlaneDrawingDartCoherentSideStripsForPair {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) (d : G.Dart) :
    ∃ S : PolygonalSideStrips (A.dartArc d),
      ∃ T : PolygonalSideStrips (A.dartArc d.symm),
        S.rightStrip = T.leftStrip ∧
          T.rightStrip = S.leftStrip ∧
            S.leftStrip.Nonempty ∧
              T.leftStrip.Nonempty ∧
                S.leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                  T.leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                    (∀ x : EuclideanSpace ℝ (Fin 2),
                      x ∈ (A.dartArc d).relativeInterior →
                        ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
                          IsOpen U ∧ x ∈ U ∧
                            U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
                              S.leftStrip ∪ T.leftStrip) ∧
                      (∀ x : EuclideanSpace ℝ (Fin 2),
                        x ∈ (A.dartArc d.symm).relativeInterior →
                          ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
                            IsOpen U ∧ x ∈ U ∧
                              U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
                                T.leftStrip ∪ S.leftStrip) ∧
                        (C.successorSector d ∩ S.leftStrip ∩
                          Metric.ball (D.vertexPlacement d.toProd.2)
                            (C.star.localDiskRadius d.toProd.2)).Nonempty ∧
                          (C.successorSector d.symm ∩ T.leftStrip ∩
                            Metric.ball (D.vertexPlacement d.symm.toProd.2)
                              (C.star.localDiskRadius d.symm.toProd.2)).Nonempty ∧
                            (∀ p : G.Dart, C.star.successor p = d →
                              (C.successorSector p ∩ S.leftStrip ∩
                                Metric.ball (D.vertexPlacement p.toProd.2)
                                  (C.star.localDiskRadius p.toProd.2)).Nonempty) ∧
                              (∀ p : G.Dart, C.star.successor p = d.symm →
                                (C.successorSector p ∩ T.leftStrip ∩
                                  Metric.ball (D.vertexPlacement p.toProd.2)
                                    (C.star.localDiskRadius p.toProd.2)).Nonempty) := by
  let γ : PolygonalArc := A.dartArc d
  obtain ⟨rT, KT, hrT, hKT, hterm⟩ :=
    C.terminal_left_endpoint_sector_access d
  obtain ⟨rTs, KTs, hrTs, hKTs, hterm_symm⟩ :=
    C.terminal_left_endpoint_sector_access d.symm
  let pd : G.Dart := C.star.successor.symm d
  have hpd_succ : C.star.successor pd = d := by
    dsimp [pd]
    exact Equiv.apply_symm_apply C.star.successor d
  obtain ⟨rI, KI, hrI, hKI, hinit_raw⟩ :=
    C.successor_initial_left_endpoint_sector_access pd
  have hinit :
      PolygonalArcInitialEndpointLeftCone (A.dartArc d) rI KI ⊆
        C.successorSector pd := by
    simpa [hpd_succ] using hinit_raw
  let pds : G.Dart := C.star.successor.symm d.symm
  have hpds_succ : C.star.successor pds = d.symm := by
    dsimp [pds]
    exact Equiv.apply_symm_apply C.star.successor d.symm
  obtain ⟨rIs, KIs, hrIs, hKIs, hinit_symm_raw⟩ :=
    C.successor_initial_left_endpoint_sector_access pds
  have hinit_symm :
      PolygonalArcInitialEndpointLeftCone (A.dartArc d.symm) rIs KIs ⊆
        C.successorSector pds := by
    simpa [hpds_succ] using hinit_symm_raw
  obtain ⟨rIso0, rIso1, hIsoBase⟩ := PolygonalArcEndpointIsolationExists γ
  let r0min : ℝ :=
    min rIso0 (min rI (min rTs (C.star.localDiskRadius d.toProd.1)))
  let r1min : ℝ :=
    min rIso1 (min rT (min rIs (C.star.localDiskRadius d.toProd.2)))
  let r0 : ℝ := r0min / 2
  let r1 : ℝ := r1min / 2
  have hr0min_pos : 0 < r0min := by
    dsimp [r0min]
    exact lt_min hIsoBase.source_pos
      (lt_min hrI (lt_min hrTs (C.star.localDiskRadius_pos d.toProd.1)))
  have hr1min_pos : 0 < r1min := by
    dsimp [r1min]
    exact lt_min hIsoBase.target_pos
      (lt_min hrT (lt_min hrIs (C.star.localDiskRadius_pos d.toProd.2)))
  have hr0 : 0 < r0 := by
    dsimp [r0]
    linarith
  have hr1 : 0 < r1 := by
    dsimp [r1]
    linarith
  have hr0_le_iso : r0 ≤ rIso0 := by
    dsimp [r0]
    have hle : r0min ≤ rIso0 := by
      dsimp [r0min]
      exact min_le_left _ _
    linarith
  have hr1_le_iso : r1 ≤ rIso1 := by
    dsimp [r1]
    have hle : r1min ≤ rIso1 := by
      dsimp [r1min]
      exact min_le_left _ _
    linarith
  have hr0_lt_iso : r0 < rIso0 := by
    have hpos := hIsoBase.source_pos
    have hle := hr0_le_iso
    by_cases heq : r0 = rIso0
    · have : r0min ≤ rIso0 := by
        dsimp [r0min]
        exact min_le_left _ _
      dsimp [r0] at heq
      nlinarith [hr0min_pos]
    · exact lt_of_le_of_ne hle heq
  have hr1_lt_iso : r1 < rIso1 := by
    have hle := hr1_le_iso
    by_cases heq : r1 = rIso1
    · have : r1min ≤ rIso1 := by
        dsimp [r1min]
        exact min_le_left _ _
      dsimp [r1] at heq
      nlinarith [hr1min_pos]
    · exact lt_of_le_of_ne hle heq
  have hr0_lt_rI : r0 < rI := by
    dsimp [r0]
    have hle : r0min ≤ rI := by
      dsimp [r0min]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith [hr0min_pos]
  have hr0_lt_rTs : r0 < rTs := by
    dsimp [r0]
    have hle : r0min ≤ rTs := by
      dsimp [r0min]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    nlinarith [hr0min_pos]
  have hr0_lt_local_source :
      r0 < C.star.localDiskRadius d.toProd.1 := by
    dsimp [r0]
    have hle : r0min ≤ C.star.localDiskRadius d.toProd.1 := by
      dsimp [r0min]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))
    nlinarith [hr0min_pos]
  have hr1_lt_rT : r1 < rT := by
    dsimp [r1]
    have hle : r1min ≤ rT := by
      dsimp [r1min]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith [hr1min_pos]
  have hr1_lt_rIs : r1 < rIs := by
    dsimp [r1]
    have hle : r1min ≤ rIs := by
      dsimp [r1min]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    nlinarith [hr1min_pos]
  have hr1_lt_local_target :
      r1 < C.star.localDiskRadius d.toProd.2 := by
    dsimp [r1]
    have hle : r1min ≤ C.star.localDiskRadius d.toProd.2 := by
      dsimp [r1min]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))
    nlinarith [hr1min_pos]
  let K0min : ℝ := min KI KTs
  let K1min : ℝ := min KT KIs
  let K0 : ℝ := K0min / 2
  let K1 : ℝ := K1min / 2
  have hK0min_pos : 0 < K0min := by
    dsimp [K0min]
    exact lt_min hKI hKTs
  have hK1min_pos : 0 < K1min := by
    dsimp [K1min]
    exact lt_min hKT hKIs
  have hK0 : 0 < K0 := by
    dsimp [K0]
    linarith
  have hK1 : 0 < K1 := by
    dsimp [K1]
    linarith
  have hK0_lt_KI : K0 < KI := by
    dsimp [K0]
    have hle : K0min ≤ KI := by
      dsimp [K0min]
      exact min_le_left _ _
    nlinarith [hK0min_pos]
  have hK0_lt_KTs : K0 < KTs := by
    dsimp [K0]
    have hle : K0min ≤ KTs := by
      dsimp [K0min]
      exact min_le_right _ _
    nlinarith [hK0min_pos]
  have hK1_lt_KT : K1 < KT := by
    dsimp [K1]
    have hle : K1min ≤ KT := by
      dsimp [K1min]
      exact min_le_left _ _
    nlinarith [hK1min_pos]
  have hK1_lt_KIs : K1 < KIs := by
    dsimp [K1]
    have hle : K1min ≤ KIs := by
      dsimp [K1min]
      exact min_le_right _ _
    nlinarith [hK1min_pos]
  have hIso : PolygonalArcEndpointIsolation γ r0 r1 := by
    refine
      { source_pos := hr0
        target_pos := hr1
        source_lt_initial_length := lt_of_lt_of_le hr0_lt_iso
          (le_of_lt hIsoBase.source_lt_initial_length)
        target_lt_terminal_length := lt_of_lt_of_le hr1_lt_iso
          (le_of_lt hIsoBase.target_lt_terminal_length)
        endpoint_closedBalls_disjoint := ?_
        source_closedBall_carrier_subset_initial_segment := ?_
        target_closedBall_carrier_subset_terminal_segment := ?_ }
    · exact Disjoint.mono
        (by
          intro x hx
          rw [Metric.mem_closedBall] at hx ⊢
          exact le_trans hx hr0_le_iso)
        (by
          intro x hx
          rw [Metric.mem_closedBall] at hx ⊢
          exact le_trans hx hr1_le_iso)
        hIsoBase.endpoint_closedBalls_disjoint
    · change
        Metric.closedBall γ.source r0 ∩ γ.carrier ⊆
          segment ℝ γ.source
            (γ.vertices[1]'(Nat.lt_of_succ_le γ.length_ge_two))
      intro x hx
      exact hIsoBase.source_closedBall_carrier_subset_initial_segment
        ⟨by
          have hxball : x ∈ Metric.closedBall γ.source r0 := hx.1
          rw [Metric.mem_closedBall] at hxball ⊢
          exact le_trans hxball hr0_le_iso, hx.2⟩
    · let hprev : γ.vertices.length - 2 < γ.vertices.length := by
        have hlen := γ.length_ge_two
        omega
      change
        Metric.closedBall γ.target r1 ∩ γ.carrier ⊆
          segment ℝ γ.target (γ.vertices[γ.vertices.length - 2]'hprev)
      intro x hx
      exact hIsoBase.target_closedBall_carrier_subset_terminal_segment
        ⟨by
          have hxball : x ∈ Metric.closedBall γ.target r1 := hx.1
          rw [Metric.mem_closedBall] at hxball ⊢
          exact le_trans hxball hr1_le_iso, hx.2⟩
  obtain ⟨δaway, hδaway_pos, hδaway⟩ :=
    PlaneDrawingDartArcEndpointAwaySeparation G D hD A d r0 r1 hr0 hr1
  let η : ℝ := min δaway (min r0 r1) / 2
  have hηpos : 0 < η := by
    dsimp [η]
    have hminpos : 0 < min δaway (min r0 r1) :=
      lt_min hδaway_pos (lt_min hr0 hr1)
    linarith
  have hη_lt_away : η < δaway := by
    dsimp [η]
    have hminpos : 0 < min δaway (min r0 r1) :=
      lt_min hδaway_pos (lt_min hr0 hr1)
    have hle : min δaway (min r0 r1) ≤ δaway := min_le_left _ _
    nlinarith
  have hη_lt_r0 : η < r0 := by
    dsimp [η]
    have hminpos : 0 < min δaway (min r0 r1) :=
      lt_min hδaway_pos (lt_min hr0 hr1)
    have hle : min δaway (min r0 r1) ≤ r0 := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith
  have hη_lt_r1 : η < r1 := by
    dsimp [η]
    have hminpos : 0 < min δaway (min r0 r1) :=
      lt_min hδaway_pos (lt_min hr0 hr1)
    have hle : min δaway (min r0 r1) ≤ r1 := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    nlinarith
  obtain ⟨controlRadii, hρ0_lt, hρ1_lt, hsourceBalls, htargetBalls⟩ :=
    PolygonalArcCollarControlRadiiExistsBelow γ η r0 r1 hηpos hr0 hr1 hIso
  obtain ⟨middleSegments⟩ :=
    PolygonalArcCollarMiddleSegmentDataExists γ controlRadii
  obtain ⟨forbiddenMargins⟩ :=
    PolygonalArcCollarMiddleForbiddenMarginsExists γ controlRadii middleSegments
  obtain ⟨compatibleTubes, hKinit_lt, hKterm_lt, htube_source, htube_target⟩ :=
    PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow γ controlRadii
      middleSegments forbiddenMargins r0 r1 K0 K1 hIso hK0 hK1
  let hsource : 0 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  let hfirst : 0 + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  let itarget : ℕ := γ.vertices.length - 1
  let htarget : itarget < γ.vertices.length := by
    have hlen := γ.length_ge_two
    dsimp [itarget]
    omega
  let jlast : ℕ := γ.vertices.length - 2
  let hlast : jlast + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    dsimp [jlast]
    omega
  obtain ⟨vertexLocalPieces, localSideData, hsource_omit, htarget_omit,
      hsource_cone, htarget_cone, hsource_disj, htarget_disj,
      hleft_source_cone, hleft_target_cone, hright_source_cone,
      hright_target_cone⟩ :=
    PolygonalArcCollarLocalSideDataExistsWithEndpointLeftCones γ controlRadii
      middleSegments forbiddenMargins compatibleTubes r0 r1 K0 K1 hr0 hr1 hK0 hK1
      hρ0_lt hρ1_lt hKinit_lt hKterm_lt hsourceBalls htargetBalls
  obtain ⟨S, hS_collar, hS_left, hS_right, hS_eta⟩ :=
    PolygonalArcSideStripAssembly γ controlRadii middleSegments forbiddenMargins
      compatibleTubes.orientedTubes vertexLocalPieces localSideData
  have hδ_carrier : (A.dartArc d.symm).carrier = γ.carrier := by
    rw [A.dartArc_symm_eq_reverse d]
    simp [γ, PolygonalArcReverse]
  have hδ_source : (A.dartArc d.symm).source = γ.target := by
    rw [A.dartArc_symm_eq_reverse d]
    simp [γ, PolygonalArcReverse]
  have hδ_target : (A.dartArc d.symm).target = γ.source := by
    rw [A.dartArc_symm_eq_reverse d]
    simp [γ, PolygonalArcReverse]
  obtain ⟨T, hT_left, hT_right⟩ :=
    PolygonalSideStripsReverseOfSameCarrier γ (A.dartArc d.symm) S hδ_carrier
      hδ_source hδ_target
  have initialCone_mono :
      ∀ (β : PolygonalArc) (r r' K K' : ℝ),
        0 ≤ r →
          r ≤ r' →
            K ≤ K' →
              0 < PolygonalArcInitialEndpointSegmentLength β →
                PolygonalArcInitialEndpointLeftCone β r K ⊆
                  PolygonalArcInitialEndpointLeftCone β r' K' := by
    intro β r r' K K' hr_nonneg hrr hKK hlen_pos q hq
    rw [PolygonalArcInitialEndpointLeftCone] at hq ⊢
    dsimp at hq ⊢
    rcases hq with ⟨z, hz, rfl⟩
    rcases hz with ⟨hz0, hzrad, hz1pos, hz1lt⟩
    refine ⟨z, ?_, rfl⟩
    refine ⟨hz0, ?_, hz1pos, ?_⟩
    · let denom : ℝ :=
        dist β.source (β.vertices[1]'(Nat.lt_of_succ_le β.length_ge_two))
      have hdenom_pos : 0 < denom := by
        dsimp [denom]
        simpa [PolygonalArcInitialEndpointSegmentLength] using hlen_pos
      have hdenom_nonneg : 0 ≤ denom := le_of_lt hdenom_pos
      have hdiv_le : r / denom ≤ r' / denom :=
        div_le_div_of_nonneg_right hrr hdenom_nonneg
      have hdiv_nonneg : 0 ≤ r / denom :=
        div_nonneg hr_nonneg hdenom_nonneg
      have hsquare_le : (r / denom) ^ 2 ≤ (r' / denom) ^ 2 :=
        pow_le_pow_left₀ hdiv_nonneg hdiv_le 2
      exact lt_of_lt_of_le hzrad (by simpa [denom] using hsquare_le)
    · have hz0_nonneg : 0 ≤ z 0 := le_of_lt hz0
      exact lt_of_lt_of_le hz1lt
        (mul_le_mul_of_nonneg_right hKK hz0_nonneg)
  have terminalCone_mono :
      ∀ (β : PolygonalArc) (r r' K K' : ℝ),
        0 ≤ r →
          r ≤ r' →
            K ≤ K' →
              0 < PolygonalArcTerminalEndpointSegmentLength β →
                PolygonalArcTerminalEndpointLeftCone β r K ⊆
                  PolygonalArcTerminalEndpointLeftCone β r' K' := by
    intro β r r' K K' hr_nonneg hrr hKK hlen_pos q hq
    rw [PolygonalArcTerminalEndpointLeftCone] at hq ⊢
    dsimp at hq ⊢
    rcases hq with ⟨z, hz, rfl⟩
    rcases hz with ⟨hz0, hzrad, hz1low, hz1neg⟩
    refine ⟨z, ?_, rfl⟩
    refine ⟨hz0, ?_, ?_, hz1neg⟩
    · let hprev : β.vertices.length - 2 < β.vertices.length := by
        have hlen := β.length_ge_two
        omega
      let denom : ℝ := dist β.target (β.vertices[β.vertices.length - 2]'hprev)
      have hdenom_pos : 0 < denom := by
        dsimp [denom]
        simpa [PolygonalArcTerminalEndpointSegmentLength, hprev] using hlen_pos
      have hdenom_nonneg : 0 ≤ denom := le_of_lt hdenom_pos
      have hdiv_le : r / denom ≤ r' / denom :=
        div_le_div_of_nonneg_right hrr hdenom_nonneg
      have hdiv_nonneg : 0 ≤ r / denom :=
        div_nonneg hr_nonneg hdenom_nonneg
      have hsquare_le : (r / denom) ^ 2 ≤ (r' / denom) ^ 2 :=
        pow_le_pow_left₀ hdiv_nonneg hdiv_le 2
      exact lt_of_lt_of_le hzrad (by simpa [denom] using hsquare_le)
    · have hz0_nonneg : 0 ≤ z 0 := le_of_lt hz0
      have hneg := neg_le_neg (mul_le_mul_of_nonneg_right hKK hz0_nonneg)
      exact lt_of_le_of_lt (by simpa only [neg_mul] using hneg) hz1low
  have hγ_initial_len_pos : 0 < PolygonalArcInitialEndpointSegmentLength γ :=
    lt_trans hIso.source_pos hIso.source_lt_initial_length
  have hγ_terminal_len_pos : 0 < PolygonalArcTerminalEndpointSegmentLength γ :=
    lt_trans hIso.target_pos hIso.target_lt_terminal_length
  obtain ⟨_, _, hIsoSymmAny⟩ := PolygonalArcEndpointIsolationExists (A.dartArc d.symm)
  have hsymm_initial_len_pos :
      0 < PolygonalArcInitialEndpointSegmentLength (A.dartArc d.symm) :=
    lt_trans hIsoSymmAny.source_pos hIsoSymmAny.source_lt_initial_length
  have hsymm_terminal_len_pos :
      0 < PolygonalArcTerminalEndpointSegmentLength (A.dartArc d.symm) :=
    lt_trans hIsoSymmAny.target_pos hIsoSymmAny.target_lt_terminal_length
  have hHalfCones :=
    PolygonalArcEndpointLeftHalfTubeSubsetLeftCones γ controlRadii middleSegments
      forbiddenMargins compatibleTubes r0 r1 K0 K1 hIso hK0 hK1 hfirst hlast
      hKinit_lt hKterm_lt
  have image_without_of_not_carrier :
      ∀ y : EuclideanSpace ℝ (Fin 2),
        y ∈ OrdinaryDrawingImage G D →
          y ∉ γ.carrier →
            y ∈ OrdinaryDrawingImageWithoutEdge G D (A.dartEdge d) := by
    intro y hyimg hynot_carrier
    rw [OrdinaryDrawingImage] at hyimg
    rw [OrdinaryDrawingImageWithoutEdge]
    rcases hyimg with hyvertex | hyedge
    · exact Or.inl hyvertex
    · rcases Set.mem_iUnion.1 hyedge with ⟨e, hye⟩
      by_cases he : e = A.dartEdge d
      · exfalso
        exact hynot_carrier (by simpa [γ, he, A.dartArc_carrier d] using hye)
      · right
        exact Set.mem_iUnion.2 ⟨⟨e, he⟩, hye⟩
  have outside_complement
      (Y : Set (EuclideanSpace ℝ (Fin 2))) (hY_collar : Y ⊆ S.collar)
      (hY_disjoint : Disjoint Y γ.carrier) :
      ∀ y : EuclideanSpace ℝ (Fin 2),
        y ∈ Y →
          y ∉ Metric.ball γ.source r0 →
            y ∉ Metric.ball γ.target r1 →
              y ∈ (OrdinaryDrawingImage G D)ᶜ := by
    intro y hyY hnot_source hnot_target hyimg
    have hynot_carrier : y ∉ γ.carrier := by
      intro hycarrier
      exact (Set.disjoint_left.mp hY_disjoint hyY) hycarrier
    have hy_without : y ∈ OrdinaryDrawingImageWithoutEdge G D (A.dartEdge d) :=
      image_without_of_not_carrier y hyimg hynot_carrier
    have hnot_balls :
        y ∉ Metric.ball (A.dartArc d).source r0 ∪
          Metric.ball (A.dartArc d).target r1 := by
      intro hyballs
      rcases hyballs with hy_source | hy_target
      · exact hnot_source (by simpa [γ] using hy_source)
      · exact hnot_target (by simpa [γ] using hy_target)
    rcases hS_eta y (hY_collar hyY) with ⟨p, hp_carrier, hyp_lt⟩
    have hsep := hδaway y hy_without hnot_balls p (by simpa [γ] using hp_carrier)
    linarith
  have left_source_complement :
      ∀ y : EuclideanSpace ℝ (Fin 2),
        y ∈ S.leftStrip →
          y ∈ Metric.ball γ.source r0 →
            y ∈ (OrdinaryDrawingImage G D)ᶜ := by
    intro y hyS hyball
    rw [hS_left] at hyS
    rcases hyS with hyHalf | hyPiece
    · rcases Set.mem_iUnion.1 hyHalf with ⟨j, hyj⟩
      rcases Set.mem_iUnion.1 hyj with ⟨hj, hyLeftHalf⟩
      by_cases hj0 : j = 0
      · subst j
        have hy_cone_small :
            y ∈ PolygonalArcInitialEndpointLeftCone γ r0 K0 :=
          hHalfCones.1 ⟨hyLeftHalf, hyball⟩
        have hy_cone : y ∈ PolygonalArcInitialEndpointLeftCone (A.dartArc d) rI KI := by
          have hy_large :=
            initialCone_mono γ r0 rI K0 KI (le_of_lt hr0) (le_of_lt hr0_lt_rI)
              (le_of_lt hK0_lt_KI) hγ_initial_len_pos hy_cone_small
          simpa [γ] using hy_large
        exact C.successorSector_subset_complement pd (hinit hy_cone)
      · have hytube : y ∈ compatibleTubes.orientedTubes.tube j hj :=
          compatibleTubes.orientedTubes.leftHalf_subset_tube j hj hyLeftHalf
        exact False.elim ((Set.disjoint_left.mp (htube_source j hj hj0) hytube) hyball)
    · rcases Set.mem_iUnion.1 hyPiece with ⟨i, hyPiecei⟩
      by_cases hi0 : i.1 = 0
      · have hi : i = ⟨0, hsource⟩ := by
          apply Fin.ext
          exact hi0
        have hy_cone_small :
            y ∈ PolygonalArcInitialEndpointLeftCone γ r0 K0 := by
          exact hleft_source_cone (by simpa [hi] using hyPiecei)
        have hy_cone : y ∈ PolygonalArcInitialEndpointLeftCone (A.dartArc d) rI KI := by
          have hy_large :=
            initialCone_mono γ r0 rI K0 KI (le_of_lt hr0) (le_of_lt hr0_lt_rI)
              (le_of_lt hK0_lt_KI) hγ_initial_len_pos hy_cone_small
          simpa [γ] using hy_large
        exact C.successorSector_subset_complement pd (hinit hy_cone)
      · have hycollar : y ∈ localSideData.vertexCollar i :=
          localSideData.leftSidePiece_subset_vertexCollar i hyPiecei
        exact False.elim ((Set.disjoint_left.mp (hsource_disj i hi0) hycollar) hyball)
  have left_target_complement :
      ∀ y : EuclideanSpace ℝ (Fin 2),
        y ∈ S.leftStrip →
          y ∈ Metric.ball γ.target r1 →
            y ∈ (OrdinaryDrawingImage G D)ᶜ := by
    intro y hyS hyball
    rw [hS_left] at hyS
    rcases hyS with hyHalf | hyPiece
    · rcases Set.mem_iUnion.1 hyHalf with ⟨j, hyj⟩
      rcases Set.mem_iUnion.1 hyj with ⟨hj, hyLeftHalf⟩
      by_cases hjlast : j = jlast
      · subst j
        have hy_cone_small :
            y ∈ PolygonalArcTerminalEndpointLeftCone γ r1 K1 :=
          hHalfCones.2.1 ⟨by simpa [jlast] using hyLeftHalf, hyball⟩
        have hy_cone : y ∈ PolygonalArcTerminalEndpointLeftCone (A.dartArc d) rT KT := by
          have hy_large :=
            terminalCone_mono γ r1 rT K1 KT (le_of_lt hr1) (le_of_lt hr1_lt_rT)
              (le_of_lt hK1_lt_KT) hγ_terminal_len_pos hy_cone_small
          simpa [γ] using hy_large
        exact C.successorSector_subset_complement d (hterm hy_cone)
      · have hytube : y ∈ compatibleTubes.orientedTubes.tube j hj :=
          compatibleTubes.orientedTubes.leftHalf_subset_tube j hj hyLeftHalf
        have hdisj := htube_target j hj (by simpa [jlast] using hjlast)
        exact False.elim ((Set.disjoint_left.mp hdisj hytube) hyball)
    · rcases Set.mem_iUnion.1 hyPiece with ⟨i, hyPiecei⟩
      by_cases hitarget : i.1 + 1 = γ.vertices.length
      · have hi : i = ⟨itarget, htarget⟩ := by
          apply Fin.ext
          dsimp [itarget]
          omega
        have hy_cone_small :
            y ∈ PolygonalArcTerminalEndpointLeftCone γ r1 K1 :=
          hleft_target_cone (by simpa [hi] using hyPiecei)
        have hy_cone : y ∈ PolygonalArcTerminalEndpointLeftCone (A.dartArc d) rT KT := by
          have hy_large :=
            terminalCone_mono γ r1 rT K1 KT (le_of_lt hr1) (le_of_lt hr1_lt_rT)
              (le_of_lt hK1_lt_KT) hγ_terminal_len_pos hy_cone_small
          simpa [γ] using hy_large
        exact C.successorSector_subset_complement d (hterm hy_cone)
      · have hycollar : y ∈ localSideData.vertexCollar i :=
          localSideData.leftSidePiece_subset_vertexCollar i hyPiecei
        exact False.elim ((Set.disjoint_left.mp (htarget_disj i hitarget) hycollar) hyball)
  have right_source_complement :
      ∀ y : EuclideanSpace ℝ (Fin 2),
        y ∈ S.rightStrip →
          y ∈ Metric.ball γ.source r0 →
            y ∈ (OrdinaryDrawingImage G D)ᶜ := by
    intro y hyS hyball
    rw [hS_right] at hyS
    rcases hyS with hyHalf | hyPiece
    · rcases Set.mem_iUnion.1 hyHalf with ⟨j, hyj⟩
      rcases Set.mem_iUnion.1 hyj with ⟨hj, hyRightHalf⟩
      by_cases hj0 : j = 0
      · subst j
        have hy_cone_small :
            y ∈ PolygonalArcTerminalEndpointLeftCone (A.dartArc d.symm) r0 K0 := by
          have hy_rev : y ∈ PolygonalArcTerminalEndpointLeftCone
              (PolygonalArcReverse γ) r0 K0 :=
            hHalfCones.2.2.1 ⟨hyRightHalf, hyball⟩
          simpa [γ, A.dartArc_symm_eq_reverse d] using hy_rev
        have hy_cone :
            y ∈ PolygonalArcTerminalEndpointLeftCone (A.dartArc d.symm) rTs KTs :=
          terminalCone_mono (A.dartArc d.symm) r0 rTs K0 KTs (le_of_lt hr0)
            (le_of_lt hr0_lt_rTs) (le_of_lt hK0_lt_KTs) hsymm_terminal_len_pos
            hy_cone_small
        exact C.successorSector_subset_complement d.symm (hterm_symm hy_cone)
      · have hytube : y ∈ compatibleTubes.orientedTubes.tube j hj :=
          compatibleTubes.orientedTubes.rightHalf_subset_tube j hj hyRightHalf
        exact False.elim ((Set.disjoint_left.mp (htube_source j hj hj0) hytube) hyball)
    · rcases Set.mem_iUnion.1 hyPiece with ⟨i, hyPiecei⟩
      by_cases hi0 : i.1 = 0
      · have hi : i = ⟨0, hsource⟩ := by
          apply Fin.ext
          exact hi0
        have hy_cone_small :
            y ∈ PolygonalArcTerminalEndpointLeftCone (A.dartArc d.symm) r0 K0 := by
          have hy_rev : y ∈ PolygonalArcTerminalEndpointLeftCone
              (PolygonalArcReverse γ) r0 K0 :=
            hright_source_cone (by simpa [hi] using hyPiecei)
          simpa [γ, A.dartArc_symm_eq_reverse d] using hy_rev
        have hy_cone :
            y ∈ PolygonalArcTerminalEndpointLeftCone (A.dartArc d.symm) rTs KTs :=
          terminalCone_mono (A.dartArc d.symm) r0 rTs K0 KTs (le_of_lt hr0)
            (le_of_lt hr0_lt_rTs) (le_of_lt hK0_lt_KTs) hsymm_terminal_len_pos
            hy_cone_small
        exact C.successorSector_subset_complement d.symm (hterm_symm hy_cone)
      · have hycollar : y ∈ localSideData.vertexCollar i :=
          localSideData.rightSidePiece_subset_vertexCollar i hyPiecei
        exact False.elim ((Set.disjoint_left.mp (hsource_disj i hi0) hycollar) hyball)
  have right_target_complement :
      ∀ y : EuclideanSpace ℝ (Fin 2),
        y ∈ S.rightStrip →
          y ∈ Metric.ball γ.target r1 →
            y ∈ (OrdinaryDrawingImage G D)ᶜ := by
    intro y hyS hyball
    rw [hS_right] at hyS
    rcases hyS with hyHalf | hyPiece
    · rcases Set.mem_iUnion.1 hyHalf with ⟨j, hyj⟩
      rcases Set.mem_iUnion.1 hyj with ⟨hj, hyRightHalf⟩
      by_cases hjlast : j = jlast
      · subst j
        have hy_cone_small :
            y ∈ PolygonalArcInitialEndpointLeftCone (A.dartArc d.symm) r1 K1 := by
          have hy_rev : y ∈ PolygonalArcInitialEndpointLeftCone
              (PolygonalArcReverse γ) r1 K1 :=
            hHalfCones.2.2.2 ⟨by simpa [jlast] using hyRightHalf, hyball⟩
          simpa [γ, A.dartArc_symm_eq_reverse d] using hy_rev
        have hy_cone :
            y ∈ PolygonalArcInitialEndpointLeftCone (A.dartArc d.symm) rIs KIs :=
          initialCone_mono (A.dartArc d.symm) r1 rIs K1 KIs (le_of_lt hr1)
            (le_of_lt hr1_lt_rIs) (le_of_lt hK1_lt_KIs) hsymm_initial_len_pos
            hy_cone_small
        exact C.successorSector_subset_complement pds (hinit_symm hy_cone)
      · have hytube : y ∈ compatibleTubes.orientedTubes.tube j hj :=
          compatibleTubes.orientedTubes.rightHalf_subset_tube j hj hyRightHalf
        have hdisj := htube_target j hj (by simpa [jlast] using hjlast)
        exact False.elim ((Set.disjoint_left.mp hdisj hytube) hyball)
    · rcases Set.mem_iUnion.1 hyPiece with ⟨i, hyPiecei⟩
      by_cases hitarget : i.1 + 1 = γ.vertices.length
      · have hi : i = ⟨itarget, htarget⟩ := by
          apply Fin.ext
          dsimp [itarget]
          omega
        have hy_cone_small :
            y ∈ PolygonalArcInitialEndpointLeftCone (A.dartArc d.symm) r1 K1 := by
          have hy_rev : y ∈ PolygonalArcInitialEndpointLeftCone
              (PolygonalArcReverse γ) r1 K1 :=
            hright_target_cone (by simpa [hi] using hyPiecei)
          simpa [γ, A.dartArc_symm_eq_reverse d] using hy_rev
        have hy_cone :
            y ∈ PolygonalArcInitialEndpointLeftCone (A.dartArc d.symm) rIs KIs :=
          initialCone_mono (A.dartArc d.symm) r1 rIs K1 KIs (le_of_lt hr1)
            (le_of_lt hr1_lt_rIs) (le_of_lt hK1_lt_KIs) hsymm_initial_len_pos
            hy_cone_small
        exact C.successorSector_subset_complement pds (hinit_symm hy_cone)
      · have hycollar : y ∈ localSideData.vertexCollar i :=
          localSideData.rightSidePiece_subset_vertexCollar i hyPiecei
        exact False.elim ((Set.disjoint_left.mp (htarget_disj i hitarget) hycollar) hyball)
  refine ⟨S, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hT_left.symm
  · exact hT_right
  · rcases vertexLocalPieces.outgoingLeftAttachment_nonempty 0 hfirst with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hS_left]
    right
    exact Set.mem_iUnion.2
      ⟨⟨0, Nat.lt_of_succ_lt hfirst⟩,
        localSideData.outgoingLeftAttachment_subset_leftSidePiece 0 hfirst hx⟩
  · rcases vertexLocalPieces.outgoingRightAttachment_nonempty 0 hfirst with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hT_left, hS_right]
    right
    exact Set.mem_iUnion.2
      ⟨⟨0, Nat.lt_of_succ_lt hfirst⟩,
        localSideData.outgoingRightAttachment_subset_rightSidePiece 0 hfirst hx⟩
  · intro y hyS
    by_cases hsource_ball : y ∈ Metric.ball γ.source r0
    · exact left_source_complement y hyS hsource_ball
    · by_cases htarget_ball : y ∈ Metric.ball γ.target r1
      · exact left_target_complement y hyS htarget_ball
      · exact outside_complement S.leftStrip S.left_subset_collar S.left_disjoint_arc
          y hyS hsource_ball htarget_ball
  · intro y hyT
    have hyR : y ∈ S.rightStrip := by
      simpa [hT_left] using hyT
    by_cases hsource_ball : y ∈ Metric.ball γ.source r0
    · exact right_source_complement y hyR hsource_ball
    · by_cases htarget_ball : y ∈ Metric.ball γ.target r1
      · exact right_target_complement y hyR htarget_ball
      · exact outside_complement S.rightStrip S.right_subset_collar S.right_disjoint_arc
          y hyR hsource_ball htarget_ball
  · intro x hxrel
    refine ⟨S.collar, S.collar_open, S.relativeInterior_subset_collar ?_, ?_⟩
    · simpa [γ] using hxrel
    · intro y hy
      have hy_not_rel : y ∉ γ.relativeInterior := by
        intro hyrel
        have hycar : y ∈ γ.carrier := by
          rw [γ.relativeInterior_eq] at hyrel
          exact hyrel.1
        have hyimg : y ∈ OrdinaryDrawingImage G D := by
          rw [OrdinaryDrawingImage]
          right
          exact Set.mem_iUnion.2
            ⟨A.dartEdge d, by simpa [γ, A.dartArc_carrier d] using hycar⟩
        exact hy.2 hyimg
      have hy_strip : y ∈ S.leftStrip ∪ S.rightStrip := by
        have hyDiff : y ∈ S.collar \ γ.relativeInterior := ⟨hy.1, hy_not_rel⟩
        rw [S.collar_without_arc] at hyDiff
        exact hyDiff
      rcases hy_strip with hy_left | hy_right
      · exact Or.inl hy_left
      · exact Or.inr (by simpa [hT_left] using hy_right)
  · intro x hxrel
    refine ⟨T.collar, T.collar_open, T.relativeInterior_subset_collar hxrel, ?_⟩
    intro y hy
    have hy_not_rel : y ∉ (A.dartArc d.symm).relativeInterior := by
      intro hyrel
      have hycar : y ∈ (A.dartArc d.symm).carrier := by
        rw [(A.dartArc d.symm).relativeInterior_eq] at hyrel
        exact hyrel.1
      have hyimg : y ∈ OrdinaryDrawingImage G D := by
        rw [OrdinaryDrawingImage]
        right
        exact Set.mem_iUnion.2
          ⟨A.dartEdge d.symm, by
            simpa [A.dartArc_carrier d.symm] using hycar⟩
      exact hy.2 hyimg
    have hy_strip : y ∈ T.leftStrip ∪ T.rightStrip := by
      have hyDiff : y ∈ T.collar \ (A.dartArc d.symm).relativeInterior :=
        ⟨hy.1, hy_not_rel⟩
      rw [T.collar_without_arc] at hyDiff
      exact hyDiff
    rcases hy_strip with hy_left | hy_right
    · exact Or.inl hy_left
    · exact Or.inr (by simpa [hT_right] using hy_right)
  · rcases vertexLocalPieces.incomingLeftAttachment_nonempty jlast hlast with ⟨x, hx⟩
    have hidx :
        (⟨jlast + 1, hlast⟩ : Fin γ.vertices.length) =
          ⟨itarget, htarget⟩ := by
      apply Fin.ext
      dsimp [jlast, itarget]
      omega
    have hx_piece :
        x ∈ localSideData.leftSidePiece ⟨itarget, htarget⟩ := by
      have hx' := localSideData.incomingLeftAttachment_subset_leftSidePiece jlast hlast hx
      simpa [hidx] using hx'
    have hx_cone_small :
        x ∈ PolygonalArcTerminalEndpointLeftCone γ r1 K1 :=
      hleft_target_cone hx_piece
    have hx_cone :
        x ∈ PolygonalArcTerminalEndpointLeftCone (A.dartArc d) rT KT := by
      have hx_large :=
        terminalCone_mono γ r1 rT K1 KT (le_of_lt hr1) (le_of_lt hr1_lt_rT)
          (le_of_lt hK1_lt_KT) hγ_terminal_len_pos hx_cone_small
      simpa [γ] using hx_large
    have hx_sector : x ∈ C.successorSector d := hterm hx_cone
    have hx_left : x ∈ S.leftStrip := by
      rw [hS_left]
      right
      exact Set.mem_iUnion.2 ⟨⟨itarget, htarget⟩, hx_piece⟩
    exact ⟨x, ⟨⟨hx_sector, hx_left⟩,
      C.successorSector_subset_localDisk d hx_sector⟩⟩
  · rcases vertexLocalPieces.outgoingRightAttachment_nonempty 0 hfirst with ⟨x, hx⟩
    have hx_piece :
        x ∈ localSideData.rightSidePiece ⟨0, Nat.lt_of_succ_lt hfirst⟩ :=
      localSideData.outgoingRightAttachment_subset_rightSidePiece 0 hfirst hx
    have hx_cone_small :
        x ∈ PolygonalArcTerminalEndpointLeftCone (A.dartArc d.symm) r0 K0 := by
      simpa [γ, A.dartArc_symm_eq_reverse d] using hright_source_cone hx_piece
    have hx_cone :
        x ∈ PolygonalArcTerminalEndpointLeftCone (A.dartArc d.symm) rTs KTs :=
      terminalCone_mono (A.dartArc d.symm) r0 rTs K0 KTs (le_of_lt hr0)
        (le_of_lt hr0_lt_rTs) (le_of_lt hK0_lt_KTs) hsymm_terminal_len_pos
        hx_cone_small
    have hx_sector : x ∈ C.successorSector d.symm := hterm_symm hx_cone
    have hx_left : x ∈ T.leftStrip := by
      rw [hT_left, hS_right]
      right
      exact Set.mem_iUnion.2
        ⟨⟨0, Nat.lt_of_succ_lt hfirst⟩, hx_piece⟩
    exact ⟨x, ⟨⟨hx_sector, hx_left⟩,
      C.successorSector_subset_localDisk d.symm hx_sector⟩⟩
  · intro p hp
    have hp_eq : p = pd := by
      dsimp [pd]
      calc
        p = C.star.successor.symm (C.star.successor p) :=
          (Equiv.symm_apply_apply C.star.successor p).symm
        _ = C.star.successor.symm d := by rw [hp]
    subst p
    rcases vertexLocalPieces.outgoingLeftAttachment_nonempty 0 hfirst with ⟨x, hx⟩
    have hx_piece :
        x ∈ localSideData.leftSidePiece ⟨0, Nat.lt_of_succ_lt hfirst⟩ :=
      localSideData.outgoingLeftAttachment_subset_leftSidePiece 0 hfirst hx
    have hx_cone_small :
        x ∈ PolygonalArcInitialEndpointLeftCone γ r0 K0 :=
      hleft_source_cone hx_piece
    have hx_cone :
        x ∈ PolygonalArcInitialEndpointLeftCone (A.dartArc d) rI KI := by
      have hx_large :=
        initialCone_mono γ r0 rI K0 KI (le_of_lt hr0) (le_of_lt hr0_lt_rI)
          (le_of_lt hK0_lt_KI) hγ_initial_len_pos hx_cone_small
      simpa [γ] using hx_large
    have hx_sector : x ∈ C.successorSector pd := hinit hx_cone
    have hx_left : x ∈ S.leftStrip := by
      rw [hS_left]
      right
      exact Set.mem_iUnion.2
        ⟨⟨0, Nat.lt_of_succ_lt hfirst⟩, hx_piece⟩
    exact ⟨x, ⟨⟨hx_sector, hx_left⟩,
      C.successorSector_subset_localDisk pd hx_sector⟩⟩
  · intro p hp
    have hp_eq : p = pds := by
      dsimp [pds]
      calc
        p = C.star.successor.symm (C.star.successor p) :=
          (Equiv.symm_apply_apply C.star.successor p).symm
        _ = C.star.successor.symm d.symm := by rw [hp]
    subst p
    rcases vertexLocalPieces.incomingRightAttachment_nonempty jlast hlast with ⟨x, hx⟩
    have hidx :
        (⟨jlast + 1, hlast⟩ : Fin γ.vertices.length) =
          ⟨itarget, htarget⟩ := by
      apply Fin.ext
      dsimp [jlast, itarget]
      omega
    have hx_piece :
        x ∈ localSideData.rightSidePiece ⟨itarget, htarget⟩ := by
      have hx' := localSideData.incomingRightAttachment_subset_rightSidePiece jlast hlast hx
      simpa [hidx] using hx'
    have hx_cone_small :
        x ∈ PolygonalArcInitialEndpointLeftCone (A.dartArc d.symm) r1 K1 := by
      simpa [γ, A.dartArc_symm_eq_reverse d] using hright_target_cone hx_piece
    have hx_cone :
        x ∈ PolygonalArcInitialEndpointLeftCone (A.dartArc d.symm) rIs KIs :=
      initialCone_mono (A.dartArc d.symm) r1 rIs K1 KIs (le_of_lt hr1)
        (le_of_lt hr1_lt_rIs) (le_of_lt hK1_lt_KIs) hsymm_initial_len_pos
        hx_cone_small
    have hx_sector : x ∈ C.successorSector pds := hinit_symm hx_cone
    have hx_left : x ∈ T.leftStrip := by
      rw [hT_left, hS_right]
      right
      exact Set.mem_iUnion.2 ⟨⟨itarget, htarget⟩, hx_piece⟩
    exact ⟨x, ⟨⟨hx_sector, hx_left⟩,
      C.successorSector_subset_localDisk pds hx_sector⟩⟩
