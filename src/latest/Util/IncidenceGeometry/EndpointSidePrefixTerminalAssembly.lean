import Util.IncidenceGeometry.EndpointSidePrefixAttachment
import Util.IncidenceGeometry.EndpointSidePrefixOrderedTerminalSuffix
import Util.IncidenceGeometry.EndpointSidePrefixTerminalChain
import Util.IncidenceGeometry.PolygonalArcFiniteFirstContactPrefix
import Util.IncidenceGeometry.StraightSegmentPolygonalArc


open Classical
noncomputable section

private lemma fiveUnion_subset_sixUnion
    {α : Type*} (A B C D E F : Set α) :
    A ∪ B ∪ C ∪ D ∪ F ⊆ A ∪ B ∪ C ∪ D ∪ E ∪ F := by
  intro z hz
  simp only [Set.mem_union] at hz ⊢
  tauto

private structure EndpointSidePrefixTerminalAssemblyPrepared
    (Aarc Barc BplusArc : PolygonalArc)
    (Rbeta H Bad DeltaX Qx SelectedSide StartSector :
      Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA : Finset (EuclideanSpace ℝ (Fin 2))) where
  E : EndpointSidePrefixAttachment
    Aarc Barc BplusArc Rbeta H Bad DeltaX Qx K XA
  prefix_source : (E.prefixPiece 0).source = Aarc.source
  prefix_carrier :
    (E.prefixPiece 0).carrier ⊆
      StartSector ∪ ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2)))
  prefix_interior : (E.prefixPiece 0).relativeInterior ⊆ StartSector
  r_ge : 3 ≤ E.r
  h' : EuclideanSpace ℝ (Fin 2)
  lastGate' : EuclideanSpace ℝ (Fin 2)
  Vin' : Set (EuclideanSpace ℝ (Fin 2))
  cprev_side :
    (E.prefixPiece (E.r - 3)).carrier ⊆ SelectedSide ∩ Vin'
  approach_side :
    (E.prefixPiece (E.r - 2)).carrier ⊆ SelectedSide ∩ Vin'
  cprev_target : (E.prefixPiece (E.r - 3)).target = lastGate'
  approach_source : (E.prefixPiece (E.r - 2)).source = lastGate'
  cprev_approach :
    (E.prefixPiece (E.r - 3)).carrier ∩
        (E.prefixPiece (E.r - 2)).carrier =
      ({lastGate'} : Set (EuclideanSpace ℝ (Fin 2)))
  approach_target : (E.prefixPiece (E.r - 2)).target = h'
  final_source : (E.prefixPiece (E.r - 1)).source = h'
  final_target : (E.prefixPiece (E.r - 1)).target = terminalGate
  approach_final :
    (E.prefixPiece (E.r - 2)).carrier ∩
        (E.prefixPiece (E.r - 1)).carrier =
      ({h'} : Set (EuclideanSpace ℝ (Fin 2)))
  final_carrier :
    (E.prefixPiece (E.r - 1)).carrier = segment ℝ h' terminalGate
  cprev_final :
    Disjoint (E.prefixPiece (E.r - 3)).carrier
      (E.prefixPiece (E.r - 1)).carrier
  gate_side_source : (E.prefixPiece E.r).source = terminalGate
  gate_side_final :
    (E.prefixPiece (E.r - 1)).carrier ∩ (E.prefixPiece E.r).carrier =
      ({terminalGate} : Set (EuclideanSpace ℝ (Fin 2)))
  gate_side_carrier :
    (E.prefixPiece E.r).carrier = segment ℝ terminalGate terminalSideSource
  terminal_side_carrier :
    E.terminalSide.carrier = segment ℝ terminalSideSource quadrantGate
  terminal_connector_carrier :
    E.terminalConnector.carrier = segment ℝ quadrantGate BplusArc.target

private structure EndpointSidePrefixTerminalAssemblyContext
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) where
  hK : K.carrier = H
  hAarcRbeta : Disjoint Aarc.carrier Rbeta
  hAarcSourceNotSide : Aarc.source ∉ SelectedSide
  hAarcSourceNeTarget : Aarc.source ≠ BplusArc.target
  hterminalGateNotSide : terminalGate ∉ SelectedSide
  hsideTerminalSep : SelectedSide ∩
    (closure TerminalSideRegion ∪
    closure TerminalBridgeRegion ∪ closure Qx) =
    (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  hTerminalSideDelta : TerminalSideRegion ⊆ DeltaX
  hTerminalBridgeDelta : TerminalBridgeRegion ⊆ DeltaX
  hQxDelta : Qx ⊆ DeltaX
  hPsource : P.source = Aarc.source
  hPtarget : P.target = predecessor.source
  hPcarrier : P.carrier ⊆
    SelectedSide ∪
    ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2)))
  hPavoid : P.relativeInterior ∩
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
    Rbeta ∪ Bad) =
    (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  hfinite : Set.Finite
    (P.carrier ∩
    (predecessor.carrier ∪ approach.carrier ∪
    segment ℝ h terminalGate))
  hfirst : (∃ hfirst : 0 + 1 < P.vertices.length,
    segment ℝ P.vertices[0] P.vertices[1] ⊆
    StartSector ∪
    ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
    openSegment ℝ P.vertices[0] P.vertices[1] ⊆ StartSector)
  hxClean : (∀ z : EuclideanSpace ℝ (Fin 2),
    z ∈ xClean ↔ z ∈ P.relativeInterior ∧ z ∈ H)
  hchargeMem : (∀ z : EuclideanSpace ℝ (Fin 2),
    z ∈ xClean → charge z ∈ XA)
  hchargeInj : (∀ z w : EuclideanSpace ℝ (Fin 2),
    z ∈ xClean → w ∈ xClean →
    charge z = charge w → z = w)
  hclean : (∀ z : EuclideanSpace ℝ (Fin 2),
    z ∈ xClean →
    z ∉ Bad ∧
    z ∉ (K.points : Set (EuclideanSpace ℝ (Fin 2))) ∧
    ∃ j : ℕ,
    ∃ hj : j + 1 < P.vertices.length,
    z ∈ openSegment ℝ
    P.vertices[j] P.vertices[j + 1] ∧
    ∃! s :
    EuclideanSpace ℝ (Fin 2) ×
    EuclideanSpace ℝ (Fin 2),
    s ∈ K.segments ∧
    z ∈ openSegment ℝ s.1 s.2 ∧
    ¬ ∃ c : ℝ,
    s.2 - s.1 =
    c • (P.vertices[j + 1] - P.vertices[j]))
  hpredecessorSide : predecessor.carrier ⊆ SelectedSide ∩ Vin
  happroachSide : approach.carrier ⊆ SelectedSide ∩ Vin
  hpredecessorTarget : predecessor.target = lastGate
  happroachSource : approach.source = lastGate
  hpredecessorApproach : predecessor.carrier ∩ approach.carrier =
    ({lastGate} : Set (EuclideanSpace ℝ (Fin 2)))
  happroachTarget : approach.target = h
  happroachSegment : approach.carrier ∩ segment ℝ h terminalGate =
    ({h} : Set (EuclideanSpace ℝ (Fin 2)))
  hpredecessorSegment : Disjoint predecessor.carrier
    (segment ℝ h terminalGate)
  hhVin : h ∈ Vin
  hhNeGate : h ≠ terminalGate
  hhAvoid : h ∉
    (Aarc.carrier ∪ Barc.carrier ∪
    BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad)
  hVinSide : Vin ⊆ SelectedSide
  hVinDelta : Vin ⊆ DeltaX
  hVinQx : Vin ∩ Qx =
    (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  hVinAvoid : Vin ∩
    ((Aarc.carrier ∪ Barc.carrier ∪
    BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
    (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  hgateClosure : terminalGate ∈ closure Vin
  hgateNotVin : terminalGate ∉ Vin
  hsegmentVin : segment ℝ h terminalGate ⊆
    Vin ∪
    ({terminalGate} :
    Set (EuclideanSpace ℝ (Fin 2)))
  hopenSegmentVin : openSegment ℝ h terminalGate ⊆ Vin
  hsegmentTerminalSide : segment ℝ h terminalGate ∩
    (TerminalSideRegion ∪
    ({terminalGate} :
    Set (EuclideanSpace ℝ (Fin 2)))) =
    ({terminalGate} :
    Set (EuclideanSpace ℝ (Fin 2)))
  hclosureVinTerminalSide : closure Vin ∩
    closure TerminalSideRegion =
    ({terminalGate} :
    Set (EuclideanSpace ℝ (Fin 2)))
  hclosureVinTerminalBridge : closure Vin ∩
    closure TerminalBridgeRegion =
    (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  hgateDelta : terminalGate ∈ DeltaX
  hgateNotQx : terminalGate ∉ Qx
  hterminalSideSourceDelta : terminalSideSource ∈ DeltaX
  hgateNeTerminalSideSource : terminalGate ≠ terminalSideSource
  hterminalSideSegment : segment ℝ terminalGate terminalSideSource ⊆
    TerminalSideRegion ∪
    ({terminalGate, terminalSideSource} :
    Set (EuclideanSpace ℝ (Fin 2)))
  hterminalSideOpen : openSegment ℝ terminalGate terminalSideSource ⊆
    TerminalSideRegion
  hterminalSideAvoid : (TerminalSideRegion ∪
    ({terminalGate, terminalSideSource} :
    Set (EuclideanSpace ℝ (Fin 2)))) ∩
    ((Aarc.carrier ∪ Barc.carrier ∪
    BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
    (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  hterminalSideSourceNeQuadrant : terminalSideSource ≠ quadrantGate
  hterminalBridgeSegment : segment ℝ terminalSideSource quadrantGate ⊆
    TerminalBridgeRegion ∪
    ({terminalSideSource, quadrantGate} :
    Set (EuclideanSpace ℝ (Fin 2)))
  hterminalBridgeOpen : openSegment ℝ terminalSideSource quadrantGate ⊆
    TerminalBridgeRegion
  hterminalBridgeAvoid : (TerminalBridgeRegion ∪
    ({terminalSideSource, quadrantGate} :
    Set (EuclideanSpace ℝ (Fin 2)))) ∩
    ((Aarc.carrier ∪ Barc.carrier ∪
    BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
    (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  hquadrantMemQx : quadrantGate ∈ Qx
  hquadrantNeTarget : quadrantGate ≠ BplusArc.target
  hterminalBridgeMeetsQx : segment ℝ terminalSideSource quadrantGate ∩ Qx =
    ({quadrantGate} :
    Set (EuclideanSpace ℝ (Fin 2)))
  hterminalClosuresMeet : closure TerminalSideRegion ∩
    closure TerminalBridgeRegion =
    ({terminalSideSource} :
    Set (EuclideanSpace ℝ (Fin 2)))
  hterminalSideClosureQx : closure TerminalSideRegion ∩ closure Qx =
    (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  hterminalBridgeClosureQx : closure TerminalBridgeRegion ∩ closure Qx =
    ({quadrantGate} :
    Set (EuclideanSpace ℝ (Fin 2)))
  hconnectorSegment : segment ℝ quadrantGate BplusArc.target ⊆ Qx
  hconnectorAvoid : openSegment ℝ quadrantGate BplusArc.target ∩
    ((Aarc.carrier ∪ Barc.carrier ∪
    BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
    (∅ : Set (EuclideanSpace ℝ (Fin 2)))

private lemma endpoint_polygonalArc_source_mem (Γ : PolygonalArc) :
    Γ.source ∈ Γ.carrier := by
  rw [Γ.carrier_eq]
  have hzero : Γ.vertices[0]'(by
      have := Γ.length_ge_two
      omega) = Γ.source := by
    have hhead := Γ.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem (by
      have := Γ.length_ge_two
      omega)] at hhead
    exact Option.some.inj hhead
  refine ⟨0, by
    have := Γ.length_ge_two
    omega, ?_⟩
  rw [hzero]
  exact left_mem_segment ℝ Γ.source
    (Γ.vertices[1]'(by
      have := Γ.length_ge_two
      omega))

private lemma endpoint_polygonalArc_target_mem (Γ : PolygonalArc) :
    Γ.target ∈ Γ.carrier := by
  rw [Γ.carrier_eq]
  let i := Γ.vertices.length - 2
  have hi : i + 1 < Γ.vertices.length := by
    dsimp [i]
    have := Γ.length_ge_two
    omega
  refine ⟨i, hi, ?_⟩
  have hlast : Γ.vertices[i + 1] = Γ.target := by
    have hlast' := Γ.target_eq_last
    rw [List.getLast?_eq_getElem?] at hlast'
    have hidx : Γ.vertices.length - 1 < Γ.vertices.length := by
      have := Γ.length_ge_two
      omega
    rw [List.getElem?_eq_getElem hidx] at hlast'
    have hiEq : i + 1 = Γ.vertices.length - 1 := by
      dsimp [i]
      have := Γ.length_ge_two
      omega
    simpa [hiEq] using Option.some.inj hlast'
  rw [hlast]
  exact right_mem_segment ℝ Γ.vertices[i] Γ.target

private structure EndpointSidePrefixTerminalAssemblyGeometry
    (Aarc Barc BplusArc P : PolygonalArc)
    (SelectedSide Rbeta H Bad Vin : Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate :
      EuclideanSpace ℝ (Fin 2))
    (xClean : Finset (EuclideanSpace ℝ (Fin 2))) where
  q : EuclideanSpace ℝ (Fin 2)
  Pq : PolygonalArc
  firstCut : EuclideanSpace ℝ (Fin 2)
  firstPiece : PolygonalArc
  remainder : PolygonalArc
  lastGate' : EuclideanSpace ℝ (Fin 2)
  h' : EuclideanSpace ℝ (Fin 2)
  Cprev' : PolygonalArc
  approach' : PolygonalArc
  final' : PolygonalArc
  gateSide : PolygonalArc
  terminalSide : PolygonalArc
  terminalConnector : PolygonalArc
  terminalGateAvoid : terminalGate ∉
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad)
  Pq_source : Pq.source = P.source
  Pq_target : Pq.target = q
  Pq_interior : Pq.relativeInterior ⊆ P.relativeInterior
  Pq_decomposition : Pq.carrier = firstPiece.carrier ∪ remainder.carrier
  firstPiece_remainder : firstPiece.carrier ∩ remainder.carrier = {firstCut}
  firstCut_not_clean : firstCut ∉ xClean
  firstPiece_source : firstPiece.source = P.source
  firstPiece_target : firstPiece.target = firstCut
  remainder_source : remainder.source = firstCut
  remainder_target : remainder.target = q
  firstPiece_carrier :
    firstPiece.carrier ⊆ segment ℝ
      (P.vertices[0]'(by have := P.length_ge_two; omega))
      (P.vertices[1]'(by have := P.length_ge_two; omega))
  firstPiece_interior :
    firstPiece.relativeInterior ⊆ openSegment ℝ
      (P.vertices[0]'(by have := P.length_ge_two; omega))
      (P.vertices[1]'(by have := P.length_ge_two; omega))
  firstPiece_interior_Pq : firstPiece.relativeInterior ⊆ Pq.relativeInterior
  remainder_interior_Pq : remainder.relativeInterior ⊆ Pq.relativeInterior
  split_transfer :
    ∀ piece ∈ [firstPiece, remainder],
      ∀ (z : EuclideanSpace ℝ (Fin 2)) (i : ℕ)
        (hi : i + 1 < P.vertices.length),
        z ∈ openSegment ℝ P.vertices[i] P.vertices[i + 1] →
        z ∈ piece.carrier → z ≠ firstCut → z ≠ q →
        ∃ j, ∃ (hj : j + 1 < piece.vertices.length),
          z ∈ openSegment ℝ piece.vertices[j] piece.vertices[j + 1] ∧
          ∃ (c : ℝ), c ≠ 0 ∧
            piece.vertices[j + 1] - piece.vertices[j] =
              c • (P.vertices[i + 1] - P.vertices[i])
  Cprev_source : Cprev'.source = q
  Cprev_target : Cprev'.target = lastGate'
  approach_source : approach'.source = lastGate'
  approach_target : approach'.target = h'
  final_source : final'.source = h'
  final_target : final'.target = terminalGate
  Cprev_side : Cprev'.carrier ⊆ SelectedSide ∩ Vin
  approach_side : approach'.carrier ⊆ SelectedSide ∩ Vin
  final_carrier : final'.carrier = segment ℝ h' terminalGate
  final_interior_Vin : final'.relativeInterior ⊆ Vin
  Pq_Cprev : remainder.carrier ∩ Cprev'.carrier = {q}
  Pq_approach : Disjoint remainder.carrier approach'.carrier
  Pq_final : Disjoint remainder.carrier final'.carrier
  Cprev_approach : Cprev'.carrier ∩ approach'.carrier = {lastGate'}
  approach_final : approach'.carrier ∩ final'.carrier = {h'}
  Cprev_final : Disjoint Cprev'.carrier final'.carrier
  gateSide_source : gateSide.source = terminalGate
  gateSide_target : gateSide.target = terminalSideSource
  gateSide_carrier : gateSide.carrier = segment ℝ terminalGate terminalSideSource
  gateSide_interior :
    gateSide.relativeInterior = openSegment ℝ terminalGate terminalSideSource
  terminalSide_source : terminalSide.source = terminalSideSource
  terminalSide_target : terminalSide.target = quadrantGate
  terminalSide_carrier :
    terminalSide.carrier = segment ℝ terminalSideSource quadrantGate
  terminalSide_interior :
    terminalSide.relativeInterior = openSegment ℝ terminalSideSource quadrantGate
  terminalConnector_source : terminalConnector.source = quadrantGate
  terminalConnector_target : terminalConnector.target = BplusArc.target
  terminalConnector_carrier :
    terminalConnector.carrier = segment ℝ quadrantGate BplusArc.target
  terminalConnector_interior :
    terminalConnector.relativeInterior = openSegment ℝ quadrantGate BplusArc.target
  gateSide_final : final'.carrier ∩ gateSide.carrier = {terminalGate}
  gateSide_terminalSide :
    gateSide.carrier ∩ terminalSide.carrier = {terminalSideSource}
  point_avoid_of_Vin : ∀ {z : EuclideanSpace ℝ (Fin 2)}, z ∈ Vin →
    z ∉ (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad)
  forbidden_no_H_subset :
    Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad ⊆
      Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad
  terminalSideSource_avoid : terminalSideSource ∉
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad)
  quadrant_avoid : quadrantGate ∉
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad)
  firstPiece_Cprev : Disjoint firstPiece.carrier Cprev'.carrier
  firstPiece_approach : Disjoint firstPiece.carrier approach'.carrier
  firstPiece_final : Disjoint firstPiece.carrier final'.carrier
  firstPiece_gateSide : Disjoint firstPiece.carrier gateSide.carrier
  remainder_gateSide : Disjoint remainder.carrier gateSide.carrier
  Cprev_gateSide : Disjoint Cprev'.carrier gateSide.carrier
  approach_gateSide : Disjoint approach'.carrier gateSide.carrier
  firstPiece_terminalSide : Disjoint firstPiece.carrier terminalSide.carrier
  remainder_terminalSide : Disjoint remainder.carrier terminalSide.carrier
  Cprev_terminalSide : Disjoint Cprev'.carrier terminalSide.carrier
  approach_terminalSide : Disjoint approach'.carrier terminalSide.carrier
  final_terminalSide : Disjoint final'.carrier terminalSide.carrier
  firstPiece_connector : Disjoint firstPiece.carrier terminalConnector.carrier
  remainder_connector : Disjoint remainder.carrier terminalConnector.carrier
  Cprev_connector : Disjoint Cprev'.carrier terminalConnector.carrier
  approach_connector : Disjoint approach'.carrier terminalConnector.carrier
  final_connector : Disjoint final'.carrier terminalConnector.carrier
  gateSide_connector : Disjoint gateSide.carrier terminalConnector.carrier
  firstCut_avoid : firstCut ∉
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad)

private structure EndpointSidePrefixTerminalAttachmentStage
    (Aarc Barc BplusArc : PolygonalArc)
    (Rbeta H Bad DeltaX Qx : Set (EuclideanSpace ℝ (Fin 2)))
    (K : FinitePolygonalSet)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (firstPiece Cprev approach final gateSide terminalSide terminalConnector :
      PolygonalArc) where
  E : EndpointSidePrefixAttachment
    Aarc Barc BplusArc Rbeta H Bad DeltaX Qx K XA
  r_eq : E.r = 5
  piece_zero : E.prefixPiece 0 = firstPiece
  piece_r_sub_three : E.prefixPiece (E.r - 3) = Cprev
  piece_r_sub_two : E.prefixPiece (E.r - 2) = approach
  piece_r_sub_one : E.prefixPiece (E.r - 1) = final
  piece_r : E.prefixPiece E.r = gateSide
  terminal_side : E.terminalSide = terminalSide
  terminal_connector : E.terminalConnector = terminalConnector

private def endpointSidePrefixPiece
    {Aarc Barc BplusArc P : PolygonalArc}
    {SelectedSide Rbeta H Bad Vin : Set (EuclideanSpace ℝ (Fin 2))}
    {terminalGate terminalSideSource quadrantGate :
      EuclideanSpace ℝ (Fin 2)}
    {xClean : Finset (EuclideanSpace ℝ (Fin 2))}
    (geom : EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean) : ℕ → PolygonalArc :=
  fun i =>
    match i with
    | 0 => geom.firstPiece
    | 1 => geom.remainder
    | 2 => geom.Cprev'
    | 3 => geom.approach'
    | 4 => geom.final'
    | 5 => geom.gateSide
    | _ => geom.firstPiece

private def endpointSideXPrefix
    {Aarc Barc BplusArc P : PolygonalArc}
    {SelectedSide Rbeta H Bad Vin : Set (EuclideanSpace ℝ (Fin 2))}
    {terminalGate terminalSideSource quadrantGate :
      EuclideanSpace ℝ (Fin 2)}
    {xClean : Finset (EuclideanSpace ℝ (Fin 2))}
    (geom : EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  xClean.filter (fun z => z ∈ geom.Pq.relativeInterior)

private structure EndpointSidePrefixCombinatorialFacts
    (Aarc Barc BplusArc P : PolygonalArc)
    (SelectedSide Rbeta H Bad Vin : Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate :
      EuclideanSpace ℝ (Fin 2))
    (xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (geom : EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean) where
  source : (endpointSidePrefixPiece geom 0).source = Aarc.source
  target : (endpointSidePrefixPiece geom 5).target = geom.terminalSide.source
  consecutive_sources : ∀ i : ℕ, i < 5 →
    (endpointSidePrefixPiece geom i).target =
      (endpointSidePrefixPiece geom (i + 1)).source
  consecutive_meets : ∀ i : ℕ, i < 5 →
    (endpointSidePrefixPiece geom i).carrier ∩
        (endpointSidePrefixPiece geom (i + 1)).carrier =
      ({(endpointSidePrefixPiece geom i).target} :
        Set (EuclideanSpace ℝ (Fin 2)))
  nonconsecutive_disjoint : ∀ i j : ℕ, i ≤ 5 → j ≤ 5 → i + 1 < j →
    Disjoint (endpointSidePrefixPiece geom i).carrier
      (endpointSidePrefixPiece geom j).carrier
  internal_gates_avoid : ∀ i : ℕ, i < 5 →
    (endpointSidePrefixPiece geom i).target ∉
      (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad)
  relative_interiors_avoid : ∀ i : ℕ, i ≤ 5 →
    (endpointSidePrefixPiece geom i).relativeInterior ∩
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ Bad) =
      (∅ : Set (EuclideanSpace ℝ (Fin 2)))

private structure EndpointSidePrefixCleanFacts
    (Aarc Barc BplusArc P : PolygonalArc)
    (SelectedSide Rbeta H Bad Vin : Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (geom : EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean) where
  spec : ∀ z : EuclideanSpace ℝ (Fin 2),
    z ∈ endpointSideXPrefix geom ↔
      (∃ i : ℕ, i ≤ 5 ∧
        z ∈ (endpointSidePrefixPiece geom i).relativeInterior) ∧ z ∈ H
  charge_mem : ∀ z : EuclideanSpace ℝ (Fin 2),
    z ∈ endpointSideXPrefix geom → charge z ∈ XA
  charge_injective : ∀ z w : EuclideanSpace ℝ (Fin 2),
    z ∈ endpointSideXPrefix geom → w ∈ endpointSideXPrefix geom →
      charge z = charge w → z = w
  clean : ∀ z : EuclideanSpace ℝ (Fin 2),
    z ∈ endpointSideXPrefix geom →
      z ∉ Bad ∧ z ∉ (K.points : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∃ i : ℕ, i ≤ 5 ∧ ∃ j : ℕ,
        ∃ hj : j + 1 < (endpointSidePrefixPiece geom i).vertices.length,
          z ∈ openSegment ℝ (endpointSidePrefixPiece geom i).vertices[j]
            (endpointSidePrefixPiece geom i).vertices[j + 1] ∧
          ∃! s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
            s ∈ K.segments ∧ z ∈ openSegment ℝ s.1 s.2 ∧
            ¬ ∃ c : ℝ, s.2 - s.1 = c •
              ((endpointSidePrefixPiece geom i).vertices[j + 1] -
                (endpointSidePrefixPiece geom i).vertices[j])

private structure EndpointSidePrefixTerminalFacts
    (Aarc Barc BplusArc : PolygonalArc)
    (Rbeta H Bad DeltaX Qx : Set (EuclideanSpace ℝ (Fin 2)))
    (K : FinitePolygonalSet)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (prefixPiece : ℕ → PolygonalArc)
    (terminalSide terminalConnector : PolygonalArc)
    (omega : EuclideanSpace ℝ (Fin 2)) where
  source_mem_delta : terminalSide.source ∈ DeltaX
  source_not_mem_Q : terminalSide.source ∉ Qx
  source_avoid : terminalSide.source ∉
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad)
  side_target : terminalSide.target = omega
  connector_source : terminalConnector.source = omega
  connector_target : terminalConnector.target = BplusArc.target
  omega_mem_Q : omega ∈ Qx
  omega_ne_target : omega ≠ BplusArc.target
  omega_avoid : omega ∉
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad)
  side_subset_delta : terminalSide.carrier ⊆ DeltaX
  side_meets_Q : terminalSide.carrier ∩ Qx = {omega}
  side_relativeInterior_avoid : terminalSide.relativeInterior ∩
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) = ∅
  connector_subset_Q : terminalConnector.carrier ⊆ Qx
  connector_relativeInterior_avoid : terminalConnector.relativeInterior ∩
    (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) = ∅
  predecessor_meets_terminal :
    (prefixPiece 5).carrier ∩ terminalSide.carrier = {terminalSide.source}
  earlier_prefix_disjoint_terminal : ∀ i : ℕ, i < 5 →
    Disjoint (prefixPiece i).carrier terminalSide.carrier
  prefix_disjoint_terminal_connector : ∀ i : ℕ, i ≤ 5 →
    Disjoint (prefixPiece i).carrier terminalConnector.carrier

private lemma endpointSidePrefixTerminalAssembly_geometry_from_context
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ctx : EndpointSidePrefixTerminalAssemblyContext
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean charge) :
    Nonempty (EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean) := by
  rcases ctx with ⟨hK, hAarcRbeta, hAarcSourceNotSide,
    hAarcSourceNeTarget, hterminalGateNotSide, hsideTerminalSep,
    hTerminalSideDelta, hTerminalBridgeDelta, hQxDelta, hPsource, hPtarget,
    hPcarrier, hPavoid, hfinite, hfirst, hxClean, hchargeMem, hchargeInj,
    hclean, hpredecessorSide, happroachSide, hpredecessorTarget,
    happroachSource, hpredecessorApproach, happroachTarget, happroachSegment,
    hpredecessorSegment, hhVin, hhNeGate, hhAvoid, hVinSide, hVinDelta,
    hVinQx, hVinAvoid, hgateClosure, hgateNotVin, hsegmentVin,
    hopenSegmentVin, hsegmentTerminalSide, hclosureVinTerminalSide,
    hclosureVinTerminalBridge, hgateDelta, hgateNotQx,
    hterminalSideSourceDelta, hgateNeTerminalSideSource,
    hterminalSideSegment, hterminalSideOpen, hterminalSideAvoid,
    hterminalSideSourceNeQuadrant, hterminalBridgeSegment,
    hterminalBridgeOpen, hterminalBridgeAvoid, hquadrantMemQx,
    hquadrantNeTarget, hterminalBridgeMeetsQx, hterminalClosuresMeet,
    hterminalSideClosureQx, hterminalBridgeClosureQx, hconnectorSegment,
    hconnectorAvoid⟩
  obtain ⟨terminalSegment, chain, hterminalSegmentSource,
      hterminalSegmentTarget, hterminalSegmentCarrier,
      hterminalSegmentInterior, happroachTerminalSegment,
      hpredecessorTerminalSegment, hchainVertices, hchainSource,
      hchainTarget, hchainCarrier, hchainInterior, hpredecessorInterior,
      happroachInterior, hterminalSegmentInteriorSubset, hchainTransfer⟩ :=
    EndpointSidePrefixTerminalChain predecessor approach lastGate h terminalGate
      hpredecessorTarget happroachSource hpredecessorApproach happroachTarget
      happroachSegment hpredecessorSegment hhNeGate
  have polygonalArc_source_mem (Γ : PolygonalArc) : Γ.source ∈ Γ.carrier := by
    rw [Γ.carrier_eq]
    have hzero : Γ.vertices[0]'(by
        have := Γ.length_ge_two
        omega) = Γ.source := by
      have hhead := Γ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by
        have := Γ.length_ge_two
        omega)] at hhead
      exact Option.some.inj hhead
    refine ⟨0, by
      have := Γ.length_ge_two
      omega, ?_⟩
    rw [hzero]
    exact left_mem_segment ℝ Γ.source
      (Γ.vertices[1]'(by
        have := Γ.length_ge_two
        omega))
  have polygonalArc_target_mem (Γ : PolygonalArc) : Γ.target ∈ Γ.carrier := by
    rw [Γ.carrier_eq]
    let i := Γ.vertices.length - 2
    have hi : i + 1 < Γ.vertices.length := by
      dsimp [i]
      have := Γ.length_ge_two
      omega
    refine ⟨i, hi, ?_⟩
    have hlast : Γ.vertices[i + 1] = Γ.target := by
      have hlast' := Γ.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlast'
      have hidx : Γ.vertices.length - 1 < Γ.vertices.length := by
        have := Γ.length_ge_two
        omega
      rw [List.getElem?_eq_getElem hidx] at hlast'
      have hiEq : i + 1 = Γ.vertices.length - 1 := by
        dsimp [i]
        have := Γ.length_ge_two
        omega
      simpa [hiEq] using Option.some.inj hlast'
    rw [hlast]
    exact right_mem_segment ℝ Γ.vertices[i] Γ.target
  have hAarcSourceMem : Aarc.source ∈ Aarc.carrier :=
    polygonalArc_source_mem Aarc
  have hterminalGateAvoid :
      terminalGate ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hmem
    have hleft :
        terminalGate ∈
          TerminalSideRegion ∪ ({terminalGate, terminalSideSource} :
            Set (EuclideanSpace ℝ (Fin 2))) := by simp
    have hright :
        terminalGate ∈
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := by
      simpa only [Set.union_assoc] using hmem
    have : terminalGate ∈
        (TerminalSideRegion ∪ ({terminalGate, terminalSideSource} :
            Set (EuclideanSpace ℝ (Fin 2)))) ∩
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := ⟨hleft, hright⟩
    rw [hterminalSideAvoid] at this
    exact this
  have hAarcSourceNeGate : Aarc.source ≠ terminalGate := by
    intro hEq
    apply hterminalGateAvoid
    rw [← hEq]
    simp only [Set.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem))))
  have hPsourceNotChain : P.source ∉ chain.carrier := by
    intro hz
    rw [hchainCarrier, hterminalSegmentCarrier] at hz
    rcases hz with (hz | hz) | hz
    · have hside : P.source ∈ SelectedSide := (hpredecessorSide hz).1
      exact hAarcSourceNotSide (by simpa [hPsource] using hside)
    · have hside : P.source ∈ SelectedSide := (happroachSide hz).1
      exact hAarcSourceNotSide (by simpa [hPsource] using hside)
    · have hz' := hsegmentVin hz
      rcases hz' with hzVin | hzGate
      · have hside : P.source ∈ SelectedSide := hVinSide hzVin
        exact hAarcSourceNotSide (by simpa [hPsource] using hside)
      · have : P.source = terminalGate := by simpa using hzGate
        exact hAarcSourceNeGate (by simpa [hPsource] using this)
  have hPtargetMemChain : P.target ∈ chain.carrier := by
    rw [hPtarget, ← hchainSource]
    exact polygonalArc_source_mem chain
  have hfiniteChain : Set.Finite (P.carrier ∩ chain.carrier) := by
    simpa [hchainCarrier, hterminalSegmentCarrier, Set.union_assoc] using hfinite
  obtain ⟨q, Pq, hqContact, hqNeSource, hPqSource, hPqTarget,
      hPqCarrier, hPqInterior, hPqMeetsChain, hPqInteriorAvoidsChain,
      hPqAlternative, hPqFirst, hPqFirstCarrier, hPqFirstOpen,
      hPqTransfer, firstCut, firstPiece, remainder, hfirstCutNotClean,
      hfirstCutInterior, hfirstPieceSource, hfirstPieceTarget, hremainderSource,
      hremainderTarget, hPqDecomposition, hfirstPieceRemainder,
      hfirstPieceDisjointChain, hremainderMeetsChain,
      hfirstPieceCarrier, hfirstPieceInterior, hfirstPieceInteriorPq,
      hremainderInteriorPq, hsplitTransfer⟩ :=
    PolygonalArcFiniteFirstContactPrefix P chain xClean hfiniteChain
      hPtargetMemChain hPsourceNotChain
  have hqNeTerminalGate : q ≠ terminalGate := by
    intro hEq
    have hqP : q ∈ P.carrier := hqContact.1
    have hqSide := hPcarrier hqP
    rcases hqSide with hqSide | hqSource
    · exact hterminalGateNotSide (by simpa [hEq] using hqSide)
    · have : Aarc.source = terminalGate := by
        simpa [hPsource, hEq] using hqSource.symm
      exact hAarcSourceNeGate this
  obtain ⟨lastGate', h', suffix, Cprev', approach', final',
      hlastGateNotClean, hhNotClean, hsuffixSource, hsuffixTarget,
      hsuffixCarrier, hsuffixAlternative, hCprevSource, hCprevTarget,
      happroach'Source, happroach'Target, hfinalSource, hfinalTarget,
      hCprevSide, happroach'Side, hfinalCarrier, hfinalVin,
      hfinalInteriorVin, hCprevChain, happroachChain, hfinalChain,
      hPqCprev, hPqApproach, hPqFinal,
      hCprevApproach, happroachFinal, hCprevFinal, hsuffixTransfer⟩ :=
    EndpointSidePrefixOrderedTerminalSuffix
      remainder chain predecessor approach terminalSegment SelectedSide Vin
        xClean q lastGate h terminalGate hchainSource hchainTarget
        hterminalSegmentSource hterminalSegmentTarget hterminalSegmentCarrier
        hchainVertices hchainCarrier hpredecessorApproach
        happroachTerminalSegment hpredecessorTerminalSegment hremainderTarget
        hqContact.2 hqNeTerminalGate hremainderMeetsChain
        hpredecessorSide happroachSide hpredecessorTarget happroachSource
        happroachTarget hsegmentVin hopenSegmentVin hVinSide
        hterminalGateNotSide
  obtain ⟨gateSide, hgateSideSource, hgateSideTarget, hgateSideCarrier,
      hgateSideInterior⟩ :=
    StraightSegmentPolygonalArc terminalGate terminalSideSource
      hgateNeTerminalSideSource
  obtain ⟨terminalSide, hterminalSideSource, hterminalSideTarget,
      hterminalSideCarrier, hterminalSideInterior⟩ :=
    StraightSegmentPolygonalArc terminalSideSource quadrantGate
      hterminalSideSourceNeQuadrant
  obtain ⟨terminalConnector, hterminalConnectorSource,
      hterminalConnectorTarget, hterminalConnectorCarrier,
      hterminalConnectorInterior⟩ :=
    StraightSegmentPolygonalArc quadrantGate BplusArc.target hquadrantNeTarget
  have hselectedDisjointTerminalSide :
      Disjoint SelectedSide (closure TerminalSideRegion) := by
    rw [Set.disjoint_left]
    intro z hzSide hzTerminal
    have hz :
        z ∈ SelectedSide ∩
      (closure TerminalSideRegion ∪ closure TerminalBridgeRegion ∪
            closure Qx) :=
      ⟨hzSide, Or.inl (Or.inl hzTerminal)⟩
    rw [hsideTerminalSep] at hz
    exact hz
  have hselectedDisjointTerminalBridge :
      Disjoint SelectedSide (closure TerminalBridgeRegion) := by
    rw [Set.disjoint_left]
    intro z hzSide hzTerminal
    have hz :
        z ∈ SelectedSide ∩
      (closure TerminalSideRegion ∪ closure TerminalBridgeRegion ∪
            closure Qx) :=
      ⟨hzSide, Or.inl (Or.inr hzTerminal)⟩
    rw [hsideTerminalSep] at hz
    exact hz
  have hselectedDisjointQx : Disjoint SelectedSide (closure Qx) := by
    rw [Set.disjoint_left]
    intro z hzSide hzQ
    have hz :
        z ∈ SelectedSide ∩
      (closure TerminalSideRegion ∪ closure TerminalBridgeRegion ∪
            closure Qx) :=
      ⟨hzSide, Or.inr hzQ⟩
    rw [hsideTerminalSep] at hz
    exact hz
  have hgateSideClosure :
      gateSide.carrier ⊆ closure TerminalSideRegion := by
    rw [hgateSideCarrier]
    exact segment_subset_closure_openSegment.trans
      (closure_mono hterminalSideOpen)
  have hterminalSideClosure :
      terminalSide.carrier ⊆ closure TerminalBridgeRegion := by
    rw [hterminalSideCarrier]
    exact segment_subset_closure_openSegment.trans
      (closure_mono hterminalBridgeOpen)
  have hfinalClosure : final'.carrier ⊆ closure Vin := by
    intro z hz
    rcases hfinalVin hz with hzVin | hzGate
    · exact subset_closure hzVin
    · have hzEq : z = terminalGate := by simpa using hzGate
      simpa [hzEq] using hgateClosure
  have hgateSideFinal :
      final'.carrier ∩ gateSide.carrier =
        ({terminalGate} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply Set.Subset.antisymm
    · intro z hz
      have hz' : z ∈ closure Vin ∩ closure TerminalSideRegion :=
        ⟨hfinalClosure hz.1, hgateSideClosure hz.2⟩
      rw [hclosureVinTerminalSide] at hz'
      exact hz'
    · intro z hz
      have hzEq : z = terminalGate := by simpa using hz
      subst z
      exact ⟨by
        rw [← hfinalTarget]
        exact polygonalArc_target_mem final', by
          rw [← hgateSideSource]
          exact polygonalArc_source_mem gateSide⟩
  have hgateSideTerminalSide :
      gateSide.carrier ∩ terminalSide.carrier =
        ({terminalSideSource} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply Set.Subset.antisymm
    · intro z hz
      have hz' :
          z ∈ closure TerminalSideRegion ∩ closure TerminalBridgeRegion :=
        ⟨hgateSideClosure hz.1, hterminalSideClosure hz.2⟩
      rw [hterminalClosuresMeet] at hz'
      exact hz'
    · intro z hz
      have hzEq : z = terminalSideSource := by simpa using hz
      subst z
      exact ⟨by
        rw [← hgateSideTarget]
        exact polygonalArc_target_mem gateSide, by
          rw [← hterminalSideSource]
          exact polygonalArc_source_mem terminalSide⟩
  have hpointAvoidOfVin {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Vin) :
      z ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hzForbidden
    have : z ∈
        Vin ∩
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := by
      refine ⟨hz, ?_⟩
      simpa only [Set.union_assoc] using hzForbidden
    rw [hVinAvoid] at this
    exact this
  have hforbiddenNoHSubset :
      (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ Bad) ⊆
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    exact fiveUnion_subset_sixUnion Aarc.carrier Barc.carrier
      BplusArc.carrier Rbeta H Bad
  have hterminalSideSourceAvoid :
      terminalSideSource ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hzForbidden
    have hzLeft :
        terminalSideSource ∈
          TerminalSideRegion ∪
            ({terminalGate, terminalSideSource} :
              Set (EuclideanSpace ℝ (Fin 2))) := by simp
    have hz :
        terminalSideSource ∈
          (TerminalSideRegion ∪
              ({terminalGate, terminalSideSource} :
                Set (EuclideanSpace ℝ (Fin 2)))) ∩
            ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H) ∪ Bad) := by
      refine ⟨hzLeft, ?_⟩
      simpa only [Set.union_assoc] using hzForbidden
    rw [hterminalSideAvoid] at hz
    exact hz
  have hquadrantAvoid :
      quadrantGate ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hzForbidden
    have hzLeft :
        quadrantGate ∈
          TerminalBridgeRegion ∪
            ({terminalSideSource, quadrantGate} :
              Set (EuclideanSpace ℝ (Fin 2))) := by simp
    have hz :
        quadrantGate ∈
          (TerminalBridgeRegion ∪
              ({terminalSideSource, quadrantGate} :
                Set (EuclideanSpace ℝ (Fin 2)))) ∩
            ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H) ∪ Bad) := by
      refine ⟨hzLeft, ?_⟩
      simpa only [Set.union_assoc] using hzForbidden
    rw [hterminalBridgeAvoid] at hz
    exact hz
  have hAarcSourceNotGateSide : Aarc.source ∉ gateSide.carrier := by
    intro hz
    have hzLeft := hterminalSideSegment (by
      simpa [hgateSideCarrier] using hz)
    have hzRight :
        Aarc.source ∈
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := by
      simp only [Set.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem))))
    have :
        Aarc.source ∈
          (TerminalSideRegion ∪
              ({terminalGate, terminalSideSource} :
                Set (EuclideanSpace ℝ (Fin 2)))) ∩
            ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H) ∪ Bad) :=
      ⟨hzLeft, hzRight⟩
    rw [hterminalSideAvoid] at this
    exact this
  have hPqGateSide : Disjoint Pq.carrier gateSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzPq hzGateSide
    rcases hPcarrier (hPqCarrier hzPq) with hzSide | hzSource
    · exact (Set.disjoint_left.mp hselectedDisjointTerminalSide hzSide)
        (hgateSideClosure hzGateSide)
    · have hzEq : z = Aarc.source := by simpa using hzSource
      exact hAarcSourceNotGateSide (by simpa [hzEq] using hzGateSide)
  have hCprevGateSide : Disjoint Cprev'.carrier gateSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzGate
    exact (Set.disjoint_left.mp hselectedDisjointTerminalSide
      (hCprevSide hzC).1) (hgateSideClosure hzGate)
  have happroachGateSide : Disjoint approach'.carrier gateSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzGate
    exact (Set.disjoint_left.mp hselectedDisjointTerminalSide
      (happroach'Side hzC).1) (hgateSideClosure hzGate)
  have hAarcSourceNotTerminalSide : Aarc.source ∉ terminalSide.carrier := by
    intro hz
    have hzLeft := hterminalBridgeSegment (by
      simpa [hterminalSideCarrier] using hz)
    have hzRight :
        Aarc.source ∈
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := by
      simp only [Set.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem))))
    have :
        Aarc.source ∈
          (TerminalBridgeRegion ∪
              ({terminalSideSource, quadrantGate} :
                Set (EuclideanSpace ℝ (Fin 2)))) ∩
            ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H) ∪ Bad) :=
      ⟨hzLeft, hzRight⟩
    rw [hterminalBridgeAvoid] at this
    exact this
  have hPqTerminalSide : Disjoint Pq.carrier terminalSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzPq hzTerminal
    rcases hPcarrier (hPqCarrier hzPq) with hzSide | hzSource
    · exact (Set.disjoint_left.mp hselectedDisjointTerminalBridge hzSide)
        (hterminalSideClosure hzTerminal)
    · have hzEq : z = Aarc.source := by simpa using hzSource
      exact hAarcSourceNotTerminalSide (by simpa [hzEq] using hzTerminal)
  have hCprevTerminalSide : Disjoint Cprev'.carrier terminalSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzTerminal
    exact (Set.disjoint_left.mp hselectedDisjointTerminalBridge
      (hCprevSide hzC).1) (hterminalSideClosure hzTerminal)
  have happroachTerminalSide :
      Disjoint approach'.carrier terminalSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzTerminal
    exact (Set.disjoint_left.mp hselectedDisjointTerminalBridge
      (happroach'Side hzC).1) (hterminalSideClosure hzTerminal)
  have hfinalTerminalSide : Disjoint final'.carrier terminalSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzFinal hzTerminal
    have hz :
        z ∈ closure Vin ∩ closure TerminalBridgeRegion :=
      ⟨hfinalClosure hzFinal, hterminalSideClosure hzTerminal⟩
    rw [hclosureVinTerminalBridge] at hz
    exact hz
  have hgateSideDisjointQx : Disjoint gateSide.carrier Qx := by
    rw [Set.disjoint_left]
    intro z hzGate hzQ
    have hz :
        z ∈ closure TerminalSideRegion ∩ closure Qx :=
      ⟨hgateSideClosure hzGate, subset_closure hzQ⟩
    rw [hterminalSideClosureQx] at hz
    exact hz
  have hAarcSourceNotConnector : Aarc.source ∉ terminalConnector.carrier := by
    intro hz
    by_cases hzEndpoints :
        Aarc.source ∈
          ({quadrantGate, BplusArc.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
    · rcases hzEndpoints with hzQuad | hzTarget
      · have hEq : Aarc.source = quadrantGate := by simpa using hzQuad
        exact hquadrantAvoid (by
          rw [← hEq]
          simp only [Set.mem_union]
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem)))))
      · exact hAarcSourceNeTarget (by simpa using hzTarget)
    · have hzInterior : Aarc.source ∈ terminalConnector.relativeInterior := by
        rw [terminalConnector.relativeInterior_eq]
        refine ⟨hz, ?_⟩
        simpa [hterminalConnectorSource, hterminalConnectorTarget] using
          hzEndpoints
      have hzOpen : Aarc.source ∈
          openSegment ℝ quadrantGate BplusArc.target := by
        simpa [hterminalConnectorInterior] using hzInterior
      have hzForbidden :
          Aarc.source ∈
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H ∪ Bad) := by
        simp only [Set.mem_union]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem))))
      have :
          Aarc.source ∈
            openSegment ℝ quadrantGate BplusArc.target ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H ∪ Bad) :=
        ⟨hzOpen, hzForbidden⟩
      rw [hconnectorAvoid] at this
      exact this
  have hPqConnector :
      Disjoint Pq.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzPq hzConnector
    rcases hPcarrier (hPqCarrier hzPq) with hzSide | hzSource
    · exact (Set.disjoint_left.mp hselectedDisjointQx hzSide)
        (subset_closure (hconnectorSegment (by
          simpa [hterminalConnectorCarrier] using hzConnector)))
    · have hzEq : z = Aarc.source := by simpa using hzSource
      exact hAarcSourceNotConnector (by simpa [hzEq] using hzConnector)
  have hCprevConnector :
      Disjoint Cprev'.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzConnector
    have hzVin := (hCprevSide hzC).2
    have hzQ := hconnectorSegment (by
      simpa [hterminalConnectorCarrier] using hzConnector)
    have hz : z ∈ Vin ∩ Qx := ⟨hzVin, hzQ⟩
    rw [hVinQx] at hz
    exact hz
  have happroachConnector :
      Disjoint approach'.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzConnector
    have hzVin := (happroach'Side hzC).2
    have hzQ := hconnectorSegment (by
      simpa [hterminalConnectorCarrier] using hzConnector)
    have hz : z ∈ Vin ∩ Qx := ⟨hzVin, hzQ⟩
    rw [hVinQx] at hz
    exact hz
  have hfinalConnector :
      Disjoint final'.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzFinal hzConnector
    have hzQ := hconnectorSegment (by
      simpa [hterminalConnectorCarrier] using hzConnector)
    rcases hfinalVin hzFinal with hzVin | hzGate
    · have hz : z ∈ Vin ∩ Qx := ⟨hzVin, hzQ⟩
      rw [hVinQx] at hz
      exact hz
    · have hzEq : z = terminalGate := by simpa using hzGate
      exact hgateNotQx (by simpa [hzEq] using hzQ)
  have hgateSideConnector :
      Disjoint gateSide.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzGate hzConnector
    exact Set.disjoint_left.mp hgateSideDisjointQx hzGate
      (hconnectorSegment (by
        simpa [hterminalConnectorCarrier] using hzConnector))
  have hfirstPieceSubsetPq : firstPiece.carrier ⊆ Pq.carrier := by
    rw [hPqDecomposition]
    exact Set.subset_union_left
  have hremainderSubsetPq : remainder.carrier ⊆ Pq.carrier := by
    rw [hPqDecomposition]
    exact Set.subset_union_right
  have hfirstPieceCprev : Disjoint firstPiece.carrier Cprev'.carrier :=
    hfirstPieceDisjointChain.mono_right hCprevChain
  have hfirstPieceApproach : Disjoint firstPiece.carrier approach'.carrier :=
    hfirstPieceDisjointChain.mono_right happroachChain
  have hfirstPieceFinal : Disjoint firstPiece.carrier final'.carrier :=
    hfirstPieceDisjointChain.mono_right hfinalChain
  have hfirstPieceGateSide : Disjoint firstPiece.carrier gateSide.carrier :=
    hPqGateSide.mono_left hfirstPieceSubsetPq
  have hremainderGateSide : Disjoint remainder.carrier gateSide.carrier :=
    hPqGateSide.mono_left hremainderSubsetPq
  have hfirstPieceTerminalSide :
      Disjoint firstPiece.carrier terminalSide.carrier :=
    hPqTerminalSide.mono_left hfirstPieceSubsetPq
  have hremainderTerminalSide :
      Disjoint remainder.carrier terminalSide.carrier :=
    hPqTerminalSide.mono_left hremainderSubsetPq
  have hfirstPieceConnector :
      Disjoint firstPiece.carrier terminalConnector.carrier :=
    hPqConnector.mono_left hfirstPieceSubsetPq
  have hremainderConnector :
      Disjoint remainder.carrier terminalConnector.carrier :=
    hPqConnector.mono_left hremainderSubsetPq
  have hfirstCutAvoid :
      firstCut ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hzForbidden
    have hcutP : firstCut ∈ P.relativeInterior :=
      hPqInterior hfirstCutInterior
    by_cases hzH : firstCut ∈ H
    · exact hfirstCutNotClean ((hxClean firstCut).mpr ⟨hcutP, hzH⟩)
    · have hzNoH :
          firstCut ∈
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ Bad) := by
        rcases hzForbidden with (((((hzA | hzB) | hzBplus) | hzRbeta) | hzH') | hzBad)
        · exact Or.inl (Or.inl (Or.inl (Or.inl hzA)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hzB)))
        · exact Or.inl (Or.inl (Or.inr hzBplus))
        · exact Or.inl (Or.inr hzRbeta)
        · exact False.elim (hzH hzH')
        · exact Or.inr hzBad
      have hz :
          firstCut ∈ P.relativeInterior ∩
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ Bad) := ⟨hcutP, hzNoH⟩
      rw [hPavoid] at hz
      exact hz
  exact ⟨{
    q := q
    Pq := Pq
    firstCut := firstCut
    firstPiece := firstPiece
    remainder := remainder
    lastGate' := lastGate'
    h' := h'
    Cprev' := Cprev'
    approach' := approach'
    final' := final'
    gateSide := gateSide
    terminalSide := terminalSide
    terminalConnector := terminalConnector
    terminalGateAvoid := hterminalGateAvoid
    Pq_source := hPqSource
    Pq_target := hPqTarget
    Pq_interior := hPqInterior
    Pq_decomposition := hPqDecomposition
    firstPiece_remainder := hfirstPieceRemainder
    firstCut_not_clean := hfirstCutNotClean
    firstPiece_source := hfirstPieceSource
    firstPiece_target := hfirstPieceTarget
    remainder_source := hremainderSource
    remainder_target := hremainderTarget
    firstPiece_carrier := hfirstPieceCarrier
    firstPiece_interior := hfirstPieceInterior
    firstPiece_interior_Pq := hfirstPieceInteriorPq
    remainder_interior_Pq := hremainderInteriorPq
    split_transfer := hsplitTransfer
    Cprev_source := hCprevSource
    Cprev_target := hCprevTarget
    approach_source := happroach'Source
    approach_target := happroach'Target
    final_source := hfinalSource
    final_target := hfinalTarget
    Cprev_side := hCprevSide
    approach_side := happroach'Side
    final_carrier := hfinalCarrier
    final_interior_Vin := hfinalInteriorVin
    Pq_Cprev := hPqCprev
    Pq_approach := hPqApproach
    Pq_final := hPqFinal
    Cprev_approach := hCprevApproach
    approach_final := happroachFinal
    Cprev_final := hCprevFinal
    gateSide_source := hgateSideSource
    gateSide_target := hgateSideTarget
    gateSide_carrier := hgateSideCarrier
    gateSide_interior := hgateSideInterior
    terminalSide_source := hterminalSideSource
    terminalSide_target := hterminalSideTarget
    terminalSide_carrier := hterminalSideCarrier
    terminalSide_interior := hterminalSideInterior
    terminalConnector_source := hterminalConnectorSource
    terminalConnector_target := hterminalConnectorTarget
    terminalConnector_carrier := hterminalConnectorCarrier
    terminalConnector_interior := hterminalConnectorInterior
    gateSide_final := hgateSideFinal
    gateSide_terminalSide := hgateSideTerminalSide
    point_avoid_of_Vin := hpointAvoidOfVin
    forbidden_no_H_subset := hforbiddenNoHSubset
    terminalSideSource_avoid := hterminalSideSourceAvoid
    quadrant_avoid := hquadrantAvoid
    firstPiece_Cprev := hfirstPieceCprev
    firstPiece_approach := hfirstPieceApproach
    firstPiece_final := hfirstPieceFinal
    firstPiece_gateSide := hfirstPieceGateSide
    remainder_gateSide := hremainderGateSide
    Cprev_gateSide := hCprevGateSide
    approach_gateSide := happroachGateSide
    firstPiece_terminalSide := hfirstPieceTerminalSide
    remainder_terminalSide := hremainderTerminalSide
    Cprev_terminalSide := hCprevTerminalSide
    approach_terminalSide := happroachTerminalSide
    final_terminalSide := hfinalTerminalSide
    firstPiece_connector := hfirstPieceConnector
    remainder_connector := hremainderConnector
    Cprev_connector := hCprevConnector
    approach_connector := happroachConnector
    final_connector := hfinalConnector
    gateSide_connector := hgateSideConnector
    firstCut_avoid := hfirstCutAvoid }⟩

private lemma endpointSidePrefixTerminalAssembly_combinatorialFacts
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ctx : EndpointSidePrefixTerminalAssemblyContext
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean charge)
    (geom : EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean) :
    Nonempty (EndpointSidePrefixCombinatorialFacts Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean geom) := by
  have hPsource := ctx.hPsource
  have hPavoid := ctx.hPavoid
  have hterminalSideOpen := ctx.hterminalSideOpen
  have hterminalSideAvoid := ctx.hterminalSideAvoid
  let q := geom.q
  let firstPiece := geom.firstPiece
  let remainder := geom.remainder
  let lastGate' := geom.lastGate'
  let h' := geom.h'
  let Cprev' := geom.Cprev'
  let approach' := geom.approach'
  let final' := geom.final'
  let gateSide := geom.gateSide
  have hterminalGateAvoid := geom.terminalGateAvoid
  have hPqInterior := geom.Pq_interior
  have hfirstPieceRemainder := geom.firstPiece_remainder
  have hfirstPieceSource := geom.firstPiece_source
  have hfirstPieceTarget := geom.firstPiece_target
  have hremainderSource := geom.remainder_source
  have hremainderTarget := geom.remainder_target
  have hfirstPieceInteriorPq := geom.firstPiece_interior_Pq
  have hremainderInteriorPq := geom.remainder_interior_Pq
  have hCprevSource := geom.Cprev_source
  have hCprevTarget := geom.Cprev_target
  have happroach'Source := geom.approach_source
  have happroach'Target := geom.approach_target
  have hfinalSource := geom.final_source
  have hfinalTarget := geom.final_target
  have hCprevSide := geom.Cprev_side
  have happroach'Side := geom.approach_side
  have hfinalInteriorVin := geom.final_interior_Vin
  have hPqCprev := geom.Pq_Cprev
  have hCprevApproach := geom.Cprev_approach
  have happroachFinal := geom.approach_final
  have hgateSideSource := geom.gateSide_source
  have hgateSideTarget := geom.gateSide_target
  have hgateSideInterior := geom.gateSide_interior
  have hterminalSideSource := geom.terminalSide_source
  have hgateSideFinal := geom.gateSide_final
  have hfirstPieceCprev := geom.firstPiece_Cprev
  have hfirstPieceApproach := geom.firstPiece_approach
  have hfirstPieceFinal := geom.firstPiece_final
  have hfirstPieceGateSide := geom.firstPiece_gateSide
  have hPqApproach := geom.Pq_approach
  have hPqFinal := geom.Pq_final
  have hremainderGateSide := geom.remainder_gateSide
  have hCprevFinal := geom.Cprev_final
  have hCprevGateSide := geom.Cprev_gateSide
  have happroachGateSide := geom.approach_gateSide
  have hpointAvoidOfVin {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Vin) :
      z ∉ (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
        Rbeta ∪ H ∪ Bad) :=
    geom.point_avoid_of_Vin hz
  have hforbiddenNoHSubset := geom.forbidden_no_H_subset
  have hfirstCutAvoid := geom.firstCut_avoid
  have polygonalArc_source_mem (Γ : PolygonalArc) : Γ.source ∈ Γ.carrier :=
    endpoint_polygonalArc_source_mem Γ
  have polygonalArc_target_mem (Γ : PolygonalArc) : Γ.target ∈ Γ.carrier :=
    endpoint_polygonalArc_target_mem Γ
  exact ⟨{
      source := by
        simp [endpointSidePrefixPiece, hfirstPieceSource, hPsource]
      target := by
        simp [endpointSidePrefixPiece, hgateSideTarget, hterminalSideSource]
      consecutive_sources := by
        intro i hi
        interval_cases i
        · simpa [endpointSidePrefixPiece] using
            hfirstPieceTarget.trans hremainderSource.symm
        · simpa [endpointSidePrefixPiece] using hremainderTarget.trans hCprevSource.symm
        · simpa [endpointSidePrefixPiece] using hCprevTarget.trans happroach'Source.symm
        · simpa [endpointSidePrefixPiece] using happroach'Target.trans hfinalSource.symm
        · simpa [endpointSidePrefixPiece] using hfinalTarget.trans hgateSideSource.symm
      consecutive_meets := by
        intro i hi
        interval_cases i
        · rw [show (endpointSidePrefixPiece geom) 0 = firstPiece by rfl,
            show (endpointSidePrefixPiece geom) (0 + 1) = remainder by rfl,
            hfirstPieceTarget]
          exact hfirstPieceRemainder
        · rw [show (endpointSidePrefixPiece geom) 1 = remainder by rfl,
            show (endpointSidePrefixPiece geom) (1 + 1) = Cprev' by rfl, hremainderTarget]
          exact hPqCprev
        · rw [show (endpointSidePrefixPiece geom) 2 = Cprev' by rfl,
            show (endpointSidePrefixPiece geom) (2 + 1) = approach' by rfl, hCprevTarget]
          exact hCprevApproach
        · rw [show (endpointSidePrefixPiece geom) 3 = approach' by rfl,
            show (endpointSidePrefixPiece geom) (3 + 1) = final' by rfl, happroach'Target]
          exact happroachFinal
        · rw [show (endpointSidePrefixPiece geom) 4 = final' by rfl,
            show (endpointSidePrefixPiece geom) (4 + 1) = gateSide by rfl, hfinalTarget]
          exact hgateSideFinal
      nonconsecutive_disjoint := by
        intro i j hi hj hij
        interval_cases i <;> interval_cases j <;>
          simp_all [endpointSidePrefixPiece]
      internal_gates_avoid := by
        intro i hi
        interval_cases i
        · simpa [endpointSidePrefixPiece, hfirstPieceTarget] using hfirstCutAvoid
        · simp only [endpointSidePrefixPiece, hremainderTarget]
          have hqVin : q ∈ Vin := (hCprevSide (by
            simpa [q, Cprev', hCprevSource] using
              polygonalArc_source_mem Cprev')).2
          exact hpointAvoidOfVin hqVin
        · simp only [endpointSidePrefixPiece, hCprevTarget]
          have hlastVin : lastGate' ∈ Vin := (hCprevSide (by
            simpa [lastGate', Cprev', hCprevTarget] using
              polygonalArc_target_mem Cprev')).2
          exact hpointAvoidOfVin hlastVin
        · simp only [endpointSidePrefixPiece, happroach'Target]
          have hh'Vin : h' ∈ Vin := (happroach'Side (by
            simpa [h', approach', happroach'Target] using
              polygonalArc_target_mem approach')).2
          exact hpointAvoidOfVin hh'Vin
        · simpa [endpointSidePrefixPiece, hfinalTarget] using hterminalGateAvoid
      relative_interiors_avoid := by
        intro i hi
        interval_cases i
        · rw [show (endpointSidePrefixPiece geom) 0 = firstPiece by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hzP : z ∈ P.relativeInterior :=
            hPqInterior (hfirstPieceInteriorPq hz.1)
          have hz' :
              z ∈ P.relativeInterior ∩
                (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                  Rbeta ∪ Bad) := ⟨hzP, hz.2⟩
          rw [hPavoid] at hz'
          exact hz'
        · rw [show (endpointSidePrefixPiece geom) 1 = remainder by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hzP : z ∈ P.relativeInterior :=
            hPqInterior (hremainderInteriorPq hz.1)
          have hz' :
              z ∈ P.relativeInterior ∩
                (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                  Rbeta ∪ Bad) := ⟨hzP, hz.2⟩
          rw [hPavoid] at hz'
          exact hz'
        · rw [show (endpointSidePrefixPiece geom) 2 = Cprev' by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          exact hpointAvoidOfVin (hCprevSide
            ((by
              rw [Cprev'.relativeInterior_eq] at hz
              exact hz.1.1))).2 (hforbiddenNoHSubset hz.2)
        · rw [show (endpointSidePrefixPiece geom) 3 = approach' by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          exact hpointAvoidOfVin (happroach'Side
            ((by
              rw [approach'.relativeInterior_eq] at hz
              exact hz.1.1))).2 (hforbiddenNoHSubset hz.2)
        · rw [show (endpointSidePrefixPiece geom) 4 = final' by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          exact hpointAvoidOfVin (hfinalInteriorVin hz.1)
            (hforbiddenNoHSubset hz.2)
        · rw [show (endpointSidePrefixPiece geom) 5 = gateSide by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hzRegion : z ∈
              TerminalSideRegion ∪
                ({terminalGate, terminalSideSource} :
                  Set (EuclideanSpace ℝ (Fin 2))) :=
            Or.inl (hterminalSideOpen (by
              rw [← geom.gateSide_interior]
              exact hz.1))
          have hz' :
              z ∈
                (TerminalSideRegion ∪
                    ({terminalGate, terminalSideSource} :
                      Set (EuclideanSpace ℝ (Fin 2)))) ∩
                  ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                      Rbeta ∪ H) ∪ Bad) := by
            refine ⟨hzRegion, ?_⟩
            exact hforbiddenNoHSubset hz.2
          rw [hterminalSideAvoid] at hz'
          exact hz'
    }⟩

private lemma endpointSidePrefixTerminalAssembly_cleanFacts
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ctx : EndpointSidePrefixTerminalAssemblyContext
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean charge)
    (geom : EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean) :
    Nonempty (EndpointSidePrefixCleanFacts Aarc Barc BplusArc P SelectedSide
      Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate K XA xClean
      charge geom) := by
  have hxClean := ctx.hxClean
  have hchargeMem := ctx.hchargeMem
  have hchargeInj := ctx.hchargeInj
  have hclean := ctx.hclean
  have hterminalSideOpen := ctx.hterminalSideOpen
  have hterminalSideAvoid := ctx.hterminalSideAvoid
  let q := geom.q
  let Pq := geom.Pq
  let firstCut := geom.firstCut
  let firstPiece := geom.firstPiece
  let remainder := geom.remainder
  let Cprev' := geom.Cprev'
  let approach' := geom.approach'
  let final' := geom.final'
  have hPqSource := geom.Pq_source
  have hPqTarget := geom.Pq_target
  have hPqInterior := geom.Pq_interior
  have hPqDecomposition := geom.Pq_decomposition
  have hfirstCutNotClean := geom.firstCut_not_clean
  have hfirstPieceSource := geom.firstPiece_source
  have hfirstPieceTarget := geom.firstPiece_target
  have hremainderSource := geom.remainder_source
  have hremainderTarget := geom.remainder_target
  have hfirstPieceInteriorPq := geom.firstPiece_interior_Pq
  have hremainderInteriorPq := geom.remainder_interior_Pq
  have hsplitTransfer := geom.split_transfer
  have hCprevSide := geom.Cprev_side
  have happroach'Side := geom.approach_side
  have hfinalInteriorVin := geom.final_interior_Vin
  have hgateSideInterior := geom.gateSide_interior
  have hpointAvoidOfVin {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Vin) :
      z ∉ (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
        Rbeta ∪ H ∪ Bad) :=
    geom.point_avoid_of_Vin hz
  have polygonalArc_source_mem (Γ : PolygonalArc) : Γ.source ∈ Γ.carrier :=
    endpoint_polygonalArc_source_mem Γ
  have polygonalArc_target_mem (Γ : PolygonalArc) : Γ.target ∈ Γ.carrier :=
    endpoint_polygonalArc_target_mem Γ
  exact ⟨{
      spec := by
        intro z
        constructor
        · intro hz
          have hz' := (Finset.mem_filter.mp hz)
          have hzCarrier : z ∈ Pq.carrier := by
            rw [Pq.relativeInterior_eq] at hz'
            exact hz'.2.1
          rcases hPqDecomposition ▸ hzCarrier with hzFirst | hzRemainder
          · refine ⟨⟨0, by omega, ?_⟩, ?_⟩
            · rw [show (endpointSidePrefixPiece geom) 0 = firstPiece by rfl,
                firstPiece.relativeInterior_eq]
              refine ⟨hzFirst, ?_⟩
              intro hzEndpoints
              rcases hzEndpoints with hzSource | hzCut
              · have hzEq : z = P.source := by
                  exact hzSource.trans hfirstPieceSource
                have hzPqRI := hz'.2
                rw [Pq.relativeInterior_eq] at hzPqRI
                exact hzPqRI.2 (Or.inl (hzEq.trans hPqSource.symm))
              · have hzEq : z = firstCut := by
                  exact hzCut.trans hfirstPieceTarget
                exact hfirstCutNotClean (by simpa [hzEq] using hz'.1)
            · exact (hxClean z).mp hz'.1 |>.2
          · refine ⟨⟨1, by omega, ?_⟩, ?_⟩
            · rw [show (endpointSidePrefixPiece geom) 1 = remainder by rfl,
                remainder.relativeInterior_eq]
              refine ⟨hzRemainder, ?_⟩
              intro hzEndpoints
              rcases hzEndpoints with hzCut | hzTarget
              · have hzEq : z = firstCut := by
                  exact hzCut.trans hremainderSource
                exact hfirstCutNotClean (by simpa [hzEq] using hz'.1)
              · have hzEq : z = q := by
                  exact hzTarget.trans hremainderTarget
                have hzPqRI := hz'.2
                rw [Pq.relativeInterior_eq] at hzPqRI
                exact hzPqRI.2 (Or.inr (hzEq.trans hPqTarget.symm))
            · exact (hxClean z).mp hz'.1 |>.2
        · rintro ⟨⟨i, hi, hzPiece⟩, hzH⟩
          have hzPq : z ∈ Pq.relativeInterior := by
            interval_cases i
            · exact hfirstPieceInteriorPq (by
                simpa [endpointSidePrefixPiece] using hzPiece)
            · exact hremainderInteriorPq (by
                simpa [endpointSidePrefixPiece] using hzPiece)
            · exfalso
              have hzVin : z ∈ Vin := (hCprevSide (by
                have hzPiece' : z ∈ Cprev'.relativeInterior := by
                  simpa [endpointSidePrefixPiece] using hzPiece
                rw [Cprev'.relativeInterior_eq] at hzPiece'
                exact hzPiece'.1)).2
              exact hpointAvoidOfVin hzVin (by
                simp only [Set.mem_union]
                exact Or.inl (Or.inr hzH))
            · exfalso
              have hzVin : z ∈ Vin := (happroach'Side (by
                have hzPiece' : z ∈ approach'.relativeInterior := by
                  simpa [endpointSidePrefixPiece] using hzPiece
                rw [approach'.relativeInterior_eq] at hzPiece'
                exact hzPiece'.1)).2
              exact hpointAvoidOfVin hzVin (by
                simp only [Set.mem_union]
                exact Or.inl (Or.inr hzH))
            · exfalso
              have hzVin : z ∈ Vin := hfinalInteriorVin (by
                simpa [endpointSidePrefixPiece] using hzPiece)
              exact hpointAvoidOfVin hzVin (by
                simp only [Set.mem_union]
                exact Or.inl (Or.inr hzH))
            · exfalso
              have hzOpen : z ∈
                  openSegment ℝ terminalGate terminalSideSource := by
                simpa [endpointSidePrefixPiece, hgateSideInterior] using hzPiece
              have hzRegion :
                  z ∈ TerminalSideRegion ∪
                    ({terminalGate, terminalSideSource} :
                      Set (EuclideanSpace ℝ (Fin 2))) :=
                Or.inl (hterminalSideOpen hzOpen)
              have hz' :
                  z ∈
                    (TerminalSideRegion ∪
                        ({terminalGate, terminalSideSource} :
                          Set (EuclideanSpace ℝ (Fin 2)))) ∩
                      ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                          Rbeta ∪ H) ∪ Bad) := by
                refine ⟨hzRegion, ?_⟩
                simp only [Set.mem_union]
                exact Or.inl (Or.inr hzH)
              rw [hterminalSideAvoid] at hz'
              exact hz'
          apply Finset.mem_filter.mpr
          refine ⟨(hxClean z).mpr ⟨hPqInterior hzPq, hzH⟩, hzPq⟩
      charge_mem := by
        intro z hz
        exact hchargeMem z (Finset.mem_filter.mp hz).1
      charge_injective := by
        intro z w hz hw hEq
        exact hchargeInj z w (Finset.mem_filter.mp hz).1
          (Finset.mem_filter.mp hw).1 hEq
      clean := by
        intro z hz
        have hzFilter := Finset.mem_filter.mp hz
        obtain ⟨hzBad, hzPoints, j, hj, hzOld, hUnique⟩ :=
          hclean z hzFilter.1
        obtain ⟨s, hsSpec, hsUnique⟩ := hUnique
        have hzNeq : z ≠ q := by
          intro hEq
          have hzEndpoints : z ∈
              ({Pq.source, Pq.target} :
                Set (EuclideanSpace ℝ (Fin 2))) := by
            right
            simpa [hEq, Pq, q] using hPqTarget.symm
          have hzRI := hzFilter.2
          rw [Pq.relativeInterior_eq] at hzRI
          exact hzRI.2 hzEndpoints
        have hzCutNe : z ≠ firstCut := by
          intro hEq
          exact hfirstCutNotClean (by simpa [hEq] using hzFilter.1)
        have hzPqCarrier : z ∈ Pq.carrier := by
          rw [Pq.relativeInterior_eq] at hzFilter
          exact hzFilter.2.1
        rcases hPqDecomposition ▸ hzPqCarrier with hzFirst | hzRemainder
        · obtain ⟨j', hj', hzNew, c, hc, hdir⟩ :=
            hsplitTransfer firstPiece (by
                change geom.firstPiece ∈ [geom.firstPiece, geom.remainder]
                simp) z j hj hzOld
              hzFirst hzCutNe
              hzNeq
          refine ⟨hzBad, hzPoints, 0, by omega, j', hj', ?_, ?_⟩
          · simpa [endpointSidePrefixPiece] using hzNew
          · refine ⟨s, ?_, ?_⟩
            · refine ⟨hsSpec.1, hsSpec.2.1, ?_⟩
              intro hparallel
              rcases hparallel with ⟨d, hd⟩
              apply hsSpec.2.2
              refine ⟨d * c, ?_⟩
              change s.2 - s.1 = d •
                (firstPiece.vertices[j' + 1] - firstPiece.vertices[j']) at hd
              rw [hdir] at hd
              simpa [mul_smul] using hd
            · intro t ht
              apply hsUnique
              refine ⟨ht.1, ht.2.1, ?_⟩
              intro hparallel
              rcases hparallel with ⟨d, hd⟩
              apply ht.2.2
              refine ⟨d * c⁻¹, ?_⟩
              change t.2 - t.1 = (d * c⁻¹) •
                (firstPiece.vertices[j' + 1] - firstPiece.vertices[j'])
              rw [hdir]
              calc
                t.2 - t.1 = d • (P.vertices[j + 1] - P.vertices[j]) := hd
                _ = (d * c⁻¹) •
                      (c • (P.vertices[j + 1] - P.vertices[j])) := by
                  have hcoef : (d * c⁻¹) * c = d := by
                    field_simp
                  rw [← mul_smul, hcoef]
        · obtain ⟨j', hj', hzNew, c, hc, hdir⟩ :=
            hsplitTransfer remainder (by
                change geom.remainder ∈ [geom.firstPiece, geom.remainder]
                simp) z j hj hzOld
              hzRemainder hzCutNe
              hzNeq
          refine ⟨hzBad, hzPoints, 1, by omega, j', hj', ?_, ?_⟩
          · simpa [endpointSidePrefixPiece] using hzNew
          · refine ⟨s, ?_, ?_⟩
            · refine ⟨hsSpec.1, hsSpec.2.1, ?_⟩
              intro hparallel
              rcases hparallel with ⟨d, hd⟩
              apply hsSpec.2.2
              refine ⟨d * c, ?_⟩
              change s.2 - s.1 = d •
                (remainder.vertices[j' + 1] - remainder.vertices[j']) at hd
              rw [hdir] at hd
              simpa [mul_smul] using hd
            · intro t ht
              apply hsUnique
              refine ⟨ht.1, ht.2.1, ?_⟩
              intro hparallel
              rcases hparallel with ⟨d, hd⟩
              apply ht.2.2
              refine ⟨d * c⁻¹, ?_⟩
              change t.2 - t.1 = (d * c⁻¹) •
                (remainder.vertices[j' + 1] - remainder.vertices[j'])
              rw [hdir]
              calc
                t.2 - t.1 = d • (P.vertices[j + 1] - P.vertices[j]) := hd
                _ = (d * c⁻¹) •
                      (c • (P.vertices[j + 1] - P.vertices[j])) := by
                  have hcoef : (d * c⁻¹) * c = d := by
                    field_simp
                  rw [← mul_smul, hcoef]
    }⟩

private lemma endpointSidePrefixTerminalAssembly_terminalFacts
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ctx : EndpointSidePrefixTerminalAssemblyContext
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean charge)
    (geom : EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean) :
    Nonempty (EndpointSidePrefixTerminalFacts Aarc Barc BplusArc Rbeta H Bad
      DeltaX Qx K XA (endpointSidePrefixPiece geom) geom.terminalSide
      geom.terminalConnector quadrantGate) := by
  have hTerminalBridgeDelta := ctx.hTerminalBridgeDelta
  have hQxDelta := ctx.hQxDelta
  have hterminalSideSourceDelta := ctx.hterminalSideSourceDelta
  have hterminalSideSourceNeQuadrant := ctx.hterminalSideSourceNeQuadrant
  have hterminalBridgeSegment := ctx.hterminalBridgeSegment
  have hterminalBridgeOpen := ctx.hterminalBridgeOpen
  have hterminalBridgeAvoid := ctx.hterminalBridgeAvoid
  have hquadrantMemQx := ctx.hquadrantMemQx
  have hquadrantNeTarget := ctx.hquadrantNeTarget
  have hterminalBridgeMeetsQx := ctx.hterminalBridgeMeetsQx
  have hconnectorSegment := ctx.hconnectorSegment
  have hconnectorAvoid := ctx.hconnectorAvoid
  have hterminalSideSource := geom.terminalSide_source
  have hterminalSideTarget := geom.terminalSide_target
  have hterminalSideCarrier := geom.terminalSide_carrier
  have hterminalSideInterior := geom.terminalSide_interior
  have hterminalConnectorSource := geom.terminalConnector_source
  have hterminalConnectorTarget := geom.terminalConnector_target
  have hterminalConnectorCarrier := geom.terminalConnector_carrier
  have hterminalConnectorInterior := geom.terminalConnector_interior
  have hgateSideTerminalSide := geom.gateSide_terminalSide
  have hterminalSideSourceAvoid := geom.terminalSideSource_avoid
  have hquadrantAvoid := geom.quadrant_avoid
  have hfirstPieceTerminalSide := geom.firstPiece_terminalSide
  have hremainderTerminalSide := geom.remainder_terminalSide
  have hCprevTerminalSide := geom.Cprev_terminalSide
  have happroachTerminalSide := geom.approach_terminalSide
  have hfinalTerminalSide := geom.final_terminalSide
  have hfirstPieceConnector := geom.firstPiece_connector
  have hremainderConnector := geom.remainder_connector
  have hCprevConnector := geom.Cprev_connector
  have happroachConnector := geom.approach_connector
  have hfinalConnector := geom.final_connector
  have hgateSideConnector := geom.gateSide_connector
  have polygonalArc_source_mem (Γ : PolygonalArc) : Γ.source ∈ Γ.carrier :=
    endpoint_polygonalArc_source_mem Γ
  have polygonalArc_target_mem (Γ : PolygonalArc) : Γ.target ∈ Γ.carrier :=
    endpoint_polygonalArc_target_mem Γ
  exact ⟨{
      source_mem_delta := by
        simpa [hterminalSideSource] using hterminalSideSourceDelta
      source_not_mem_Q := by
        rw [hterminalSideSource]
        intro hzQ
        have hzSeg :
            terminalSideSource ∈
              segment ℝ terminalSideSource quadrantGate :=
          left_mem_segment ℝ terminalSideSource quadrantGate
        have hz :
            terminalSideSource ∈
              segment ℝ terminalSideSource quadrantGate ∩ Qx :=
          ⟨hzSeg, hzQ⟩
        rw [hterminalBridgeMeetsQx] at hz
        have : terminalSideSource = quadrantGate := by simpa using hz
        exact hterminalSideSourceNeQuadrant this
      source_avoid := by
        simpa [hterminalSideSource] using hterminalSideSourceAvoid
      side_target := hterminalSideTarget
      connector_source := hterminalConnectorSource
      connector_target := hterminalConnectorTarget
      omega_mem_Q := hquadrantMemQx
      omega_ne_target := hquadrantNeTarget
      omega_avoid := hquadrantAvoid
      side_subset_delta := by
        intro z hz
        have hz' := hterminalBridgeSegment (by
          simpa [hterminalSideCarrier] using hz)
        rcases hz' with hzRegion | hzEndpoint
        · exact hTerminalBridgeDelta hzRegion
        · rcases hzEndpoint with hzSource | hzQuad
          · have hzEq : z = terminalSideSource := by simpa using hzSource
            simpa [hzEq] using hterminalSideSourceDelta
          · have hzEq : z = quadrantGate := by simpa using hzQuad
            exact hQxDelta (by simpa [hzEq] using hquadrantMemQx)
      side_meets_Q := by
        simpa [hterminalSideCarrier] using hterminalBridgeMeetsQx
      side_relativeInterior_avoid := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzRegion :
            z ∈ TerminalBridgeRegion ∪
              ({terminalSideSource, quadrantGate} :
                Set (EuclideanSpace ℝ (Fin 2))) :=
          Or.inl (hterminalBridgeOpen (by
            simpa [hterminalSideInterior] using hz.1))
        have hz' :
            z ∈
              (TerminalBridgeRegion ∪
                  ({terminalSideSource, quadrantGate} :
                    Set (EuclideanSpace ℝ (Fin 2)))) ∩
                ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                    Rbeta ∪ H) ∪ Bad) := by
          refine ⟨hzRegion, ?_⟩
          simpa only [Set.union_assoc] using hz.2
        rw [hterminalBridgeAvoid] at hz'
        exact hz'
      connector_subset_Q := by
        simpa [hterminalConnectorCarrier] using hconnectorSegment
      connector_relativeInterior_avoid := by
        simpa [hterminalConnectorInterior] using hconnectorAvoid
      predecessor_meets_terminal := by
        simpa [endpointSidePrefixPiece, hterminalSideSource] using hgateSideTerminalSide
      earlier_prefix_disjoint_terminal := by
        intro i hi
        interval_cases i <;>
          simp [endpointSidePrefixPiece, hfirstPieceTerminalSide,
            hremainderTerminalSide, hCprevTerminalSide,
            happroachTerminalSide, hfinalTerminalSide]
      prefix_disjoint_terminal_connector := by
        intro i hi
        interval_cases i <;>
          simp [endpointSidePrefixPiece, hfirstPieceConnector, hremainderConnector,
            hCprevConnector,
            happroachConnector, hfinalConnector, hgateSideConnector]
    }⟩

private lemma endpointSidePrefixTerminalAssembly_attachment_from_geometry
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ctx : EndpointSidePrefixTerminalAssemblyContext
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean charge)
    (geom : EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean) :
    Nonempty (EndpointSidePrefixTerminalAttachmentStage Aarc Barc BplusArc
      Rbeta H Bad DeltaX Qx K XA geom.firstPiece geom.Cprev' geom.approach'
      geom.final' geom.gateSide geom.terminalSide geom.terminalConnector) := by
  obtain ⟨combinatorial⟩ :=
    endpointSidePrefixTerminalAssembly_combinatorialFacts
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean
      charge ctx geom
  obtain ⟨cleanFacts⟩ :=
    endpointSidePrefixTerminalAssembly_cleanFacts
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean
      charge ctx geom
  obtain ⟨terminalFacts⟩ :=
    endpointSidePrefixTerminalAssembly_terminalFacts
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean
      charge ctx geom
  let E : EndpointSidePrefixAttachment
      Aarc Barc BplusArc Rbeta H Bad DeltaX Qx K XA :=
    { r := 5
      prefixPiece := endpointSidePrefixPiece geom
      xPrefix := endpointSideXPrefix geom
      chargePrefix := charge
      omega := quadrantGate
      terminalSide := geom.terminalSide
      terminalConnector := geom.terminalConnector
      presentation_carrier := ctx.hK
      copied_prefix_disjoint_tail := ctx.hAarcRbeta
      prefix_source := combinatorial.source
      prefix_target := combinatorial.target
      prefix_consecutive_sources := combinatorial.consecutive_sources
      prefix_consecutive_meets := combinatorial.consecutive_meets
      prefix_nonconsecutive_disjoint := combinatorial.nonconsecutive_disjoint
      prefix_internal_gates_avoid := combinatorial.internal_gates_avoid
      prefix_relative_interiors_avoid := combinatorial.relative_interiors_avoid
      xPrefix_spec := cleanFacts.spec
      chargePrefix_mem := cleanFacts.charge_mem
      chargePrefix_injective := cleanFacts.charge_injective
      xPrefix_clean := cleanFacts.clean
      terminal_source_mem_delta := terminalFacts.source_mem_delta
      terminal_source_not_mem_Q := terminalFacts.source_not_mem_Q
      terminal_source_avoid := terminalFacts.source_avoid
      terminal_side_target := terminalFacts.side_target
      terminal_connector_source := terminalFacts.connector_source
      terminal_connector_target := terminalFacts.connector_target
      omega_mem_Q := terminalFacts.omega_mem_Q
      omega_ne_target := terminalFacts.omega_ne_target
      omega_avoid := terminalFacts.omega_avoid
      terminal_side_subset_delta := terminalFacts.side_subset_delta
      terminal_side_meets_Q := terminalFacts.side_meets_Q
      terminal_side_relativeInterior_avoid :=
        terminalFacts.side_relativeInterior_avoid
      terminal_connector_subset_Q := terminalFacts.connector_subset_Q
      terminal_connector_relativeInterior_avoid :=
        terminalFacts.connector_relativeInterior_avoid
      predecessor_meets_terminal := terminalFacts.predecessor_meets_terminal
      earlier_prefix_disjoint_terminal :=
        terminalFacts.earlier_prefix_disjoint_terminal
      prefix_disjoint_terminal_connector :=
        terminalFacts.prefix_disjoint_terminal_connector }
  exact ⟨{
    E := E
    r_eq := by simp [E]
    piece_zero := by simp [E, endpointSidePrefixPiece]
    piece_r_sub_three := by simp [E, endpointSidePrefixPiece]
    piece_r_sub_two := by simp [E, endpointSidePrefixPiece]
    piece_r_sub_one := by simp [E, endpointSidePrefixPiece]
    piece_r := by simp [E, endpointSidePrefixPiece]
    terminal_side := by simp [E]
    terminal_connector := by simp [E] }⟩

private lemma endpointSidePrefixTerminalAssembly_finish_from_geometry
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ctx : EndpointSidePrefixTerminalAssemblyContext
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean charge)
    (geom : EndpointSidePrefixTerminalAssemblyGeometry Aarc Barc BplusArc P
      SelectedSide Rbeta H Bad Vin terminalGate terminalSideSource quadrantGate
      xClean)
    (stage : EndpointSidePrefixTerminalAttachmentStage Aarc Barc BplusArc
      Rbeta H Bad DeltaX Qx K XA geom.firstPiece geom.Cprev' geom.approach'
      geom.final' geom.gateSide geom.terminalSide geom.terminalConnector) :
    Nonempty (EndpointSidePrefixTerminalAssemblyPrepared Aarc Barc BplusArc
      Rbeta H Bad DeltaX Qx SelectedSide StartSector terminalGate
      terminalSideSource quadrantGate K XA) := by
  exact ⟨
    { E := stage.E
      prefix_source := stage.E.prefix_source
      prefix_carrier := by
        rw [stage.piece_zero]
        exact geom.firstPiece_carrier.trans ctx.hfirst.choose_spec.1
      prefix_interior := by
        rw [stage.piece_zero]
        exact geom.firstPiece_interior.trans ctx.hfirst.choose_spec.2
      r_ge := by
        rw [stage.r_eq]
        omega
      h' := geom.h'
      lastGate' := geom.lastGate'
      Vin' := Vin
      cprev_side := by
        rw [stage.piece_r_sub_three]
        exact geom.Cprev_side
      approach_side := by
        rw [stage.piece_r_sub_two]
        exact geom.approach_side
      cprev_target := by
        rw [stage.piece_r_sub_three]
        exact geom.Cprev_target
      approach_source := by
        rw [stage.piece_r_sub_two]
        exact geom.approach_source
      cprev_approach := by
        rw [stage.piece_r_sub_three, stage.piece_r_sub_two]
        exact geom.Cprev_approach
      approach_target := by
        rw [stage.piece_r_sub_two]
        exact geom.approach_target
      final_source := by
        rw [stage.piece_r_sub_one]
        exact geom.final_source
      final_target := by
        rw [stage.piece_r_sub_one]
        exact geom.final_target
      approach_final := by
        rw [stage.piece_r_sub_two, stage.piece_r_sub_one]
        exact geom.approach_final
      final_carrier := by
        rw [stage.piece_r_sub_one]
        exact geom.final_carrier
      cprev_final := by
        rw [stage.piece_r_sub_three, stage.piece_r_sub_one]
        exact geom.Cprev_final
      gate_side_source := by
        rw [stage.piece_r]
        exact geom.gateSide_source
      gate_side_final := by
        rw [stage.piece_r_sub_one, stage.piece_r]
        exact geom.gateSide_final
      gate_side_carrier := by
        rw [stage.piece_r]
        exact geom.gateSide_carrier
      terminal_side_carrier := by
        rw [stage.terminal_side]
        exact geom.terminalSide_carrier
      terminal_connector_carrier := by
        rw [stage.terminal_connector]
        exact geom.terminalConnector_carrier }⟩

private lemma endpointSidePrefixTerminalAssembly_prepare_from_context
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (ctx : EndpointSidePrefixTerminalAssemblyContext
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean charge) :
    Nonempty (EndpointSidePrefixTerminalAssemblyPrepared Aarc Barc BplusArc
      Rbeta H Bad DeltaX Qx SelectedSide StartSector terminalGate
      terminalSideSource quadrantGate K XA) := by
  obtain ⟨geom⟩ :=
    endpointSidePrefixTerminalAssembly_geometry_from_context
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean
      charge ctx
  obtain ⟨stage⟩ :=
    endpointSidePrefixTerminalAssembly_attachment_from_geometry
      Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean
      charge ctx geom
  exact endpointSidePrefixTerminalAssembly_finish_from_geometry
    Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
    StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
    terminalGate terminalSideSource quadrantGate h lastGate K XA xClean
    charge ctx geom stage


private lemma endpointSidePrefixTerminalAssembly_prepare
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    K.carrier = H →
      Disjoint Aarc.carrier Rbeta →
        Aarc.source ∉ SelectedSide →
          Aarc.source ≠ BplusArc.target →
            terminalGate ∉ SelectedSide →
            SelectedSide ∩
                (closure TerminalSideRegion ∪
                  closure TerminalBridgeRegion ∪ closure Qx) =
              (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
              TerminalSideRegion ⊆ DeltaX →
                TerminalBridgeRegion ⊆ DeltaX →
                  Qx ⊆ DeltaX →
            P.source = Aarc.source →
          P.target = predecessor.source →
            P.carrier ⊆
              SelectedSide ∪
                ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) →
              P.relativeInterior ∩
                  (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                    Rbeta ∪ Bad) =
                (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
              Set.Finite
                (P.carrier ∩
                  (predecessor.carrier ∪ approach.carrier ∪
                    segment ℝ h terminalGate)) →
                (∃ hfirst : 0 + 1 < P.vertices.length,
                  segment ℝ P.vertices[0] P.vertices[1] ⊆
                      StartSector ∪
                        ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    openSegment ℝ P.vertices[0] P.vertices[1] ⊆ StartSector) →
                (∀ z : EuclideanSpace ℝ (Fin 2),
                  z ∈ xClean ↔ z ∈ P.relativeInterior ∧ z ∈ H) →
                  (∀ z : EuclideanSpace ℝ (Fin 2),
                    z ∈ xClean → charge z ∈ XA) →
                    (∀ z w : EuclideanSpace ℝ (Fin 2),
                      z ∈ xClean → w ∈ xClean →
                        charge z = charge w → z = w) →
                      (∀ z : EuclideanSpace ℝ (Fin 2),
                        z ∈ xClean →
                          z ∉ Bad ∧
                            z ∉ (K.points : Set (EuclideanSpace ℝ (Fin 2))) ∧
                              ∃ j : ℕ,
                                ∃ hj : j + 1 < P.vertices.length,
                                  z ∈ openSegment ℝ
                                      P.vertices[j] P.vertices[j + 1] ∧
                                    ∃! s :
                                      EuclideanSpace ℝ (Fin 2) ×
                                        EuclideanSpace ℝ (Fin 2),
                                      s ∈ K.segments ∧
                                        z ∈ openSegment ℝ s.1 s.2 ∧
                                          ¬ ∃ c : ℝ,
                                            s.2 - s.1 =
                                              c • (P.vertices[j + 1] - P.vertices[j])) →
                        predecessor.carrier ⊆ SelectedSide ∩ Vin →
                          approach.carrier ⊆ SelectedSide ∩ Vin →
                            predecessor.target = lastGate →
                              approach.source = lastGate →
                                predecessor.carrier ∩ approach.carrier =
                                  ({lastGate} : Set (EuclideanSpace ℝ (Fin 2))) →
                                  approach.target = h →
                                    approach.carrier ∩ segment ℝ h terminalGate =
                                      ({h} : Set (EuclideanSpace ℝ (Fin 2))) →
                                      Disjoint predecessor.carrier
                                        (segment ℝ h terminalGate) →
                                        h ∈ Vin →
                                          h ≠ terminalGate →
                                            h ∉
                                              (Aarc.carrier ∪ Barc.carrier ∪
                                                BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) →
                                            Vin ⊆ SelectedSide →
                                              Vin ⊆ DeltaX →
                                                Vin ∩ Qx =
                                                  (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                  Vin ∩
                                                      ((Aarc.carrier ∪ Barc.carrier ∪
                                                          BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                    (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                    terminalGate ∈ closure Vin →
                                                      terminalGate ∉ Vin →
                                                        segment ℝ h terminalGate ⊆
                                                          Vin ∪
                                                            ({terminalGate} :
                                                              Set (EuclideanSpace ℝ (Fin 2))) →
                                                          openSegment ℝ h terminalGate ⊆ Vin →
                                                            segment ℝ h terminalGate ∩
                                                                (TerminalSideRegion ∪
                                                                  ({terminalGate} :
                                                                    Set (EuclideanSpace ℝ (Fin 2)))) =
                                                              ({terminalGate} :
                                                                Set (EuclideanSpace ℝ (Fin 2))) →
                                                            closure Vin ∩
                                                                closure TerminalSideRegion =
                                                              ({terminalGate} :
                                                                Set (EuclideanSpace ℝ (Fin 2))) →
                                                              closure Vin ∩
                                                                  closure TerminalBridgeRegion =
                                                                (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                              terminalGate ∈ DeltaX →
                                                                terminalGate ∉ Qx →
                                                                  terminalSideSource ∈ DeltaX →
                                                                    terminalGate ≠ terminalSideSource →
                                                                      segment ℝ terminalGate terminalSideSource ⊆
                                                                        TerminalSideRegion ∪
                                                                          ({terminalGate, terminalSideSource} :
                                                                            Set (EuclideanSpace ℝ (Fin 2))) →
                                                                        openSegment ℝ terminalGate terminalSideSource ⊆
                                                                          TerminalSideRegion →
                                                                          (TerminalSideRegion ∪
                                                                              ({terminalGate, terminalSideSource} :
                                                                                Set (EuclideanSpace ℝ (Fin 2)))) ∩
                                                                              ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                  BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                                            (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                            terminalSideSource ≠ quadrantGate →
                                                                              segment ℝ terminalSideSource quadrantGate ⊆
                                                                                TerminalBridgeRegion ∪
                                                                                  ({terminalSideSource, quadrantGate} :
                                                                                    Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                openSegment ℝ terminalSideSource quadrantGate ⊆
                                                                                  TerminalBridgeRegion →
                                                                                  (TerminalBridgeRegion ∪
                                                                                      ({terminalSideSource, quadrantGate} :
                                                                                        Set (EuclideanSpace ℝ (Fin 2)))) ∩
                                                                                      ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                          BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                                                    (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                    quadrantGate ∈ Qx →
                                                                                      quadrantGate ≠ BplusArc.target →
                                                                                        segment ℝ terminalSideSource quadrantGate ∩ Qx =
                                                                                          ({quadrantGate} :
                                                                                            Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                        closure TerminalSideRegion ∩
                                                                                            closure TerminalBridgeRegion =
                                                                                          ({terminalSideSource} :
                                                                                            Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                          closure TerminalSideRegion ∩ closure Qx =
                                                                                            (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                            closure TerminalBridgeRegion ∩ closure Qx =
                                                                                              ({quadrantGate} :
                                                                                                Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                              segment ℝ quadrantGate BplusArc.target ⊆ Qx →
                                                                                                openSegment ℝ quadrantGate BplusArc.target ∩
                                                                                                    ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                                        BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                                                                  (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      Nonempty (EndpointSidePrefixTerminalAssemblyPrepared Aarc Barc BplusArc
        Rbeta H Bad DeltaX Qx SelectedSide StartSector terminalGate
        terminalSideSource quadrantGate K XA) := by
  intro hK hAarcRbeta hAarcSourceNotSide hAarcSourceNeTarget
    hterminalGateNotSide hsideTerminalSep hTerminalSideDelta
    hTerminalBridgeDelta hQxDelta hPsource hPtarget hPcarrier
    hPavoid hfinite hfirst hxClean hchargeMem hchargeInj hclean
    hpredecessorSide happroachSide hpredecessorTarget happroachSource
    hpredecessorApproach happroachTarget happroachSegment
    hpredecessorSegment hhVin hhNeGate hhAvoid hVinSide hVinDelta
    hVinQx hVinAvoid hgateClosure hgateNotVin hsegmentVin hopenSegmentVin
    hsegmentTerminalSide hclosureVinTerminalSide hclosureVinTerminalBridge
    hgateDelta hgateNotQx hterminalSideSourceDelta hgateNeTerminalSideSource
    hterminalSideSegment hterminalSideOpen hterminalSideAvoid
    hterminalSideSourceNeQuadrant hterminalBridgeSegment hterminalBridgeOpen
    hterminalBridgeAvoid hquadrantMemQx hquadrantNeTarget
    hterminalBridgeMeetsQx hterminalClosuresMeet hterminalSideClosureQx
    hterminalBridgeClosureQx hconnectorSegment hconnectorAvoid
  exact endpointSidePrefixTerminalAssembly_prepare_from_context
    Aarc Barc BplusArc P predecessor approach SelectedSide Rbeta H Bad
      StartSector DeltaX Qx TerminalSideRegion TerminalBridgeRegion Vin
      terminalGate terminalSideSource quadrantGate h lastGate K XA xClean charge
    {
      hK := hK
      hAarcRbeta := hAarcRbeta
      hAarcSourceNotSide := hAarcSourceNotSide
      hAarcSourceNeTarget := hAarcSourceNeTarget
      hterminalGateNotSide := hterminalGateNotSide
      hsideTerminalSep := hsideTerminalSep
      hTerminalSideDelta := hTerminalSideDelta
      hTerminalBridgeDelta := hTerminalBridgeDelta
      hQxDelta := hQxDelta
      hPsource := hPsource
      hPtarget := hPtarget
      hPcarrier := hPcarrier
      hPavoid := hPavoid
      hfinite := hfinite
      hfirst := hfirst
      hxClean := hxClean
      hchargeMem := hchargeMem
      hchargeInj := hchargeInj
      hclean := hclean
      hpredecessorSide := hpredecessorSide
      happroachSide := happroachSide
      hpredecessorTarget := hpredecessorTarget
      happroachSource := happroachSource
      hpredecessorApproach := hpredecessorApproach
      happroachTarget := happroachTarget
      happroachSegment := happroachSegment
      hpredecessorSegment := hpredecessorSegment
      hhVin := hhVin
      hhNeGate := hhNeGate
      hhAvoid := hhAvoid
      hVinSide := hVinSide
      hVinDelta := hVinDelta
      hVinQx := hVinQx
      hVinAvoid := hVinAvoid
      hgateClosure := hgateClosure
      hgateNotVin := hgateNotVin
      hsegmentVin := hsegmentVin
      hopenSegmentVin := hopenSegmentVin
      hsegmentTerminalSide := hsegmentTerminalSide
      hclosureVinTerminalSide := hclosureVinTerminalSide
      hclosureVinTerminalBridge := hclosureVinTerminalBridge
      hgateDelta := hgateDelta
      hgateNotQx := hgateNotQx
      hterminalSideSourceDelta := hterminalSideSourceDelta
      hgateNeTerminalSideSource := hgateNeTerminalSideSource
      hterminalSideSegment := hterminalSideSegment
      hterminalSideOpen := hterminalSideOpen
      hterminalSideAvoid := hterminalSideAvoid
      hterminalSideSourceNeQuadrant := hterminalSideSourceNeQuadrant
      hterminalBridgeSegment := hterminalBridgeSegment
      hterminalBridgeOpen := hterminalBridgeOpen
      hterminalBridgeAvoid := hterminalBridgeAvoid
      hquadrantMemQx := hquadrantMemQx
      hquadrantNeTarget := hquadrantNeTarget
      hterminalBridgeMeetsQx := hterminalBridgeMeetsQx
      hterminalClosuresMeet := hterminalClosuresMeet
      hterminalSideClosureQx := hterminalSideClosureQx
      hterminalBridgeClosureQx := hterminalBridgeClosureQx
      hconnectorSegment := hconnectorSegment
      hconnectorAvoid := hconnectorAvoid }
lemma EndpointSidePrefixTerminalAssembly
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    K.carrier = H →
      Disjoint Aarc.carrier Rbeta →
        Aarc.source ∉ SelectedSide →
          Aarc.source ≠ BplusArc.target →
            terminalGate ∉ SelectedSide →
            SelectedSide ∩
                (closure TerminalSideRegion ∪
                  closure TerminalBridgeRegion ∪ closure Qx) = ∅ →
              TerminalSideRegion ⊆ DeltaX →
                TerminalBridgeRegion ⊆ DeltaX →
                  Qx ⊆ DeltaX →
            P.source = Aarc.source →
          P.target = predecessor.source →
            P.carrier ⊆ SelectedSide ∪ ({Aarc.source} : Set _) →
              P.relativeInterior ∩
                  (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                    Rbeta ∪ Bad) = ∅ →
              Set.Finite
                (P.carrier ∩
                  (predecessor.carrier ∪ approach.carrier ∪
                    segment ℝ h terminalGate)) →
                (∃ hfirst : 0 + 1 < P.vertices.length,
                  segment ℝ P.vertices[0] P.vertices[1] ⊆
                      StartSector ∪ ({Aarc.source} : Set _) ∧
                    openSegment ℝ P.vertices[0] P.vertices[1] ⊆ StartSector) →
                (∀ z, z ∈ xClean ↔ z ∈ P.relativeInterior ∧ z ∈ H) →
                  (∀ z, z ∈ xClean → charge z ∈ XA) →
                    (∀ z w, z ∈ xClean → w ∈ xClean →
                      charge z = charge w → z = w) →
                      (∀ z, z ∈ xClean →
                        z ∉ Bad ∧ z ∉ (K.points : Set _) ∧
                          ∃ j, ∃ hj : j + 1 < P.vertices.length,
                            z ∈ openSegment ℝ P.vertices[j] P.vertices[j + 1] ∧
                              ∃! s : EuclideanSpace ℝ (Fin 2) ×
                                  EuclideanSpace ℝ (Fin 2),
                                s ∈ K.segments ∧
                                  z ∈ openSegment ℝ s.1 s.2 ∧
                                    ¬ ∃ c : ℝ, s.2 - s.1 =
                                      c • (P.vertices[j + 1] - P.vertices[j])) →
                        predecessor.carrier ⊆ SelectedSide ∩ Vin →
                          approach.carrier ⊆ SelectedSide ∩ Vin →
                            predecessor.target = lastGate →
                              approach.source = lastGate →
                                predecessor.carrier ∩ approach.carrier =
                                  ({lastGate} : Set _) →
                                  approach.target = h →
                                    approach.carrier ∩ segment ℝ h terminalGate =
                                      ({h} : Set _) →
                                      Disjoint predecessor.carrier
                                        (segment ℝ h terminalGate) →
                                        h ∈ Vin → h ≠ terminalGate →
                                          h ∉ (Aarc.carrier ∪ Barc.carrier ∪
                                            BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) →
                                            Vin ⊆ SelectedSide → Vin ⊆ DeltaX →
                                              Vin ∩ Qx = ∅ →
                                                Vin ∩ ((Aarc.carrier ∪ Barc.carrier ∪
                                                  BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) = ∅ →
                                                  terminalGate ∈ closure Vin →
                                                    terminalGate ∉ Vin →
                                                      segment ℝ h terminalGate ⊆
                                                        Vin ∪ ({terminalGate} : Set _) →
                                                        openSegment ℝ h terminalGate ⊆ Vin →
                                                          segment ℝ h terminalGate ∩
                                                              (TerminalSideRegion ∪
                                                                ({terminalGate} : Set _)) =
                                                            ({terminalGate} : Set _) →
                                                            closure Vin ∩ closure TerminalSideRegion =
                                                              ({terminalGate} : Set _) →
                                                              closure Vin ∩ closure TerminalBridgeRegion = ∅ →
                                                                terminalGate ∈ DeltaX →
                                                                  terminalGate ∉ Qx →
                                                                    terminalSideSource ∈ DeltaX →
                                                                      terminalGate ≠ terminalSideSource →
                                                                        segment ℝ terminalGate terminalSideSource ⊆
                                                                          TerminalSideRegion ∪
                                                                            ({terminalGate, terminalSideSource} : Set _) →
                                                                          openSegment ℝ terminalGate terminalSideSource ⊆
                                                                            TerminalSideRegion →
                                                                            (TerminalSideRegion ∪
                                                                                ({terminalGate, terminalSideSource} : Set _)) ∩
                                                                                ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                  BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) = ∅ →
                                                                              terminalSideSource ≠ quadrantGate →
                                                                                segment ℝ terminalSideSource quadrantGate ⊆
                                                                                  TerminalBridgeRegion ∪
                                                                                    ({terminalSideSource, quadrantGate} : Set _) →
                                                                                  openSegment ℝ terminalSideSource quadrantGate ⊆
                                                                                    TerminalBridgeRegion →
                                                                                    (TerminalBridgeRegion ∪
                                                                                        ({terminalSideSource, quadrantGate} : Set _)) ∩
                                                                                        ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                          BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) = ∅ →
                                                                                      quadrantGate ∈ Qx →
                                                                                        quadrantGate ≠ BplusArc.target →
                                                                                          segment ℝ terminalSideSource quadrantGate ∩ Qx =
                                                                                            ({quadrantGate} : Set _) →
                                                                                          closure TerminalSideRegion ∩
                                                                                              closure TerminalBridgeRegion =
                                                                                            ({terminalSideSource} : Set _) →
                                                                                            closure TerminalSideRegion ∩ closure Qx = ∅ →
                                                                                              closure TerminalBridgeRegion ∩ closure Qx =
                                                                                                ({quadrantGate} : Set _) →
                                                                                                segment ℝ quadrantGate BplusArc.target ⊆ Qx →
                                                                                                  openSegment ℝ quadrantGate BplusArc.target ∩
                                                                                                      ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                                        BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) = ∅ →
      ∃ E : EndpointSidePrefixAttachment
          Aarc Barc BplusArc Rbeta H Bad DeltaX Qx K XA,
        (E.prefixPiece 0).source = Aarc.source ∧
          (E.prefixPiece 0).carrier ⊆
              StartSector ∪ ({Aarc.source} : Set _) ∧
            (E.prefixPiece 0).relativeInterior ⊆ StartSector ∧
              3 ≤ E.r ∧
                ∃ h' lastGate' : EuclideanSpace ℝ (Fin 2),
                  ∃ Vin' : Set (EuclideanSpace ℝ (Fin 2)),
                    (E.prefixPiece (E.r - 3)).carrier ⊆ SelectedSide ∩ Vin' ∧
                      (E.prefixPiece (E.r - 2)).carrier ⊆ SelectedSide ∩ Vin' ∧
                        (E.prefixPiece (E.r - 3)).target = lastGate' ∧
                          (E.prefixPiece (E.r - 2)).source = lastGate' ∧
                            (E.prefixPiece (E.r - 3)).carrier ∩
                                (E.prefixPiece (E.r - 2)).carrier = ({lastGate'} : Set _) ∧
                              (E.prefixPiece (E.r - 2)).target = h' ∧
                                (E.prefixPiece (E.r - 1)).source = h' ∧
                                  (E.prefixPiece (E.r - 1)).target = terminalGate ∧
                                    (E.prefixPiece (E.r - 2)).carrier ∩
                                        (E.prefixPiece (E.r - 1)).carrier = ({h'} : Set _) ∧
                                      (E.prefixPiece (E.r - 1)).carrier =
                                        segment ℝ h' terminalGate ∧
                                        Disjoint (E.prefixPiece (E.r - 3)).carrier
                                          (E.prefixPiece (E.r - 1)).carrier ∧
                                          (E.prefixPiece E.r).source = terminalGate ∧
                                            (E.prefixPiece (E.r - 1)).carrier ∩
                                                (E.prefixPiece E.r).carrier =
                                              ({terminalGate} : Set _) ∧
                                              (E.prefixPiece E.r).carrier =
                                                segment ℝ terminalGate terminalSideSource ∧
                                                E.terminalSide.carrier =
                                                  segment ℝ terminalSideSource quadrantGate ∧
                                                  E.terminalConnector.carrier =
                                                    segment ℝ quadrantGate BplusArc.target :=
  fun hK hAarcRbeta hAarcSourceNotSide hAarcSourceNeTarget
      hterminalGateNotSide hsideTerminalSep hTerminalSideDelta
      hTerminalBridgeDelta hQxDelta hPsource hPtarget hPcarrier
      hPavoid hfinite hfirst hxClean hchargeMem hchargeInj hclean
      hpredecessorSide happroachSide hpredecessorTarget happroachSource
      hpredecessorApproach happroachTarget happroachSegment
      hpredecessorSegment hhVin hhNeGate hhAvoid hVinSide hVinDelta
      hVinQx hVinAvoid hgateClosure hgateNotVin hsegmentVin hopenSegmentVin
      hsegmentTerminalSide hclosureVinTerminalSide hclosureVinTerminalBridge
      hgateDelta hgateNotQx hterminalSideSourceDelta hgateNeTerminalSideSource
      hterminalSideSegment hterminalSideOpen hterminalSideAvoid
      hterminalSideSourceNeQuadrant hterminalBridgeSegment hterminalBridgeOpen
      hterminalBridgeAvoid hquadrantMemQx hquadrantNeTarget
      hterminalBridgeMeetsQx hterminalClosuresMeet hterminalSideClosureQx
      hterminalBridgeClosureQx hconnectorSegment hconnectorAvoid => by
    obtain ⟨prep⟩ := endpointSidePrefixTerminalAssembly_prepare Aarc Barc BplusArc P
      predecessor approach SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin terminalGate
      terminalSideSource quadrantGate h lastGate K XA xClean charge hK
      hAarcRbeta hAarcSourceNotSide hAarcSourceNeTarget hterminalGateNotSide
      hsideTerminalSep hTerminalSideDelta hTerminalBridgeDelta hQxDelta
      hPsource hPtarget hPcarrier hPavoid hfinite hfirst hxClean hchargeMem
      hchargeInj hclean hpredecessorSide happroachSide hpredecessorTarget
      happroachSource hpredecessorApproach happroachTarget happroachSegment
      hpredecessorSegment hhVin hhNeGate hhAvoid hVinSide hVinDelta hVinQx
      hVinAvoid hgateClosure hgateNotVin hsegmentVin hopenSegmentVin
      hsegmentTerminalSide hclosureVinTerminalSide hclosureVinTerminalBridge
      hgateDelta hgateNotQx hterminalSideSourceDelta hgateNeTerminalSideSource
      hterminalSideSegment hterminalSideOpen hterminalSideAvoid
      hterminalSideSourceNeQuadrant hterminalBridgeSegment hterminalBridgeOpen
      hterminalBridgeAvoid hquadrantMemQx hquadrantNeTarget
      hterminalBridgeMeetsQx hterminalClosuresMeet hterminalSideClosureQx
      hterminalBridgeClosureQx hconnectorSegment hconnectorAvoid
    exact ⟨prep.E, prep.prefix_source, prep.prefix_carrier,
      prep.prefix_interior, prep.r_ge, prep.h', prep.lastGate', prep.Vin',
      prep.cprev_side, prep.approach_side, prep.cprev_target,
      prep.approach_source, prep.cprev_approach, prep.approach_target,
      prep.final_source, prep.final_target, prep.approach_final,
      prep.final_carrier, prep.cprev_final, prep.gate_side_source,
      prep.gate_side_final, prep.gate_side_carrier,
      prep.terminal_side_carrier, prep.terminal_connector_carrier⟩
