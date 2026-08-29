/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayExplicitStageResidual

/-!
# The localized front-plus-tail row at an explicit old stage

The existing interval localization proof is carried over with actual old
and later indices. The old stage need not be in the avoiding club. The
chosen safe path, bounded alternating components, literal ordinary survivors
and reference-missing certificate are all retained. This includes stage zero
without constructing a spurious preceding stage.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ExplicitStageInterval

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open ControlledSlices SliceCandidate

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- A first-hit prefix family is tight at the stopping set. -/
private theorem firstHitPrefixFamily_meetsOnlyAtTerminal
    {G : DWeb V} {A T C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G A T W)
    (hsep : RelationalRoof.Separates G.graph.Adj A T C) :
    SliceSpliceSource.MeetsOnlyAtTerminal G
      (firstHitPrefixFamily hW hsep) C := by
  rintro _ ⟨a, rfl⟩ x hx hxC
  have hxInter : x ∈ (linkageFirstHitAt hW hsep a).support ∩ C :=
    ⟨hx, hxC⟩
  rw [linkageFirstHitAt_targetPure hW hsep a] at hxInter
  have hxEq : x = (linkageFirstHitAt hW hsep a).finish :=
    Set.mem_singleton_iff.1 hxInter
  subst x
  rfl

/-- A tight old-to-new stage linkage lifts entirely into the ambient roof
of the new frontier. -/
private theorem stageLinkage_vertexSet_subset_outerRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {alpha beta : Stage (succ kappa)} (hab : alpha < beta)
    {A : Set V} {W : Set (C.ladder.stageWeb alpha).DPath}
    (hA : A ⊆ (C.ladder.frontier alpha))
    (hW : IsLinkageBetween (C.ladder.stageWeb alpha)
      A (C.ladder.frontier beta) W)
    (htight : SliceSpliceSource.MeetsOnlyAtTerminal
      (C.ladder.stageWeb alpha) W (C.ladder.frontier beta)) :
    (C.ladder.stageWeb alpha).vertexSet W ⊆ (Gamma.roof (C.ladder.frontier beta)) := by
  let H := C.ladder.stageWeb alpha
  rintro x ⟨p, hpW, hxp⟩
  obtain ⟨f, rfl⟩ := hW.finiteCharacter hpW
  let q : FinitePath Gamma.graph :=
    SliceSegmentCore.liftStageFinitePath C.ladder alpha f
  have hxq : x ∈ q.support := by
    change x ∈ f.support at hxp
    simpa only [q, SliceSegmentCore.liftStageFinitePath_support] using hxp
  apply Gamma.pathSupportRoof (Sum.inl q : Gamma.DPath) (C.ladder.frontier beta)
  · apply C.legal.frontierChronology hab
    apply hA
    have hfInitial : f.start ∈ H.initialSet W :=
      ⟨Sum.inl f, hpW, rfl⟩
    rwa [hW.initialSet_eq] at hfInitial
  · intro t ht
    change some f.finish = some t at ht
    have hfinish : f.finish ∈ H.terminalFrontier W :=
      ⟨Sum.inl f, hpW, rfl⟩
    exact Option.some.inj ht ▸ hW.terminalFrontier_subset hfinish
  · intro y hy
    have hyf : y ∈ f.support := by
      have hyq := hy.1
      change y ∈ q.support at hyq
      simpa only [q, SliceSegmentCore.liftStageFinitePath_support] using hyq
    have hterminal := htight (Sum.inl f : H.DPath) hpW y hyf hy.2
    change some f.finish = some y at hterminal
    exact Set.mem_singleton_iff.2 (Option.some.inj hterminal).symm
  · exact hxq

/-- Alternating components rooted and generated inside one set remain in
that set. -/
private theorem exceptionalComponentVertices_subset
    {G : DWeb V} {W O : Set G.DPath} {E R : Set V}
    (hE : E ⊆ R) (hW : G.vertexSet W ⊆ R)
    (hO : G.vertexSet O ⊆ R) :
    exceptionalComponentVertices G W O E ⊆ R := by
  intro x hx
  simp only [exceptionalComponentVertices, Set.mem_iUnion] at hx
  obtain ⟨root, hrootE, hreach⟩ := hx
  change Relation.ReflTransGen
    (AlternatingComponents.EdgeRel W O) root x at hreach
  induction hreach with
  | refl => exact hE hrootE
  | @tail a b _hab hab ih =>
      rcases AlternatingComponents.edgeRel_implies_sameWarpPath hab with
        hsame | hsame
      · obtain ⟨p, hpW, _ha, hb⟩ := hsame
        exact hW ⟨p, hpW, hb⟩
      · obtain ⟨p, hpO, _ha, hb⟩ := hsame
        exact hO ⟨p, hpO, hb⟩

/-- Initial vertices of canonical old-to-new ladder intervals which touch
the selected deletion-safe path.  This is the additional bounded root set
which must be kept in the exchanged components when the safe target suffix
is retained. -/
def stageContactInitials
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {alpha beta : Stage (succ kappa)} (hab : alpha < beta) {z : V}
    (S : SafeStageTargetPath C alpha z) : Set V :=
  let H := C.ladder.stageWeb alpha
  H.initialSet (H.pathsMeetingFamily (C.ordinaryStageFamily hab.le) S.stageFamily)

/-- The source-faithful front-plus-tail output of Assertion 9.31.  The
interval family links the complete old frontier to the new frontier and
literally contains the selected safe prefix.  `path = front * tail` is the
same deletion-safe path all the way to the ambient target. -/
structure StageIntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (alpha beta : Stage (succ kappa)) (hab : alpha < beta) (z : V) where
  safe : SafeStageTargetPath C alpha z
  source_mem : z ∈ (C.ladder.frontier alpha)
  stageInterval : Set (C.ladder.stageWeb alpha).DPath
  stageInterval_linkage : IsLinkageBetween
    (C.ladder.stageWeb alpha) (C.ladder.frontier alpha) (C.ladder.frontier beta) stageInterval
  /-- The component exchange changes only this `kappa`-small union of
  alternating components.  Outside it, `stageInterval` retains the literal
  canonical ladder intervals. -/
  exceptionalComponents : Set V
  exceptionalComponents_card : #exceptionalComponents ≤ kappa
  exceptionalComponents_subset_outerRoof :
    exceptionalComponents ⊆ (Gamma.roof (C.ladder.frontier beta))
  excludedInitials_subset_exceptional :
    ((C.stageExceptional alpha beta) ∪ {z}) ∪
      stageContactInitials C hab safe ⊆ exceptionalComponents
  scheduled_mem_exceptional : z ∈ exceptionalComponents
  ordinaryRetained : Set (C.ladder.stageWeb alpha).DPath
  ordinaryRetained_eq : ordinaryRetained =
    CardinalInduction.SliceCandidate.initialPart
      (C.ladder.stageWeb alpha)
      (SliceSpliceSource.initialRestriction
        (C.ladder.stageWeb alpha) (C.ordinaryStageFamily hab.le)
        ((C.ladder.frontier alpha) \ (((C.stageExceptional alpha beta) ∪ {z}) ∪
          stageContactInitials C hab safe)))
      exceptionalComponentsᶜ
  ordinaryRetained_subset : ordinaryRetained ⊆ stageInterval
  ambientInterval : Set Gamma.DPath
  ambientInterval_eq_lift : ambientInterval =
    SliceSegmentCore.liftStageFamily C.ladder alpha stageInterval
  ambientInterval_linkage : IsLinkageBetween Gamma
    (C.ladder.frontier alpha) (C.ladder.frontier beta) ambientInterval
  ambientInterval_meetsOnlyAtTerminal :
    SliceSpliceSource.MeetsOnlyAtTerminal Gamma ambientInterval (C.ladder.frontier beta)
  ambientInterval_in_outerRoof : ∀ p ∈ ambientInterval,
    p.support ⊆ (Gamma.roof (C.ladder.frontier beta))
  path : FinitePath Gamma.graph
  path_mem_safe : (Sum.inl path : Gamma.DPath) ∈ safe.ambientFamily
  path_start : path.start = z
  path_finish : path.finish ∈ Gamma.target
  front : FinitePath Gamma.graph
  front_mem_interval : (Sum.inl front : Gamma.DPath) ∈ ambientInterval
  front_support_subset_exceptional :
    front.support ⊆ exceptionalComponents
  front_start : front.start = z
  front_finish_mem : front.finish ∈ (C.ladder.frontier beta)
  front_slice_pure : front.support ∩ (C.ladder.frontier beta) = {front.finish}
  front_isPrefix : front.IsPrefixOf path
  tail : FinitePath Gamma.graph
  tail_start : tail.start = front.finish
  front_tail_inter : front.support ∩ tail.support = {front.finish}
  interval_tail_inter : Gamma.vertexSet ambientInterval ∩ tail.support =
    {front.finish}
  splice_eq : front.appendFinite tail tail_start
      front_tail_inter.subset = path

/-- Construction provenance for the canonical interval reference.  A
deferred survivor interval omitted by the exchanged row is either rooted in
the explicit bounded exceptional/contact set, or is wholly contained in the
alternating exceptional component installed by the transaction. -/
structure ReferenceMissingCertificate
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {alpha beta : Stage (succ kappa)} {hab : alpha < beta} {z : V}
    (T : StageIntervalTransaction C alpha beta hab z) : Prop where
  missing : ∀ p ∈ (C.ordinaryStageFamily hab.le),
    C.ladder.liftStagePath alpha p ∉ T.ambientInterval →
      p.initial ∈
          (((C.stageExceptional alpha beta) ∪ {z}) ∪
            stageContactInitials C hab T.safe) ∨
        p.support ⊆ T.exceptionalComponents

namespace StageIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {alpha beta : Stage (succ kappa)} {hab : alpha < beta} {z : V}

theorem ambientInterval_vertexSet_inter_oldRoof
    (T : StageIntervalTransaction C alpha beta hab z) :
    Gamma.vertexSet T.ambientInterval ∩ Gamma.roof (C.ladder.frontier alpha) =
      C.ladder.frontier alpha := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨q, hq, hxq⟩, hxRoof⟩
    rw [T.ambientInterval_eq_lift] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have hxeq : x = r.initial := by
      by_contra hxne
      have hxRawRoof : x ∈ Gamma.roof
          (Gamma.terminalFrontier (C.ladder.warpAt alpha)) := by
        rw [← Gamma.roof_essential,
          ← C.ladder.frontier_eq_essential_terminalFrontier
            C.legal.roofsSourceAtStages alpha]
        exact hxRoof
      exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial alpha r hxq hxne) hxRawRoof
    rw [hxeq, ← T.stageInterval_linkage.initialSet_eq]
    exact ⟨r, hr, rfl⟩
  · intro x hx
    have hxInitial : x ∈ (C.ladder.stageWeb alpha).initialSet T.stageInterval :=
      T.stageInterval_linkage.initialSet_eq.symm ▸ hx
    obtain ⟨p, hp, hpInitial⟩ := hxInitial
    refine ⟨?_, Gamma.subset_roof (C.ladder.frontier alpha) hx⟩
    refine ⟨C.ladder.liftStagePath alpha p, ?_, ?_⟩
    · rw [T.ambientInterval_eq_lift, SliceSegmentCore.mem_liftStageFamily]
      exact ⟨p, hp, rfl⟩
    · rw [C.ladder.support_liftStagePath, ← hpInitial]
      exact p.initial_mem_support

theorem front_support_subset_outerRoof
    (T : StageIntervalTransaction C alpha beta hab z) :
    T.front.support ⊆ (Gamma.roof (C.ladder.frontier beta)) := by
  apply Gamma.pathSupportRoof (.inl T.front : Gamma.DPath) (C.ladder.frontier beta)
  · apply C.legal.frontierChronology hab
    change T.front.start ∈ (C.ladder.frontier alpha)
    rw [T.front_start]
    exact T.source_mem
  · intro t ht
    change some T.front.finish = some t at ht
    exact Option.some.inj ht ▸ T.front_finish_mem
  · intro x hx
    apply Set.mem_singleton_iff.2
    exact Set.mem_singleton_iff.1 (T.front_slice_pure ▸ hx)

theorem tail_boundary (T : StageIntervalTransaction C alpha beta hab z) :
    T.tail.start ∈ (C.ladder.frontier beta) ∧ T.tail.finish ∈ Gamma.target := by
  refine ⟨T.tail_start.symm ▸ T.front_finish_mem, ?_⟩
  have hfinish : T.tail.finish = T.path.finish := by
    calc
      T.tail.finish =
          (T.front.appendFinite T.tail T.tail_start
            T.front_tail_inter.subset).finish :=
        (T.front.appendFinite_finish T.tail T.tail_start
          T.front_tail_inter.subset).symm
      _ = T.path.finish := congrArg FinitePath.finish T.splice_eq
  exact hfinish.symm ▸ T.path_finish

theorem front_support_subset_path
    (T : StageIntervalTransaction C alpha beta hab z) :
    T.front.support ⊆ T.path.support :=
  T.front_isPrefix.support_subset

theorem tail_support_subset_path
    (T : StageIntervalTransaction C alpha beta hab z) :
    T.tail.support ⊆ T.path.support := by
  rw [← T.splice_eq,
    T.front.support_appendFinite_eq_union T.tail T.tail_start
      T.front_tail_inter.subset]
  exact Set.subset_union_right

/-- Away from the splice vertex, the retained ambient suffix is disjoint
from the complete old-to-new interval row. -/
theorem interval_tail_disjoint_off_start
    (T : StageIntervalTransaction C alpha beta hab z) :
    Disjoint (Gamma.vertexSet T.ambientInterval \ {T.tail.start})
      (T.tail.support \ {T.tail.start}) := by
  rw [T.tail_start]
  apply Set.disjoint_left.2
  rintro x ⟨hxInterval, hxne⟩ ⟨hxTail, _⟩
  have hx := Set.mem_inter hxInterval hxTail
  rw [T.interval_tail_inter] at hx
  exact hxne hx

end StageIntervalTransaction

theorem exists_stageIntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {alpha beta : Stage (succ kappa)} (hab : alpha < beta) (hbeta : beta ∈ C.club)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa)
    {z : V} (S : SafeStageTargetPath C alpha z)
    (hz : z ∈ (C.ladder.frontier alpha)) :
    Nonempty {T : StageIntervalTransaction C alpha beta hab z //
      T.safe = S ∧ ReferenceMissingCertificate T} := by
  let H := C.ladder.stageWeb alpha
  let X := H.vertexSet S.stageFamily
  let R := H.delete X
  let I := R.retarget ((C.ladder.frontier beta) \ X)
  obtain ⟨Wres, hWres⟩ :=
    C.isLinkable_retargetedStageResidual hext hab hbeta S
  have hWresR : IsLinkageBetween R R.source ((C.ladder.frontier beta) \ X) Wres := by
    change IsLinkageBetween R R.source ((C.ladder.frontier beta) \ X) Wres at hWres
    exact hWres
  let L : Set H.DPath := H.liftDeleteFamily X Wres
  have hLsmall : IsLinkageBetween H R.source ((C.ladder.frontier beta) \ X) L :=
    CardinalInduction.RegularProtectedDeltaLift.IsLinkageBetween.liftDeleteFamily
      H X hWresR
  have hLX : Disjoint (H.vertexSet L) X := by
    exact H.vertexSet_liftDeleteFamily_disjoint
      (hWresR.initialSet_eq.symm ▸
        (Set.Subset.rfl : R.source ⊆ R.source))
  have hL : IsLinkageBetween H R.source (C.ladder.frontier beta) L :=
    RegularProtectedAmbientRebuild.IsLinkageBetween.mono_target_sdiff hLsmall hLX
  have holdRoof : (C.ladder.frontier alpha) ⊆ H.roof (C.ladder.frontier beta) := by
    intro v hv p hp
    let qG := SliceSegmentCore.liftStageFinitePath
      C.ladder alpha p
    have hqG : Gamma.IsTargetPathFrom v qG := by
      have hp' := hp
      change p.start = v ∧ p.finish ∈ Gamma.target at hp'
      exact ⟨by simpa only [qG,
        SliceSegmentCore.liftStageFinitePath_start] using hp'.1,
        by simpa only [qG,
          SliceSegmentCore.liftStageFinitePath_finish] using hp'.2⟩
    obtain ⟨t, htqG, htT⟩ :=
      (C.legal.frontierChronology hab hv) qG hqG
    exact ⟨t, by simpa only [qG,
      SliceSegmentCore.liftStageFinitePath_support] using htqG, htT⟩
  have hRroof : R.source ⊆ H.roof (C.ladder.frontier beta) := by
    intro v hv
    exact holdRoof hv.1
  let hsepL : RelationalRoof.Separates H.graph.Adj
      R.source (C.ladder.frontier beta) (C.ladder.frontier beta) := by
    intro _ t p _ ht
    exact ⟨t, p.end_mem_support, ht⟩
  let Lstop : Set H.DPath := firstHitPrefixFamily hL hsepL
  have hLstop : IsLinkageBetween H R.source (C.ladder.frontier beta) Lstop :=
    firstHitPrefixFamily_isLinkageBetween hL hsepL
  have hLstopL : H.vertexSet Lstop ⊆ H.vertexSet L := by
    rintro x ⟨q, ⟨a, rfl⟩, hxq⟩
    refine ⟨(linkageMemberAt hL a).1, (linkageMemberAt hL a).2, ?_⟩
    rw [linkageMemberAt_eq_finite hL a]
    exact linkageFirstHitAt_support_subset hL hsepL a hxq
  have hLstopX : Disjoint (H.vertexSet Lstop) X :=
    hLX.mono_left hLstopL
  have hzRoof : z ∈ H.roof (C.ladder.frontier beta) := holdRoof hz
  have hzRoofSet : ({z} : Set V) ⊆ H.roof (C.ladder.frontier beta) := by
    simpa only [Set.singleton_subset_iff]
  let hsep : RelationalRoof.Separates H.graph.Adj
      ({z} : Set V) H.target (C.ladder.frontier beta) :=
    separates_target_of_subset_roof hzRoofSet
  let Pfront : Set H.DPath := firstHitPrefixFamily S.stage_linkage hsep
  have hPfront : IsLinkageBetween H ({z} : Set V) (C.ladder.frontier beta) Pfront :=
    firstHitPrefixFamily_isLinkageBetween S.stage_linkage hsep
  have hPfrontX : H.vertexSet Pfront ⊆ X := by
    rintro x ⟨q, ⟨a, rfl⟩, hxq⟩
    refine ⟨(linkageMemberAt S.stage_linkage a).1,
      (linkageMemberAt S.stage_linkage a).2, ?_⟩
    rw [linkageMemberAt_eq_finite S.stage_linkage a]
    exact linkageFirstHitAt_support_subset S.stage_linkage hsep a hxq
  have hdisjoint : Disjoint (H.vertexSet Pfront) (H.vertexSet Lstop) := by
    exact (hLstopX.mono_right hPfrontX).symm
  have hUnion : IsLinkageBetween H (({z} : Set V) ∪ R.source)
      (C.ladder.frontier beta) (Pfront ∪ Lstop) :=
    SingularRetargetedRow.linkageBetween_union_of_vertexSet_disjoint
      H hPfront hLstop hdisjoint
  have hHNorm : H.IsNormalized := by
    intro x y hxy
    let Q := Gamma.quotient
      (Gamma.terminalFrontier (C.ladder.warpAt alpha))
    have hxyQ : Q.graph.Adj x y := Q.essentialPart_adj_imp hxy
    have hxyGamma : Gamma.graph.Adj x y := Gamma.quotient_adj_imp hxyQ
    refine ⟨?_, (C.normalized hxyGamma).2⟩
    have hNoEnterQ : Q.NoEdgeEnters Q.source :=
      DWeb.NoEdgeEnters.quotient (G := Gamma)
        (fun {_ _} e hy ↦ (C.normalized e).1 hy)
    exact fun hy ↦ hNoEnterQ hxyQ hy.1
  have hXsource : X ∩ H.source = ({z} : Set V) := by
    have hzH : z ∈ H.source := by
      change z ∈ (C.ladder.frontier alpha)
      exact hz
    exact IsLinkageBetween.vertexSet_inter_source_eq hHNorm
      S.stage_linkage (by simpa only [Set.singleton_subset_iff] using hzH)
  have hsources : ({z} : Set V) ∪ R.source = (C.ladder.frontier alpha) := by
    change ({z} : Set V) ∪ (H.source \ X) = H.source
    ext x
    constructor
    · rintro (hxz | hxR)
      · have hzH : z ∈ H.source := by
          change z ∈ (C.ladder.frontier alpha)
          exact hz
        exact hxz ▸ hzH
      · exact hxR.1
    · intro hxH
      by_cases hxX : x ∈ X
      · have hx : x ∈ X ∩ H.source := ⟨hxX, hxH⟩
        rw [hXsource] at hx
        exact Or.inl hx
      · exact Or.inr ⟨hxH, hxX⟩
  have hBaseInterval : IsLinkageBetween H (C.ladder.frontier alpha) (C.ladder.frontier beta)
      (Pfront ∪ Lstop) := by
    rwa [hsources] at hUnion
  have hPfrontTight : SliceSpliceSource.MeetsOnlyAtTerminal
      H Pfront (C.ladder.frontier beta) :=
    firstHitPrefixFamily_meetsOnlyAtTerminal S.stage_linkage hsep
  have hLstopTight : SliceSpliceSource.MeetsOnlyAtTerminal
      H Lstop (C.ladder.frontier beta) :=
    firstHitPrefixFamily_meetsOnlyAtTerminal hL hsepL
  have hBaseTight : SliceSpliceSource.MeetsOnlyAtTerminal
      H (Pfront ∪ Lstop) (C.ladder.frontier beta) := by
    intro p hp
    exact hp.elim (hPfrontTight p) (hLstopTight p)
  /- Retain the arbitrary completed interval only in the alternating
  components rooted at an inessential source, the scheduled source, or an
  ordinary interval which touches the full deletion-safe path.  The last
  class is essential: it makes every restored ordinary interval disjoint
  from the ambient target suffix. -/
  let M : Set H.DPath :=
    H.pathsMeetingFamily (C.ordinaryStageFamily hab.le) S.stageFamily
  let contact : Set V := H.initialSet M
  have hMcard : #M ≤ kappa := by
    apply H.mk_pathsMeetingFamily_le (C.ordinaryStageFamily hab.le) S.stageFamily
    · exact (C.ordinaryStageFamily_isLinkageBetween hab.le).isWarp
    · exact C.capacity_infinite
    · exact (mk_linkage_le_initial H S.stage_linkage).trans (by
        rw [Cardinal.mk_singleton]
        exact Cardinal.one_le_aleph0.trans C.capacity_infinite)
    · intro p _hp
      exact p.support_countable.le_aleph0.trans C.capacity_infinite
  have hcontactCard : #contact ≤ kappa :=
    (RegularProtectedAmbientRebuild.mk_initialSet_le_family H M).trans hMcard
  have hcontactSub : contact ⊆ (C.ladder.frontier alpha) := by
    rintro x ⟨p, hpM, rfl⟩
    have hpInitial : p.initial ∈ H.initialSet (C.ordinaryStageFamily hab.le) :=
      ⟨p, hpM.1, rfl⟩
    rw [(C.ordinaryStageFamily_isLinkageBetween hab.le).initialSet_eq] at hpInitial
    exact hpInitial.1
  let Ebase : Set V := (C.stageExceptional alpha beta) ∪ {z}
  let E : Set V := Ebase ∪ contact
  have hEsub : E ⊆ (C.ladder.frontier alpha) := by
    rintro x ((hx | rfl) | hxContact)
    · exact hx.1
    · exact hz
    · exact hcontactSub hxContact
  have hEcard : #E ≤ kappa := by
    have hbase : #Ebase ≤ kappa := by
      refine (Cardinal.mk_union_le (C.stageExceptional alpha beta) ({z} : Set V)).trans ?_
      apply Cardinal.add_le_of_le C.capacity_infinite
      · exact (C.mk_stageExceptional_le hab.le hbeta)
      · rw [Cardinal.mk_singleton]
        exact Cardinal.one_le_aleph0.trans C.capacity_infinite
    refine (Cardinal.mk_union_le Ebase contact).trans ?_
    exact Cardinal.add_le_of_le C.capacity_infinite hbase hcontactCard
  let O : Set H.DPath := SliceSpliceSource.initialRestriction H
    (C.ordinaryStageFamily hab.le) ((C.ladder.frontier alpha) \ E)
  have hO : IsLinkageBetween H ((C.ladder.frontier alpha) \ E) (C.ladder.frontier beta) O := by
    apply SliceSpliceSource.isLinkageBetween_initialRestriction
      (C.ordinaryStageFamily_isLinkageBetween hab.le)
    intro x hx
    exact ⟨hx.1, fun hxExceptional ↦
      hx.2 (Or.inl (Or.inl hxExceptional))⟩
  have hOX : Disjoint (H.vertexSet O) X := by
    apply Set.disjoint_left.2
    rintro x ⟨p, hpO, hxp⟩ hxX
    have hpM : p ∈ M := by
      refine ⟨hpO.1, ?_⟩
      obtain ⟨q, hqS, hxq⟩ := hxX
      exact ⟨q, hqS, Set.not_disjoint_iff.mpr ⟨x, hxp, hxq⟩⟩
    have hpContact : p.initial ∈ contact := ⟨p, hpM, rfl⟩
    exact hpO.2.2 (Or.inr hpContact)
  have hOTight : SliceSpliceSource.MeetsOnlyAtTerminal
      H O (C.ladder.frontier beta) := by
    intro p hp
    exact (C.ordinaryStageFamily_meetsOnlyAtTerminal hab.le) p hp.1
  have hBaseRoof : H.vertexSet (Pfront ∪ Lstop) ⊆ (Gamma.roof (C.ladder.frontier beta)) :=
    stageLinkage_vertexSet_subset_outerRoof C hab
      (Set.Subset.rfl) hBaseInterval hBaseTight
  have hORoof : H.vertexSet O ⊆ (Gamma.roof (C.ladder.frontier beta)) :=
    stageLinkage_vertexSet_subset_outerRoof C hab
      Set.sdiff_subset hO hOTight
  have hERoof : E ⊆ (Gamma.roof (C.ladder.frontier beta)) :=
    hEsub.trans (C.legal.frontierChronology hab)
  let D : Set V := exceptionalComponentVertices H (Pfront ∪ Lstop) O E
  have hDRoof : D ⊆ (Gamma.roof (C.ladder.frontier beta)) :=
    exceptionalComponentVertices_subset hERoof hBaseRoof hORoof
  have hDcard : #D ≤ kappa := by
    apply lt_succ_iff.mp
    apply mk_exceptionalComponentVertices_lt
      (Cardinal.isRegular_succ C.capacity_infinite)
      (C.capacity_infinite.trans_lt (lt_succ kappa))
      hBaseInterval.isWarp hO.isWarp
      hBaseInterval.finiteCharacter hO.finiteCharacter
    exact (lt_succ_iff.mpr hEcard)
  let I : Set H.DPath := componentMixedFamily H (Pfront ∪ Lstop) O E
  have hIRoof : H.vertexSet I ⊆ (Gamma.roof (C.ladder.frontier beta)) := by
    rintro x ⟨p, hpI, hxp⟩
    rcases hpI with hpBase | hpOrdinary
    · exact hBaseRoof ⟨p, hpBase.1, hxp⟩
    · exact hORoof ⟨p, hpOrdinary.1, hxp⟩
  have hInterval : IsLinkageBetween H (C.ladder.frontier alpha) (C.ladder.frontier beta) I := by
    exact componentMixedFamily_isLinkageBetween_of_complement H
      hBaseInterval hO hEsub
  have hIntervalTight : SliceSpliceSource.MeetsOnlyAtTerminal
      H I (C.ladder.frontier beta) := by
    intro p hp
    rcases hp with hpBase | hpOrdinary
    · exact hBaseTight p hpBase.1
    · exact hOTight p hpOrdinary.1
  have hzD : z ∈ D :=
    mem_exceptionalComponentVertices_of_mem H (Pfront ∪ Lstop) O
      (Or.inl (Or.inr (Set.mem_singleton z)))
  let ORetained : Set H.DPath := initialPart H O Dᶜ
  have hORetained : ORetained ⊆ I := by
    intro p hp
    exact Or.inr hp
  let W : Set Gamma.DPath :=
    SliceSegmentCore.liftStageFamily C.ladder alpha I
  have hW : IsLinkageBetween Gamma (C.ladder.frontier alpha) (C.ladder.frontier beta) W :=
    CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily hInterval
  let a : ({z} : Set V) := ⟨z, Set.mem_singleton z⟩
  let pathH : FinitePath H.graph := linkageFiniteAt S.stage_linkage a
  have hpathH : (Sum.inl pathH : H.DPath) ∈ S.stageFamily := by
    rw [← linkageMemberAt_eq_finite S.stage_linkage a]
    exact (linkageMemberAt S.stage_linkage a).2
  let frontH : FinitePath H.graph := linkageFirstHitAt S.stage_linkage hsep a
  have hfrontH : (Sum.inl frontH : H.DPath) ∈ Pfront := ⟨a, rfl⟩
  let path : FinitePath Gamma.graph :=
    SliceSegmentCore.liftStageFinitePath C.ladder alpha pathH
  let front : FinitePath Gamma.graph :=
    SliceSegmentCore.liftStageFinitePath C.ladder alpha frontH
  have hpathSafe : (Sum.inl path : Gamma.DPath) ∈ S.ambientFamily := by
    rw [S.ambient_eq_lift]
    exact ⟨Sum.inl pathH, hpathH, by
      simp only [SliceSegmentCore.liftStagePath_finite, path]⟩
  have hfrontW : (Sum.inl front : Gamma.DPath) ∈ W := by
    have hfrontI : (Sum.inl frontH : H.DPath) ∈ I := by
      apply Or.inl
      exact ⟨Or.inl hfrontH, by
        change frontH.start ∈ D
        simpa only [frontH, linkageFirstHitAt_start, a] using hzD⟩
    refine ⟨Sum.inl frontH, hfrontI, ?_⟩
    simp only [SliceSegmentCore.liftStagePath_finite, front]
  have hfrontPrefixH : frontH.IsPrefixOf pathH :=
    (linkageFiniteAt S.stage_linkage a).walk.firstHit (C.ladder.frontier beta)
      (linkageFiniteAt_meets S.stage_linkage hsep a) |>.support_prefix
  have hfrontPrefix : front.IsPrefixOf path := by
    change front.walk.support <+: path.walk.support
    change frontH.walk.support <+: pathH.walk.support at hfrontPrefixH
    simpa only [front, path,
      SliceSegmentCore.liftStageFinitePath_walk_support] using hfrontPrefixH
  have hfrontD : front.support ⊆ D := by
    have hstartD : frontH.start ∈ D := by
      simpa only [frontH, linkageFirstHitAt_start, a] using hzD
    have hsupportD : frontH.support ⊆ D :=
      path_support_subset_exceptionalComponents_left
        hBaseInterval.finiteCharacter (Or.inl hfrontH)
        frontH.start_mem_support hstartD
    intro x hx
    apply hsupportD
    simpa only [front,
      SliceSegmentCore.liftStageFinitePath_support] using hx
  let hfinish : front.finish ∈ path.support :=
    hfrontPrefix.support_subset front.finish_mem_support
  let tail : FinitePath Gamma.graph := path.suffixFromAux front.finish hfinish
  obtain ⟨htailStart, _hinter, hinterEq, hsplice⟩ :=
    appendFinite_suffixFromAux_eq_of_prefix hfrontPrefix
  have hintervalTail : Gamma.vertexSet W ∩ tail.support =
      {front.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨q, hqW, hxq⟩, hxTail⟩
      obtain ⟨qH, hqH, rfl⟩ := hqW
      have hxqH : x ∈ qH.support := by
        simpa only [C.ladder.support_liftStagePath alpha qH] using hxq
      have hxPath : x ∈ path.support :=
        path.suffixFromAux_support_subset front.finish hfinish hxTail
      have hxPathH : x ∈ pathH.support := by
        simpa only [path,
          SliceSegmentCore.liftStageFinitePath_support] using hxPath
      have hxX : x ∈ X :=
        ⟨(Sum.inl pathH : H.DPath), hpathH, hxPathH⟩
      rcases hqH with ⟨hqBase, _hqD⟩ | ⟨hqOrdinary, _hqDc⟩
      · rcases hqBase with hqFront | hqResidual
        · obtain ⟨b, hqEq⟩ := hqFront
          have hba : b = a := Subtype.ext (Set.mem_singleton_iff.1 b.2)
          subst b
          have hqEq' : qH = Sum.inl frontH := hqEq.symm
          subst qH
          have hxFront : x ∈ front.support := by
            change x ∈ frontH.support at hxqH
            simpa only [front,
              SliceSegmentCore.liftStageFinitePath_support] using hxqH
          have hx := Set.mem_inter hxFront hxTail
          rw [hinterEq] at hx
          exact hx
        · exact False.elim (Set.disjoint_left.1 hLstopX
            ⟨qH, hqResidual, hxqH⟩ hxX)
      · exact False.elim (Set.disjoint_left.1 hOX
          ⟨qH, hqOrdinary, hxqH⟩ hxX)
    · intro x hx
      have hxeq : x = front.finish := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨⟨Sum.inl front, hfrontW, front.finish_mem_support⟩, ?_⟩
      rw [← htailStart]
      exact tail.start_mem_support
  let Tout : StageIntervalTransaction C alpha beta hab z := {
    safe := S
    source_mem := hz
    stageInterval := I
    stageInterval_linkage := hInterval
    exceptionalComponents := D
    exceptionalComponents_card := hDcard
    exceptionalComponents_subset_outerRoof := hDRoof
    excludedInitials_subset_exceptional := by
      intro x hx
      exact mem_exceptionalComponentVertices_of_mem H (Pfront ∪ Lstop) O hx
    scheduled_mem_exceptional := hzD
    ordinaryRetained := ORetained
    ordinaryRetained_eq := rfl
    ordinaryRetained_subset := hORetained
    ambientInterval := W
    ambientInterval_eq_lift := rfl
    ambientInterval_linkage := hW
    ambientInterval_meetsOnlyAtTerminal :=
      CardinalInduction.SliceDeltaLift.meetsOnlyAtTerminal_liftStageFamily
        hIntervalTight
    ambientInterval_in_outerRoof := by
      rintro p ⟨q, hqI, rfl⟩ x hxp
      apply hIRoof ⟨q, hqI, ?_⟩
      simpa only [C.ladder.support_liftStagePath alpha q] using hxp
    path := path
    path_mem_safe := hpathSafe
    path_start := by
      simpa only [path, SliceSegmentCore.liftStageFinitePath_start,
        pathH, a] using linkageFiniteAt_start S.stage_linkage a
    path_finish := by
      have hfinish := linkageFiniteAt_finish_mem S.stage_linkage a
      change pathH.finish ∈ Gamma.target at hfinish
      simpa only [path, SliceSegmentCore.liftStageFinitePath_finish,
        pathH] using hfinish
    front := front
    front_mem_interval := hfrontW
    front_support_subset_exceptional := hfrontD
    front_start := by
      simpa only [front, SliceSegmentCore.liftStageFinitePath_start,
        frontH, a] using linkageFirstHitAt_start S.stage_linkage hsep a
    front_finish_mem := by
      simpa only [front, SliceSegmentCore.liftStageFinitePath_finish,
        frontH] using linkageFirstHitAt_finish_mem S.stage_linkage hsep a
    front_slice_pure := by
      simpa only [front, SliceSegmentCore.liftStageFinitePath_support,
        SliceSegmentCore.liftStageFinitePath_finish, frontH] using
        linkageFirstHitAt_targetPure S.stage_linkage hsep a
    front_isPrefix := hfrontPrefix
    tail := tail
    tail_start := htailStart
    front_tail_inter := hinterEq
    interval_tail_inter := hintervalTail
    splice_eq := hsplice }
  have hmissing : ReferenceMissingCertificate Tout := by
    constructor
    intro p hpF₀ hpNotInterval
    by_cases hpE : p.initial ∈ E
    · exact Or.inl (by
        simpa only [Tout, E, Ebase, contact, M,
          stageContactInitials] using hpE)
    · right
      have hpInitial : p.initial ∈ (C.ladder.frontier alpha) := by
        have hpInitialSet : p.initial ∈
            H.initialSet (C.ordinaryStageFamily hab.le) :=
          ⟨p, hpF₀, rfl⟩
        rw [(C.ordinaryStageFamily_isLinkageBetween hab.le).initialSet_eq]
          at hpInitialSet
        exact hpInitialSet.1
      have hpO : p ∈ O := by
        exact ⟨hpF₀, hpInitial, hpE⟩
      have hpD : p.initial ∈ D := by
        by_contra hpNotD
        have hpRetained : p ∈ ORetained := by
          exact ⟨hpO, hpNotD⟩
        apply hpNotInterval
        rw [Tout.ambientInterval_eq_lift]
        exact ⟨p, hORetained hpRetained, rfl⟩
      have hOfinite : H.HasFiniteCharacter O := by
        intro q hq
        exact (C.ordinaryStageFamily_isLinkageBetween hab.le).finiteCharacter
          hq.1
      have hpSupport : p.support ⊆ D :=
        path_support_subset_exceptionalComponents_right hOfinite hpO
          p.initial_mem_support hpD
      simpa only [Tout] using hpSupport
  exact ⟨⟨Tout, rfl, hmissing⟩⟩


#print axioms exists_stageIntervalTransaction
#print axioms StageIntervalTransaction.interval_tail_disjoint_off_start
#print axioms StageIntervalTransaction.ambientInterval_vertexSet_inter_oldRoof

end Erdos599.Blueprint.LinkageBlueprint.ExplicitStageInterval
