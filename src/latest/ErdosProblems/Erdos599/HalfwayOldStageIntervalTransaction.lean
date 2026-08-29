/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayDeferredOldStageComplement
import ErdosProblems.Erdos599.HalfwayRetainedLaterLinkage
import ErdosProblems.Erdos599.HalfwayStageSafeTarget
import ErdosProblems.Erdos599.HalfwayStageAuxiliaryAmbient
import ErdosProblems.Erdos599.ProtectedCardinalAssembly
import ErdosProblems.Erdos599.SingularSafeBatch
import ErdosProblems.Erdos599.SliceSuffixFromAux

/-!
# The old-to-new interval transaction in Assertion 9.31

The old ladder frontier can be much larger than the current induction
cardinal.  Assertion 9.31 does not solve that whole source by a cardinality
bound.  It deletes the path supplied by Assertion 9.23 and applies the
current extension clause to the old-to-new interval.  The ordinary ladder
intervals link every source except

* the small inessential-extension set, and
* the initials of ordinary intervals meeting the selected finite path.

The latter family has cardinal at most the current cardinal because it is a
subfamily of a warp meeting a current-cardinal family of countable paths.
This file formalizes that exact argument.  The output retains the selected
old-to-new prefix literally, together with the suffix of the same safe path
to the ambient target.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.ControlledSlices
open _root_.Erdos599.CardinalInduction.SliceCandidate

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- Initial vertices are no more numerous than the paths of the family. -/
private theorem mk_initialSet_le_family
    (G : DWeb V) (W : Set G.DPath) :
    #(G.initialSet W) ≤ #W := by
  let choosePath : G.initialSet W → W := fun x ↦
    ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  apply Cardinal.mk_le_of_injective (f := choosePath)
  intro x y hxy
  apply Subtype.ext
  have hx := (Classical.choose_spec x.2).2
  have hy := (Classical.choose_spec y.2).2
  exact calc
    x.1 = (choosePath x).1.initial := hx.symm
    _ = (choosePath y).1.initial :=
      congrArg (fun p : W ↦ p.1.initial) hxy
    _ = y.1 := hy

/-- A linkage avoiding `X` can be retyped in the deleted web, with the
right endpoint set reduced by `X`. -/
private theorem IsLinkageBetween.restrictDeleteFamily
    (G : DWeb V) (X : Set V) {A B : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G A B W)
    (havoid : Disjoint (G.vertexSet W) X) :
    IsLinkageBetween (G.delete X) A (B \ X)
      (G.restrictDeleteFamily X W havoid) := by
  refine ⟨DWeb.IsWarp.restrictDeleteFamily G hW.isWarp havoid,
    G.fd_hasFiniteCharacter_restrictDeleteFamily hW.finiteCharacter havoid,
    ?_, ?_, ?_⟩
  · simpa only [G.initialSet_restrictDeleteFamily] using hW.initialSet_eq
  · rw [G.terminalFrontier_restrictDeleteFamily]
    rintro x hx
    refine ⟨hW.terminalFrontier_subset hx, ?_⟩
    obtain ⟨p, hpW, hpx⟩ := hx
    intro hxX
    exact Set.disjoint_left.1 havoid
      ⟨p, hpW, G.terminal_mem_support hpx⟩ hxX
  · rintro q ⟨p, _hp, rfl⟩
    obtain ⟨f, hpf, hends, hsource⟩ := hW.endpointPure p.1 p.2
    have hpfin : p.1 = (Sum.inl f : G.DPath) := hpf
    have hqmem : G.restrictDeleteMember X W havoid p ∈
        G.restrictDeleteFamily X W havoid :=
      ⟨p, Set.mem_univ p, rfl⟩
    obtain ⟨f', hf'⟩ :=
      G.fd_hasFiniteCharacter_restrictDeleteFamily
        hW.finiteCharacter havoid hqmem
    refine ⟨f', hf', ?_, ?_⟩
    · have hsupport : f'.support = f.support := by
        calc
          f'.support = (G.restrictDeleteMember X W havoid p).support :=
            (congrArg Path.support hf').symm
          _ = p.1.support := G.support_restrictDeleteMember X W havoid p
          _ = f.support := congrArg Path.support hpfin
      have hstart : f'.start = f.start := by
        have hi' := congrArg Path.initial hf'
        have hi := G.initial_restrictDeleteMember X W havoid p
        exact hi'.symm.trans (hi.trans (congrArg Path.initial hpfin))
      have hfinish : f'.finish = f.finish := by
        have ht := G.terminal?_restrictDeleteMember X W havoid p
        rw [hf'] at ht
        rw [hpfin] at ht
        exact Option.some.inj ht
      rw [hsupport, hstart, hfinish]
      calc
        f.support ∩ (A ∪ (B \ X)) = f.support ∩ (A ∪ B) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
          constructor
          · rintro ⟨hxf, hxA | ⟨hxB, _⟩⟩
            · exact ⟨hxf, Or.inl hxA⟩
            · exact ⟨hxf, Or.inr hxB⟩
          · rintro ⟨hxf, hxA | hxB⟩
            · exact ⟨hxf, Or.inl hxA⟩
            · refine ⟨hxf, Or.inr ⟨hxB, ?_⟩⟩
              intro hxX
              exact Set.disjoint_left.1 havoid ⟨p.1, p.2,
                hpfin ▸ hxf⟩ hxX
        _ = {f.start, f.finish} := hends
    · have hsupport : f'.support = f.support := by
        calc
          f'.support = (G.restrictDeleteMember X W havoid p).support :=
            (congrArg Path.support hf').symm
          _ = p.1.support := G.support_restrictDeleteMember X W havoid p
          _ = f.support := congrArg Path.support hpfin
      have hstart : f'.start = f.start := by
        have hi' := congrArg Path.initial hf'
        have hi := G.initial_restrictDeleteMember X W havoid p
        exact hi'.symm.trans (hi.trans (congrArg Path.initial hpfin))
      rw [hsupport, hstart]
      exact hsource

/-- Widening the right endpoint set preserves a linkage when the old right
set is contained in the new one. -/
private theorem IsLinkageBetween.mono_target_sdiff
    {G : DWeb V} {A B X : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G A (B \ X) W)
    (havoid : Disjoint (G.vertexSet W) X) :
    IsLinkageBetween G A B W := by
  refine ⟨hW.isWarp, hW.finiteCharacter, hW.initialSet_eq,
    hW.terminalFrontier_subset.trans Set.sdiff_subset, ?_⟩
  intro p hp
  obtain ⟨f, rfl, hends, hsource⟩ := hW.endpointPure p hp
  refine ⟨f, rfl, ?_, hsource⟩
  calc
    f.support ∩ (A ∪ B) = f.support ∩ (A ∪ (B \ X)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
      constructor
      · rintro ⟨hxf, hxA | hxB⟩
        · exact ⟨hxf, Or.inl hxA⟩
        · refine ⟨hxf, Or.inr ⟨hxB, ?_⟩⟩
          intro hxX
          exact Set.disjoint_left.1 havoid ⟨Sum.inl f, hp, hxf⟩ hxX
      · rintro ⟨hxf, hxA | ⟨hxB, _⟩⟩
        · exact ⟨hxf, Or.inl hxA⟩
        · exact ⟨hxf, Or.inr hxB⟩
    _ = {f.start, f.finish} := hends

/-- A bounded exceptional set plus a linkage on its complement is enough
to invoke the current extension clause.  If the whole source is smaller
than the current cardinal, the lower/current small-source lemma is used;
otherwise the exceptional set is padded inside the source. -/
private theorem isLinkable_of_bounded_exceptional_complement_extensionThrough
    (Base : DWeb V)
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Base kappa)
    (hkappa : aleph0 ≤ kappa)
    (G : DWeb V) (hG : G.IsUnhindered)
    (hGBase : ∀ {x y : V}, G.graph.Adj x y → Base.graph.Adj x y)
    {E : Set V} (hEsource : E ⊆ G.source) (hEcard : #E ≤ kappa)
    {F : Set G.DPath}
    (hF : IsLinkageBetween G (G.source \ E) G.target F) :
    IsLinkable G := by
  by_cases hlarge : kappa ≤ #G.source
  · obtain ⟨E', hEE', hE'source, hE'card⟩ :=
      CardinalInduction.SingularSafeBatch.exists_superset_mk_eq_of_mk_le
        hEsource hEcard hlarge hkappa
    apply hext kappa le_rfl G hGBase hG E' hE'source hE'card
    refine ⟨SliceSpliceSource.initialRestriction G F (G.source \ E'), ?_⟩
    apply SliceSpliceSource.isLinkageBetween_initialRestriction hF
    rintro x ⟨hxSource, hxE'⟩
    exact ⟨hxSource, fun hxE ↦ hxE' (hEE' hxE)⟩
  · exact _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor.linkable_of_source_mk_le
      hext hGBase hG (lt_of_not_ge hlarge).le

/-- The old-stage residual is still roofed by the new frontier after the
safe path carrier is deleted.  Every residual target path lifts to an
ambient target path; the ladder chronology forces a new-frontier contact,
and deletion says that contact is not in the removed carrier. -/
private theorem residual_source_subset_roof_newSlice
    (C : ClubStageGeometry Gamma Y kappa theta) {z : V}
    (S : SafeOldStageTargetPath C z) :
    let H := C.ladder.stageWeb C.oldStage
    let X := H.vertexSet S.stageFamily
    (H.delete X).source ⊆ (H.delete X).roof (C.newSlice \ X) := by
  dsimp only
  intro a ha p hp
  let qH : FinitePath (C.ladder.stageWeb C.oldStage).graph :=
    p.lift (C.ladder.stageWeb C.oldStage).delete_adj_imp
  let qG : FinitePath Gamma.graph :=
    SliceSegmentCore.liftStageFinitePath C.ladder C.oldStage qH
  have hqG : Gamma.IsTargetPathFrom a qG := by
    refine ⟨?_, ?_⟩
    · change qH.start = a
      exact hp.1
    · change qH.finish ∈ Gamma.target
      exact hp.2.1
  have haRoof : a ∈ C.outerRoof :=
    C.legal.frontierChronology C.old_lt_new ha.1
  obtain ⟨t, htqG, htT⟩ := haRoof qG hqG
  have htqH : t ∈ qH.support := by
    simpa only [qG, SliceSegmentCore.liftStageFinitePath_support] using htqG
  have htp : t ∈ p.support := by
    simpa only [qH, FinitePath.support_lift] using htqH
  have hpInitial : Path.initial (Sum.inl p :
      ((C.ladder.stageWeb C.oldStage).delete
        ((C.ladder.stageWeb C.oldStage).vertexSet S.stageFamily)).DPath)
      ∉ (C.ladder.stageWeb C.oldStage).vertexSet S.stageFamily := by
    change p.start ∉ (C.ladder.stageWeb C.oldStage).vertexSet S.stageFamily
    intro hpX
    apply ha.2
    rw [← hp.1]
    exact hpX
  have havoid := (C.ladder.stageWeb C.oldStage).liftDeletePath_avoids
    ((C.ladder.stageWeb C.oldStage).vertexSet S.stageFamily)
    (Sum.inl p) hpInitial
  refine ⟨t, htp, htT, ?_⟩
  intro htX
  rw [(C.ladder.stageWeb C.oldStage).support_liftDeletePath] at havoid
  apply Set.disjoint_left.1 havoid
  · exact htp
  · exact htX

/-- The exact positive replacement for the unsupported whole-old-frontier
cardinality argument.  The safely deleted old-to-new interval web is
linkable, although the old frontier itself may have arbitrary cardinality. -/
theorem ClubStageGeometry.isLinkable_retargetedResidualInterval_of_extensionThrough
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa)
    {z : V} (S : SafeOldStageTargetPath C z) :
    let H := C.ladder.stageWeb C.oldStage
    let X := H.vertexSet S.stageFamily
    IsLinkable ((H.delete X).retarget (C.newSlice \ X)) := by
  let H := C.ladder.stageWeb C.oldStage
  let X := H.vertexSet S.stageFamily
  let R := H.delete X
  let I := R.retarget (C.newSlice \ X)
  let E₀ := C.deferredOldStageExceptional
  let F₀ := C.deferredOldStageOrdinaryFamily
  let M := H.pathsMeetingFamily F₀ S.stageFamily
  let E : Set V := I.source ∩ (E₀ ∪ H.initialSet M)
  let A : Set V := I.source \ E
  let F : Set H.DPath := SliceSpliceSource.initialRestriction H F₀ A
  have hIunhindered : I.IsUnhindered := by
    rintro ⟨W, hW⟩
    apply S.deletion_safe
    refine ⟨W, ?_⟩
    exact DWeb.IsHindrance.of_retarget R hW
      (residual_source_subset_roof_newSlice C S)
  have hMcard : #M ≤ kappa := by
    apply H.mk_pathsMeetingFamily_le F₀ S.stageFamily
    · exact C.deferredOldStageOrdinaryFamily_isLinkageBetween.isWarp
    · exact C.capacity_infinite
    · exact (mk_linkage_le_initial H S.stage_linkage).trans (by
        rw [Cardinal.mk_singleton]
        exact Cardinal.one_le_aleph0.trans C.capacity_infinite)
    · intro p _hp
      exact p.support_countable.le_aleph0.trans C.capacity_infinite
  have hEcard : #E ≤ kappa := by
    refine (Cardinal.mk_subtype_mono Set.inter_subset_right).trans ?_
    refine (Cardinal.mk_union_le E₀ (H.initialSet M)).trans ?_
    apply Cardinal.add_le_of_le C.capacity_infinite
    · exact C.mk_deferredOldStageExceptional_le
    · exact (mk_initialSet_le_family H M).trans hMcard
  have hAsub : A ⊆ C.oldSlice \ E₀ := by
    rintro x ⟨hxI, hxE⟩
    refine ⟨hxI.1, ?_⟩
    intro hxE₀
    exact hxE ⟨hxI, Or.inl hxE₀⟩
  have hF : IsLinkageBetween H A C.newSlice F :=
    SliceSpliceSource.isLinkageBetween_initialRestriction
      C.deferredOldStageOrdinaryFamily_isLinkageBetween hAsub
  have hFavoid : Disjoint (H.vertexSet F) X := by
    apply Set.disjoint_left.2
    rintro x ⟨p, hpF, hxp⟩ hxX
    have hpM : p ∈ M := by
      refine ⟨hpF.1, ?_⟩
      obtain ⟨q, hqS, hxq⟩ := hxX
      refine ⟨q, hqS, ?_⟩
      rw [Set.not_disjoint_iff]
      exact ⟨x, hxp, hxq⟩
    have hpInitialM : p.initial ∈ H.initialSet M := ⟨p, hpM, rfl⟩
    exact hpF.2.2 ⟨hpF.2.1, Or.inr hpInitialM⟩
  have hFR : IsLinkageBetween R A (C.newSlice \ X)
      (H.restrictDeleteFamily X F hFavoid) :=
    IsLinkageBetween.restrictDeleteFamily H X hF hFavoid
  have hFI : IsLinkageBetween I (I.source \ E) I.target
      (H.restrictDeleteFamily X F hFavoid) := by
    refine ⟨hFR.isWarp, hFR.finiteCharacter, ?_,
      hFR.terminalFrontier_subset, ?_⟩
    · change R.initialSet (H.restrictDeleteFamily X F hFavoid) = A
      exact hFR.initialSet_eq
    intro p hp
    exact hFR.endpointPure p hp
  apply isLinkable_of_bounded_exceptional_complement_extensionThrough
    Gamma hext C.capacity_infinite I hIunhindered
      C.oldResidualInterval_adj_ambient
      (E := E) Set.inter_subset_left hEcard hFI

/-- Legacy universal-induction wrapper around the ambient-restricted
extension-only residual theorem. -/
theorem ClubStageGeometry.isLinkable_retargetedResidualInterval
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hext : UniversalExtensionClauseAt V kappa)
    {z : V} (S : SafeOldStageTargetPath C z) :
    let H := C.ladder.stageWeb C.oldStage
    let X := H.vertexSet S.stageFamily
    IsLinkable ((H.delete X).retarget (C.newSlice \ X)) := by
  have hthrough :
      _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
        Gamma kappa := by
    intro rho hrho H hHambient hH
    rcases hrho.lt_or_eq with hlt | rfl
    · exact (hlower rho hlt H hH).1
    · exact hext H hH
  exact C.isLinkable_retargetedResidualInterval_of_extensionThrough hthrough S

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
    {A : Set V} {W : Set (C.ladder.stageWeb C.oldStage).DPath}
    (hA : A ⊆ C.oldSlice)
    (hW : IsLinkageBetween (C.ladder.stageWeb C.oldStage)
      A C.newSlice W)
    (htight : SliceSpliceSource.MeetsOnlyAtTerminal
      (C.ladder.stageWeb C.oldStage) W C.newSlice) :
    (C.ladder.stageWeb C.oldStage).vertexSet W ⊆ C.outerRoof := by
  let H := C.ladder.stageWeb C.oldStage
  rintro x ⟨p, hpW, hxp⟩
  obtain ⟨f, rfl⟩ := hW.finiteCharacter hpW
  let q : FinitePath Gamma.graph :=
    SliceSegmentCore.liftStageFinitePath C.ladder C.oldStage f
  have hxq : x ∈ q.support := by
    change x ∈ f.support at hxp
    simpa only [q, SliceSegmentCore.liftStageFinitePath_support] using hxp
  apply Gamma.pathSupportRoof (Sum.inl q : Gamma.DPath) C.newSlice
  · apply C.legal.frontierChronology C.old_lt_new
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
def oldStageContactInitials
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) {z : V}
    (S : SafeOldStageTargetPath C z) : Set V :=
  let H := C.ladder.stageWeb C.oldStage
  H.initialSet (H.pathsMeetingFamily C.deferredOldStageOrdinaryFamily S.stageFamily)

/-- The source-faithful front-plus-tail output of Assertion 9.31.  The
interval family links the complete old frontier to the new frontier and
literally contains the selected safe prefix.  `path = front * tail` is the
same deletion-safe path all the way to the ambient target. -/
structure OldStageIntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (z : V) where
  safe : SafeOldStageTargetPath C z
  source_mem : z ∈ C.oldSlice
  stageInterval : Set (C.ladder.stageWeb C.oldStage).DPath
  stageInterval_linkage : IsLinkageBetween
    (C.ladder.stageWeb C.oldStage) C.oldSlice C.newSlice stageInterval
  /-- The component exchange changes only this `kappa`-small union of
  alternating components.  Outside it, `stageInterval` retains the literal
  canonical ladder intervals. -/
  exceptionalComponents : Set V
  exceptionalComponents_card : #exceptionalComponents ≤ kappa
  exceptionalComponents_subset_outerRoof :
    exceptionalComponents ⊆ C.outerRoof
  excludedInitials_subset_exceptional :
    (C.deferredOldStageExceptional ∪ {z}) ∪
      oldStageContactInitials C safe ⊆ exceptionalComponents
  scheduled_mem_exceptional : z ∈ exceptionalComponents
  ordinaryRetained : Set (C.ladder.stageWeb C.oldStage).DPath
  ordinaryRetained_eq : ordinaryRetained =
    CardinalInduction.SliceCandidate.initialPart
      (C.ladder.stageWeb C.oldStage)
      (SliceSpliceSource.initialRestriction
        (C.ladder.stageWeb C.oldStage) C.deferredOldStageOrdinaryFamily
        (C.oldSlice \ ((C.deferredOldStageExceptional ∪ {z}) ∪
          oldStageContactInitials C safe)))
      exceptionalComponentsᶜ
  ordinaryRetained_subset : ordinaryRetained ⊆ stageInterval
  ambientInterval : Set Gamma.DPath
  ambientInterval_eq_lift : ambientInterval =
    SliceSegmentCore.liftStageFamily C.ladder C.oldStage stageInterval
  ambientInterval_linkage : IsLinkageBetween Gamma
    C.oldSlice C.newSlice ambientInterval
  ambientInterval_meetsOnlyAtTerminal :
    SliceSpliceSource.MeetsOnlyAtTerminal Gamma ambientInterval C.newSlice
  ambientInterval_in_outerRoof : ∀ p ∈ ambientInterval,
    p.support ⊆ C.outerRoof
  path : FinitePath Gamma.graph
  path_mem_safe : (Sum.inl path : Gamma.DPath) ∈ safe.ambientFamily
  path_start : path.start = z
  path_finish : path.finish ∈ Gamma.target
  front : FinitePath Gamma.graph
  front_mem_interval : (Sum.inl front : Gamma.DPath) ∈ ambientInterval
  front_support_subset_exceptional :
    front.support ⊆ exceptionalComponents
  front_start : front.start = z
  front_finish_mem : front.finish ∈ C.newSlice
  front_slice_pure : front.support ∩ C.newSlice = {front.finish}
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
structure IntervalReferenceMissingCertificate
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {z : V}
    (T : OldStageIntervalTransaction C z) : Prop where
  missing : ∀ p ∈ C.deferredOldStageOrdinaryFamily,
    C.ladder.liftStagePath C.oldStage p ∉ T.ambientInterval →
      p.initial ∈
          ((C.deferredOldStageExceptional ∪ {z}) ∪
            oldStageContactInitials C T.safe) ∨
        p.support ⊆ T.exceptionalComponents

namespace OldStageIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {z : V}

theorem front_support_subset_outerRoof
    (T : OldStageIntervalTransaction C z) :
    T.front.support ⊆ C.outerRoof := by
  apply Gamma.pathSupportRoof (.inl T.front : Gamma.DPath) C.newSlice
  · apply C.legal.frontierChronology C.old_lt_new
    change T.front.start ∈ C.oldSlice
    rw [T.front_start]
    exact T.source_mem
  · intro t ht
    change some T.front.finish = some t at ht
    exact Option.some.inj ht ▸ T.front_finish_mem
  · intro x hx
    apply Set.mem_singleton_iff.2
    exact Set.mem_singleton_iff.1 (T.front_slice_pure ▸ hx)

theorem tail_boundary (T : OldStageIntervalTransaction C z) :
    T.tail.start ∈ C.newSlice ∧ T.tail.finish ∈ Gamma.target := by
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
    (T : OldStageIntervalTransaction C z) :
    T.front.support ⊆ T.path.support :=
  T.front_isPrefix.support_subset

theorem tail_support_subset_path
    (T : OldStageIntervalTransaction C z) :
    T.tail.support ⊆ T.path.support := by
  rw [← T.splice_eq,
    T.front.support_appendFinite_eq_union T.tail T.tail_start
      T.front_tail_inter.subset]
  exact Set.subset_union_right

/-- Away from the splice vertex, the retained ambient suffix is disjoint
from the complete old-to-new interval row. -/
theorem interval_tail_disjoint_off_start
    (T : OldStageIntervalTransaction C z) :
    Disjoint (Gamma.vertexSet T.ambientInterval \ {T.tail.start})
      (T.tail.support \ {T.tail.start}) := by
  rw [T.tail_start]
  apply Set.disjoint_left.2
  rintro x ⟨hxInterval, hxne⟩ ⟨hxTail, _⟩
  have hx := Set.mem_inter hxInterval hxTail
  rw [T.interval_tail_inter] at hx
  exact hxne hx

end OldStageIntervalTransaction

/-- Complete one already-selected deletion-safe path to the full old-to-new
interval row.  This is the source-order form needed in Assertion 9.31: the
safe path is selected first and inserted in the closure seed, while the
later stage (and hence this completion) is chosen only after the closure. -/
theorem ClubStageGeometry.exists_oldStageIntervalTransaction_of_safe_extensionThrough
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hext : _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
      Gamma kappa)
    {z : V} (S : SafeOldStageTargetPath C z)
    (hz : z ∈ C.oldSlice) :
    Nonempty {T : OldStageIntervalTransaction C z //
      T.safe = S ∧ IntervalReferenceMissingCertificate T} := by
  let H := C.ladder.stageWeb C.oldStage
  let X := H.vertexSet S.stageFamily
  let R := H.delete X
  let I := R.retarget (C.newSlice \ X)
  obtain ⟨Wres, hWres⟩ :=
    C.isLinkable_retargetedResidualInterval_of_extensionThrough hext S
  have hWresR : IsLinkageBetween R R.source (C.newSlice \ X) Wres := by
    change IsLinkageBetween R R.source (C.newSlice \ X) Wres at hWres
    exact hWres
  let L : Set H.DPath := H.liftDeleteFamily X Wres
  have hLsmall : IsLinkageBetween H R.source (C.newSlice \ X) L :=
    CardinalInduction.RegularProtectedDeltaLift.IsLinkageBetween.liftDeleteFamily
      H X hWresR
  have hLX : Disjoint (H.vertexSet L) X := by
    exact H.vertexSet_liftDeleteFamily_disjoint
      (hWresR.initialSet_eq.symm ▸
        (Set.Subset.rfl : R.source ⊆ R.source))
  have hL : IsLinkageBetween H R.source C.newSlice L :=
    IsLinkageBetween.mono_target_sdiff hLsmall hLX
  have holdRoof : C.oldSlice ⊆ H.roof C.newSlice := by
    intro v hv
    intro p hp
    let qG := SliceSegmentCore.liftStageFinitePath
      C.ladder C.oldStage p
    have hqG : Gamma.IsTargetPathFrom v qG := by
      have hp' := hp
      change p.start = v ∧ p.finish ∈ Gamma.target at hp'
      exact ⟨by simpa only [qG,
        SliceSegmentCore.liftStageFinitePath_start] using hp'.1,
        by simpa only [qG,
          SliceSegmentCore.liftStageFinitePath_finish] using hp'.2⟩
    obtain ⟨t, htqG, htT⟩ :=
      (C.legal.frontierChronology C.old_lt_new hv) qG hqG
    exact ⟨t, by simpa only [qG,
      SliceSegmentCore.liftStageFinitePath_support] using htqG, htT⟩
  have hRroof : R.source ⊆ H.roof C.newSlice := by
    intro v hv
    exact holdRoof hv.1
  let hsepL : RelationalRoof.Separates H.graph.Adj
      R.source C.newSlice C.newSlice := by
    intro _ t p _ ht
    exact ⟨t, p.end_mem_support, ht⟩
  let Lstop : Set H.DPath := firstHitPrefixFamily hL hsepL
  have hLstop : IsLinkageBetween H R.source C.newSlice Lstop :=
    firstHitPrefixFamily_isLinkageBetween hL hsepL
  have hLstopL : H.vertexSet Lstop ⊆ H.vertexSet L := by
    rintro x ⟨q, ⟨a, rfl⟩, hxq⟩
    refine ⟨(linkageMemberAt hL a).1, (linkageMemberAt hL a).2, ?_⟩
    rw [linkageMemberAt_eq_finite hL a]
    exact linkageFirstHitAt_support_subset hL hsepL a hxq
  have hLstopX : Disjoint (H.vertexSet Lstop) X :=
    hLX.mono_left hLstopL
  have hzRoof : z ∈ H.roof C.newSlice := holdRoof hz
  have hzRoofSet : ({z} : Set V) ⊆ H.roof C.newSlice := by
    simpa only [Set.singleton_subset_iff]
  let hsep : RelationalRoof.Separates H.graph.Adj
      ({z} : Set V) H.target C.newSlice :=
    separates_target_of_subset_roof hzRoofSet
  let Pfront : Set H.DPath := firstHitPrefixFamily S.stage_linkage hsep
  have hPfront : IsLinkageBetween H ({z} : Set V) C.newSlice Pfront :=
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
      C.newSlice (Pfront ∪ Lstop) :=
    SingularRetargetedRow.linkageBetween_union_of_vertexSet_disjoint
      H hPfront hLstop hdisjoint
  have hHNorm : H.IsNormalized := by
    intro x y hxy
    let Q := Gamma.quotient
      (Gamma.terminalFrontier (C.ladder.warpAt C.oldStage))
    have hxyQ : Q.graph.Adj x y := Q.essentialPart_adj_imp hxy
    have hxyGamma : Gamma.graph.Adj x y := Gamma.quotient_adj_imp hxyQ
    refine ⟨?_, (C.normalized hxyGamma).2⟩
    have hNoEnterQ : Q.NoEdgeEnters Q.source :=
      DWeb.NoEdgeEnters.quotient (G := Gamma)
        (fun {_ _} e hy ↦ (C.normalized e).1 hy)
    exact fun hy ↦ hNoEnterQ hxyQ hy.1
  have hXsource : X ∩ H.source = ({z} : Set V) := by
    have hzH : z ∈ H.source := by
      change z ∈ C.oldSlice
      exact hz
    exact IsLinkageBetween.vertexSet_inter_source_eq hHNorm
      S.stage_linkage (by simpa only [Set.singleton_subset_iff] using hzH)
  have hsources : ({z} : Set V) ∪ R.source = C.oldSlice := by
    change ({z} : Set V) ∪ (H.source \ X) = H.source
    ext x
    constructor
    · rintro (hxz | hxR)
      · have hzH : z ∈ H.source := by
          change z ∈ C.oldSlice
          exact hz
        exact hxz ▸ hzH
      · exact hxR.1
    · intro hxH
      by_cases hxX : x ∈ X
      · have hx : x ∈ X ∩ H.source := ⟨hxX, hxH⟩
        rw [hXsource] at hx
        exact Or.inl hx
      · exact Or.inr ⟨hxH, hxX⟩
  have hBaseInterval : IsLinkageBetween H C.oldSlice C.newSlice
      (Pfront ∪ Lstop) := by
    rwa [hsources] at hUnion
  have hPfrontTight : SliceSpliceSource.MeetsOnlyAtTerminal
      H Pfront C.newSlice :=
    firstHitPrefixFamily_meetsOnlyAtTerminal S.stage_linkage hsep
  have hLstopTight : SliceSpliceSource.MeetsOnlyAtTerminal
      H Lstop C.newSlice :=
    firstHitPrefixFamily_meetsOnlyAtTerminal hL hsepL
  have hBaseTight : SliceSpliceSource.MeetsOnlyAtTerminal
      H (Pfront ∪ Lstop) C.newSlice := by
    intro p hp
    exact hp.elim (hPfrontTight p) (hLstopTight p)
  /- Retain the arbitrary completed interval only in the alternating
  components rooted at an inessential source, the scheduled source, or an
  ordinary interval which touches the full deletion-safe path.  The last
  class is essential: it makes every restored ordinary interval disjoint
  from the ambient target suffix. -/
  let M : Set H.DPath :=
    H.pathsMeetingFamily C.deferredOldStageOrdinaryFamily S.stageFamily
  let contact : Set V := H.initialSet M
  have hMcard : #M ≤ kappa := by
    apply H.mk_pathsMeetingFamily_le C.deferredOldStageOrdinaryFamily S.stageFamily
    · exact C.deferredOldStageOrdinaryFamily_isLinkageBetween.isWarp
    · exact C.capacity_infinite
    · exact (mk_linkage_le_initial H S.stage_linkage).trans (by
        rw [Cardinal.mk_singleton]
        exact Cardinal.one_le_aleph0.trans C.capacity_infinite)
    · intro p _hp
      exact p.support_countable.le_aleph0.trans C.capacity_infinite
  have hcontactCard : #contact ≤ kappa :=
    (mk_initialSet_le_family H M).trans hMcard
  have hcontactSub : contact ⊆ C.oldSlice := by
    rintro x ⟨p, hpM, rfl⟩
    have hpInitial : p.initial ∈ H.initialSet C.deferredOldStageOrdinaryFamily :=
      ⟨p, hpM.1, rfl⟩
    rw [C.deferredOldStageOrdinaryFamily_isLinkageBetween.initialSet_eq] at hpInitial
    exact hpInitial.1
  let Ebase : Set V := C.deferredOldStageExceptional ∪ {z}
  let E : Set V := Ebase ∪ contact
  have hEsub : E ⊆ C.oldSlice := by
    rintro x ((hx | rfl) | hxContact)
    · exact hx.1
    · exact hz
    · exact hcontactSub hxContact
  have hEcard : #E ≤ kappa := by
    have hbase : #Ebase ≤ kappa := by
      refine (Cardinal.mk_union_le C.deferredOldStageExceptional ({z} : Set V)).trans ?_
      apply Cardinal.add_le_of_le C.capacity_infinite
      · exact C.mk_deferredOldStageExceptional_le
      · rw [Cardinal.mk_singleton]
        exact Cardinal.one_le_aleph0.trans C.capacity_infinite
    refine (Cardinal.mk_union_le Ebase contact).trans ?_
    exact Cardinal.add_le_of_le C.capacity_infinite hbase hcontactCard
  let O : Set H.DPath := SliceSpliceSource.initialRestriction H
    C.deferredOldStageOrdinaryFamily (C.oldSlice \ E)
  have hO : IsLinkageBetween H (C.oldSlice \ E) C.newSlice O := by
    apply SliceSpliceSource.isLinkageBetween_initialRestriction
      C.deferredOldStageOrdinaryFamily_isLinkageBetween
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
      H O C.newSlice := by
    intro p hp
    exact C.deferredOldStageOrdinaryFamily_meetsOnlyAtTerminal p hp.1
  have hBaseRoof : H.vertexSet (Pfront ∪ Lstop) ⊆ C.outerRoof :=
    stageLinkage_vertexSet_subset_outerRoof C
      (Set.Subset.rfl) hBaseInterval hBaseTight
  have hORoof : H.vertexSet O ⊆ C.outerRoof :=
    stageLinkage_vertexSet_subset_outerRoof C
      Set.sdiff_subset hO hOTight
  have hERoof : E ⊆ C.outerRoof :=
    hEsub.trans (C.legal.frontierChronology C.old_lt_new)
  let D : Set V := exceptionalComponentVertices H (Pfront ∪ Lstop) O E
  have hDRoof : D ⊆ C.outerRoof :=
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
  have hIRoof : H.vertexSet I ⊆ C.outerRoof := by
    rintro x ⟨p, hpI, hxp⟩
    rcases hpI with hpBase | hpOrdinary
    · exact hBaseRoof ⟨p, hpBase.1, hxp⟩
    · exact hORoof ⟨p, hpOrdinary.1, hxp⟩
  have hInterval : IsLinkageBetween H C.oldSlice C.newSlice I := by
    exact componentMixedFamily_isLinkageBetween_of_complement H
      hBaseInterval hO hEsub
  have hIntervalTight : SliceSpliceSource.MeetsOnlyAtTerminal
      H I C.newSlice := by
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
    SliceSegmentCore.liftStageFamily C.ladder C.oldStage I
  have hW : IsLinkageBetween Gamma C.oldSlice C.newSlice W :=
    CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily hInterval
  let a : ({z} : Set V) := ⟨z, Set.mem_singleton z⟩
  let pathH : FinitePath H.graph := linkageFiniteAt S.stage_linkage a
  have hpathH : (Sum.inl pathH : H.DPath) ∈ S.stageFamily := by
    rw [← linkageMemberAt_eq_finite S.stage_linkage a]
    exact (linkageMemberAt S.stage_linkage a).2
  let frontH : FinitePath H.graph := linkageFirstHitAt S.stage_linkage hsep a
  have hfrontH : (Sum.inl frontH : H.DPath) ∈ Pfront := ⟨a, rfl⟩
  let path : FinitePath Gamma.graph :=
    SliceSegmentCore.liftStageFinitePath C.ladder C.oldStage pathH
  let front : FinitePath Gamma.graph :=
    SliceSegmentCore.liftStageFinitePath C.ladder C.oldStage frontH
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
    (linkageFiniteAt S.stage_linkage a).walk.firstHit C.newSlice
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
        simpa only [C.ladder.support_liftStagePath C.oldStage qH] using hxq
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
  let Tout : OldStageIntervalTransaction C z := {
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
      simpa only [C.ladder.support_liftStagePath C.oldStage q] using hxp
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
  have hmissing : IntervalReferenceMissingCertificate Tout := by
    constructor
    intro p hpF₀ hpNotInterval
    by_cases hpE : p.initial ∈ E
    · exact Or.inl (by
        simpa only [Tout, E, Ebase, contact, M,
          oldStageContactInitials] using hpE)
    · right
      have hpInitial : p.initial ∈ C.oldSlice := by
        have hpInitialSet : p.initial ∈
            H.initialSet C.deferredOldStageOrdinaryFamily :=
          ⟨p, hpF₀, rfl⟩
        rw [C.deferredOldStageOrdinaryFamily_isLinkageBetween.initialSet_eq]
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
        exact C.deferredOldStageOrdinaryFamily_isLinkageBetween.finiteCharacter
          hq.1
      have hpSupport : p.support ⊆ D :=
        path_support_subset_exceptionalComponents_right hOfinite hpO
          p.initial_mem_support hpD
      simpa only [Tout] using hpSupport
  exact ⟨⟨Tout, rfl, hmissing⟩⟩

/-- Legacy universal-induction wrapper around the extension-only completion
of a preselected safe path. -/
theorem ClubStageGeometry.exists_oldStageIntervalTransaction_of_safe
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hext : UniversalExtensionClauseAt V kappa)
    {z : V} (S : SafeOldStageTargetPath C z)
    (hz : z ∈ C.oldSlice) :
    Nonempty {T : OldStageIntervalTransaction C z // T.safe = S} := by
  have hthrough :
      _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
        Gamma kappa := by
    intro rho hrho H hHambient hH
    rcases hrho.lt_or_eq with hlt | rfl
    · exact (hlower rho hlt H hH).1
    · exact hext H hH
  obtain ⟨T⟩ := C.exists_oldStageIntervalTransaction_of_safe_extensionThrough
    hthrough S hz
  exact ⟨⟨T.1, T.2.1⟩⟩

/-- Assertion 9.23 followed by the exact bounded-exceptional application
of `(clubsuit)` to the deleted old-to-new interval. -/
theorem ClubStageGeometry.exists_oldStageIntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hext : UniversalExtensionClauseAt V kappa)
    {z : V} (hz : z ∈ C.oldSlice) :
    Nonempty (OldStageIntervalTransaction C z) := by
  obtain ⟨S⟩ := C.exists_safeOldStageTargetPath hz
  obtain ⟨T⟩ := C.exists_oldStageIntervalTransaction_of_safe hlower hext S hz
  exact ⟨T.1⟩

#print axioms ClubStageGeometry.isLinkable_retargetedResidualInterval
#print axioms
  ClubStageGeometry.isLinkable_retargetedResidualInterval_of_extensionThrough
#print axioms
  ClubStageGeometry.exists_oldStageIntervalTransaction_of_safe_extensionThrough
#print axioms ClubStageGeometry.exists_oldStageIntervalTransaction_of_safe
#print axioms ClubStageGeometry.exists_oldStageIntervalTransaction

end LinkageBlueprint
end Blueprint
end Erdos599
