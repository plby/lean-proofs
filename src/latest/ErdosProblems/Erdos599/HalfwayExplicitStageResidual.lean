/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayExplicitStageComplement
import ErdosProblems.Erdos599.HalfwayPostClosureIntervalTransaction

/-!
# Safely deleted interval completion at an explicit old stage

The old frontier is not assumed small or in the avoiding club. The later
club stage supplies the bounded nonsurvivor set. Ordinary survivor intervals
meeting the selected safe path give the only further exceptions. Retargeting
the safely deleted old stage remains unhindered, and the genuine current
extension clause fills this bounded exception.
-/

noncomputable section

namespace Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor

open Set Cardinal

universe u

variable {V : Type u} {Base H : DWeb V} {kappa : Cardinal.{u}}

theorem linkable_of_bounded_exceptional_complement
    (hext : ExtensionThroughFor Base kappa) (hkappa : aleph0 ≤ kappa)
    (hHBase : ∀ {x y : V}, H.graph.Adj x y → Base.graph.Adj x y)
    (hH : H.IsUnhindered) {E : Set V} (hEsource : E ⊆ H.source) (hEcard : #E ≤ kappa)
    {F : Set H.DPath} (hF : IsLinkageBetween H (H.source \ E) H.target F) :
    IsLinkable H := by
  by_cases hlarge : kappa ≤ #H.source
  · obtain ⟨E', hEE', hE'source, hE'card⟩ :=
      SingularSafeBatch.exists_superset_mk_eq_of_mk_le hEsource hEcard hlarge hkappa
    apply hext kappa le_rfl H hHBase hH E' hE'source hE'card
    refine ⟨SliceSpliceSource.initialRestriction H F (H.source \ E'), ?_⟩
    apply SliceSpliceSource.isLinkageBetween_initialRestriction hF
    rintro x ⟨hxSource, hxE'⟩
    exact ⟨hxSource, fun hxE ↦ hxE' (hEE' hxE)⟩
  · exact hext.linkable_of_source_mk_le hHBase hH (lt_of_not_ge hlarge).le

end Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem SafeStageTargetPath.residual_source_subset_roof_later
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {a b : Stage (succ kappa)}
    {z : V} (S : SafeStageTargetPath C a z) (hab : a < b) :
    let H := C.ladder.stageWeb a
    let X := H.vertexSet S.stageFamily
    (H.delete X).source ⊆ (H.delete X).roof (C.ladder.frontier b \ X) := by
  dsimp only
  intro x hx p hp
  let qH : FinitePath (C.ladder.stageWeb a).graph :=
    p.lift (C.ladder.stageWeb a).delete_adj_imp
  let qG : FinitePath Gamma.graph := SliceSegmentCore.liftStageFinitePath C.ladder a qH
  have hqG : Gamma.IsTargetPathFrom x qG := ⟨hp.1, hp.2.1⟩
  obtain ⟨t, htqG, htT⟩ := (C.legal.frontierChronology hab hx.1) qG hqG
  have htp : t ∈ p.support := by
    simpa only [qG, qH, SliceSegmentCore.liftStageFinitePath_support,
      FinitePath.support_lift] using htqG
  have hstart : Path.initial (Sum.inl p :
      ((C.ladder.stageWeb a).delete
        ((C.ladder.stageWeb a).vertexSet S.stageFamily)).DPath) ∉
        (C.ladder.stageWeb a).vertexSet S.stageFamily := by
    change p.start ∉ _
    rw [hp.1]
    exact hx.2
  have havoid := (C.ladder.stageWeb a).liftDeletePath_avoids
    ((C.ladder.stageWeb a).vertexSet S.stageFamily) (Sum.inl p) hstart
  refine ⟨t, htp, htT, ?_⟩
  intro htX
  rw [(C.ladder.stageWeb a).support_liftDeletePath] at havoid
  exact Set.disjoint_left.mp havoid htp htX

/-- Current extension fills the whole old-to-later residual using only its
bounded exceptional source, even when the old stage is zero. -/
theorem ClubStageGeometry.isLinkable_retargetedStageResidual
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa)
    {a b : Stage (succ kappa)} (hab : a < b) (hb : b ∈ C.club)
    {z : V} (S : SafeStageTargetPath C a z) :
    let H := C.ladder.stageWeb a
    let X := H.vertexSet S.stageFamily
    IsLinkable ((H.delete X).retarget (C.ladder.frontier b \ X)) := by
  let H := C.ladder.stageWeb a
  let X := H.vertexSet S.stageFamily
  let R := H.delete X
  let I := R.retarget (C.ladder.frontier b \ X)
  let E₀ := C.stageExceptional a b
  let F₀ := C.ordinaryStageFamily hab.le
  let M := H.pathsMeetingFamily F₀ S.stageFamily
  let E : Set V := I.source ∩ (E₀ ∪ H.initialSet M)
  let A := I.source \ E
  let F := SliceSpliceSource.initialRestriction H F₀ A
  have hI : I.IsUnhindered := by
    rintro ⟨W, hW⟩
    exact S.deletion_safe ⟨W,
      DWeb.IsHindrance.of_retarget R hW (S.residual_source_subset_roof_later hab)⟩
  have hMcard : #M ≤ kappa := by
    apply H.mk_pathsMeetingFamily_le F₀ S.stageFamily
    · exact (C.ordinaryStageFamily_isLinkageBetween hab.le).isWarp
    · exact C.capacity_infinite
    · exact (SliceCandidate.mk_linkage_le_initial H S.stage_linkage).trans (by
        rw [Cardinal.mk_singleton]
        exact Cardinal.one_le_aleph0.trans C.capacity_infinite)
    · intro p _hp
      exact p.support_countable.le_aleph0.trans C.capacity_infinite
  have hEcard : #E ≤ kappa := by
    apply (Cardinal.mk_subtype_mono Set.inter_subset_right).trans
    apply (Cardinal.mk_union_le E₀ (H.initialSet M)).trans
    exact Cardinal.add_le_of_le C.capacity_infinite (C.mk_stageExceptional_le hab.le hb)
      ((RegularProtectedAmbientRebuild.mk_initialSet_le_family H M).trans hMcard)
  have hAsub : A ⊆ C.ladder.frontier a \ E₀ := by
    rintro x ⟨hxI, hxE⟩
    exact ⟨hxI.1, fun hxE₀ ↦ hxE ⟨hxI, Or.inl hxE₀⟩⟩
  have hF : IsLinkageBetween H A (C.ladder.frontier b) F :=
    SliceSpliceSource.isLinkageBetween_initialRestriction
      (C.ordinaryStageFamily_isLinkageBetween hab.le) hAsub
  have hFavoid : Disjoint (H.vertexSet F) X := by
    apply Set.disjoint_left.mpr
    rintro x ⟨p, hpF, hxp⟩ ⟨q, hqS, hxq⟩
    have hpM : p ∈ M := ⟨hpF.1, q, hqS, Set.not_disjoint_iff.mpr ⟨x, hxp, hxq⟩⟩
    exact hpF.2.2 ⟨hpF.2.1, Or.inr ⟨p, hpM, rfl⟩⟩
  have hFR : IsLinkageBetween R A (C.ladder.frontier b \ X)
      (H.restrictDeleteFamily X F hFavoid) :=
    RegularProtectedAmbientRebuild.IsLinkageBetween.restrictDeleteFamily H X hF hFavoid
  have hFI : IsLinkageBetween I (I.source \ E) I.target
      (H.restrictDeleteFamily X F hFavoid) :=
    ⟨hFR.isWarp, hFR.finiteCharacter, hFR.initialSet_eq,
      hFR.terminalFrontier_subset, hFR.endpointPure⟩
  exact hext.linkable_of_bounded_exceptional_complement C.capacity_infinite
    (C.retargetDeleteStageWeb_adj_ambient a X (C.ladder.frontier b \ X))
    hI Set.inter_subset_left hEcard hFI

#print axioms
  ProtectedCardinalAssembly.ExtensionThroughFor.linkable_of_bounded_exceptional_complement
#print axioms SafeStageTargetPath.residual_source_subset_roof_later
#print axioms ClubStageGeometry.isLinkable_retargetedStageResidual

end Erdos599.Blueprint.LinkageBlueprint
