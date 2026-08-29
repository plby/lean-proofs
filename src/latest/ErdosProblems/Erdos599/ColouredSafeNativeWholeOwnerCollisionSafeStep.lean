/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerResidualPartialStar
import ErdosProblems.Erdos599.SingularCertifiedSafeHistory
import ErdosProblems.Erdos599.HalfwayRetainedLaterLinkage

/-!
# One protected collision repair

An arbitrary bounded target linkage cannot be frozen: deleting its carrier
need not leave an unhindered web.  A `SafeDesignatedLinkage`, however, has
exactly that certificate.  This file proves the honest one-successor step.
One fresh source is safely completed, the bounded additional source set is
solved in the resulting vertex deletion, and the solution is lifted back.
Every previously safe-completed path and the new singleton path are retained
literally.

This is a successor theorem only.  It does not assert residual safety for
the final arbitrary bounded linkage, and hence makes no claim about an
infinite iteration.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.CardinalInduction.SingularCertifiedSafeHistory

open RegularSafeCompletion SingularSafeDesignatedLinkage
open _root_.Erdos599.Blueprint.LinkageBlueprint

universe u

variable {V : Type u}

/-- Add one safely completed source, then solve a bounded disjoint block in
the certified residual.  The old safe family and the new safe path are
literal members of the output linkage. -/
theorem exists_boundedAdditionalLinkage_containing_safeSuccessor
    {Base G : DWeb V} {kappa : Cardinal.{u}}
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Base kappa)
    (hGBase : ∀ {x y : V}, G.graph.Adj x y → Base.graph.Adj x y)
    (hNorm : G.IsNormalized)
    {A B : Set V} (old : SafeDesignatedLinkage G B)
    (hBsource : B ⊆ G.source) {a : V}
    (haSource : a ∈ G.source) (haFresh : a ∉ B)
    (hAsource : A ⊆ G.source)
    (hAdisjoint : Disjoint A (insert a B))
    (hAcard : #A ≤ kappa) :
    ∃ (E : CertifiedSafeDesignatedExtension G old a)
        (W : Set G.DPath),
      IsLinkageBetween G (insert a B ∪ A) G.target W ∧
      E.extended.paths ⊆ W ∧ old.paths ⊆ W ∧
      E.choice.completion.family ⊆ W := by
  obtain ⟨E⟩ := exists_certifiedSafeDesignatedExtension
    G hNorm old hBsource haSource haFresh
  let X := G.vertexSet E.extended.paths
  let H := G.delete X
  have hHNorm : H.IsNormalized :=
    SingularExtension.DWeb.IsNormalized.delete hNorm X
  have hAavoid : A ⊆ Xᶜ := by
    intro x hxA hxX
    have hxNotInitial : x ∉ insert a B := by
      exact fun hx ↦ Set.disjoint_left.1 hAdisjoint hxA hx
    exact hxNotInitial (by
      have hxinter : x ∈ G.vertexSet E.extended.paths ∩ G.source :=
        ⟨hxX, hAsource hxA⟩
      rw [IsLinkageBetween.vertexSet_inter_source_eq
        hNorm E.extended.linkage
          (Set.union_subset (Set.singleton_subset_iff.2 haSource) hBsource)]
        at hxinter
      exact hxinter)
  have hAH : A ⊆ H.source := by
    intro x hxA
    exact ⟨hAsource hxA, hAavoid hxA⟩
  have hNoEnter : H.NoEdgeEnters H.source := by
    intro x y hxy hy
    exact (hHNorm hxy).1 hy
  have hSub : (H.sourceSubweb A).IsUnhindered :=
    E.extended.residual_unhindered.sourceSubweb H hNoEnter hAH
  have hSubBase : ∀ {x y : V},
      (H.sourceSubweb A).graph.Adj x y → Base.graph.Adj x y := by
    intro x y hxy
    exact hGBase hxy.1
  have hSubCard : #(H.sourceSubweb A).source ≤ kappa := by
    simpa only [DWeb.sourceSubweb_source] using hAcard
  have hlinkable : IsLinkable (H.sourceSubweb A) :=
    ProtectedCardinalAssembly.ExtensionThroughFor.linkable_of_source_mk_le
      hext hSubBase hSub hSubCard
  obtain ⟨R, hR⟩ := hlinkable
  change IsLinkageBetween H A H.target R at hR
  let L := G.liftDeleteFamily X R
  have hL : IsLinkageBetween G A G.target L := by
    exact IsLinkageBetween.liftDeleteFamily_toAmbientTarget hR hAH
  have hdisjoint : Disjoint
      (G.vertexSet E.extended.paths) (G.vertexSet L) := by
    exact (G.vertexSet_liftDeleteFamily_disjoint
      (hR.initialSet_eq.symm ▸ hAH)).symm
  have hunion : IsLinkageBetween G ((insert a B) ∪ A) G.target
      (E.extended.paths ∪ L) :=
    SingularRetargetedRow.linkageBetween_union_of_vertexSet_disjoint
      G E.extended.linkage hL hdisjoint
  refine ⟨E, E.extended.paths ∪ L, hunion,
    Set.subset_union_left, ?_, ?_⟩
  · exact E.old_subset_paths.trans Set.subset_union_left
  · exact E.new_subset_paths.trans Set.subset_union_left

#print axioms exists_boundedAdditionalLinkage_containing_safeSuccessor

end Erdos599.CardinalInduction.SingularCertifiedSafeHistory

namespace Erdos599.Blueprint.LinkageBlueprint

open Cardinal Order Set
open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.RegularSafeCompletion
open _root_.Erdos599.CardinalInduction.SingularSafeDesignatedLinkage
open _root_.Erdos599.CardinalInduction.SingularCertifiedSafeHistory
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- Resolve one concrete colliding survivor source by choosing its target
path safely first and then re-solving the entire bounded residual block in
the resulting deletion.  The selected safe path is retained literally.

The earlier arbitrary residual linkage `P` is used only to identify the
collision and is deliberately replaced; it has no deletion-safety
certificate. -/
theorem exists_oneCollisionTargetRepair
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa)
    {P : Set Gamma.DPath} {t : V}
    (ht : t ∈ T.nativeWholeOwnerCollidingSurvivorSources
      R' hlater P) :
    ∃ (W : Set (C.ladder.stageWeb R.later.stage).DPath)
        (q : DirectedPath.FinitePath
          (C.ladder.stageWeb R.later.stage).graph),
      IsLinkageBetween (C.ladder.stageWeb R.later.stage)
          ({t} ∪ T.nativeWholeOwnerNonsurvivingTerminals R')
          (C.ladder.stageWeb R.later.stage).target W ∧
      (Sum.inl q : (C.ladder.stageWeb R.later.stage).DPath) ∈ W ∧
      q.start = t ∧
      ((C.ladder.stageWeb R.later.stage).delete q.support).IsUnhindered := by
  let G := C.ladder.stageWeb R.later.stage
  let A := T.nativeWholeOwnerNonsurvivingTerminals R'
  have hNorm : G.IsNormalized :=
    RegularCandidateProvider.stageWeb_isNormalized
      C.normalized C.ladder R.later.stage
  have hG : G.IsUnhindered :=
    (nativeCapturedGeometry R).newStage_isUnhindered
  let old : SafeDesignatedLinkage G ∅ :=
    SingularSafeDesignatedLinkage.empty G hG
  have htSurviving : t ∈ T.nativeWholeOwnerSurvivingTerminals R' :=
    T.nativeWholeOwnerCollidingSurvivorSources_subset_surviving
      R' hlater P ht
  have htSource : t ∈ G.source := by
    change t ∈ C.ladder.frontier R.later.stage
    exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
      htSurviving.1
  have hAsource : A ⊆ G.source := by
    change A ⊆ C.ladder.frontier R.later.stage
    exact T.nativeWholeOwnerNonsurvivingTerminals_subset_oldFrontier R'
  have hAdisjoint : Disjoint A (insert t ∅) := by
    rw [Set.disjoint_left]
    intro x hxA hx
    have hxt : x = t := by simpa using hx
    subst x
    exact hxA.2 htSurviving.2
  have hGBase : ∀ {x y : V}, G.graph.Adj x y → Gamma.graph.Adj x y := by
    intro x y hxy
    exact C.stageWeb_adj_ambient R.later.stage hxy
  obtain ⟨E, W, hW, _hextended, _hold, hnew⟩ :=
    exists_boundedAdditionalLinkage_containing_safeSuccessor
      hext hGBase hNorm old (by simp) htSource (by simp)
      hAsource hAdisjoint
      (T.nativeWholeOwnerNonsurvivingTerminals_card_le R' hlater)
  let c := E.choice.completion
  refine ⟨W, c.path, ?_, hnew (Set.mem_singleton _), c.start_eq, ?_⟩
  · simpa only [G, A, insert_empty_eq] using hW
  · simpa [G, old, SingularSafeDesignatedLinkage.empty,
      DWeb.vertexSet] using c.next_unhindered

#print axioms
  NativePostClosureIntervalTransaction.exists_oneCollisionTargetRepair

end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
