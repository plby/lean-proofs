/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedSourceGeometry
import ErdosProblems.Erdos599.SplitGroundingGroundedUnused

/-!
# Reserved-root provenance for grounded split requests

The grounded source geometry already gives an original-source prefix for
every selected request.  This file retains the chosen stage of its parent.
The unused-stage subtraction then shows that the prefix starts at a source
different from the reserved record's initial vertex.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

private abbrev SplitGroundedRootInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

/-- Full chosen-stage provenance of a request selected from the grounded
split auxiliary. -/
theorem splitGroundedSelectedRequestTrace_grounded_record_data
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S)
    (r : Request (SplitGroundedRootInput L hL) S.cut) :
    ∃ (a : Ladder.Stage kappa) (parent : Gamma.DPath),
      a ∈ L.phiGround ∧ L.chosen a = some parent ∧
        parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        (selectedRequestTrace
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial ∈
          parent.support ∧
        parent.initial ∈ Gamma.source ∧
        a = (L.splitGroundedPopularAuxiliaryIndexed hL hground).f
          ⟨(strongSelectedPath
            (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).start,
            (strongSelectedWarp
              (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K)
                |>.starts_in_source ⟨r, rfl⟩⟩ := by
  let J := SplitGroundedRootInput L hL
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  have hpGround : U.f ⟨p.start, hpSource⟩ ∈ L.phiGround :=
    L.splitGroundedPopularAuxiliary_sourceIndex_mem_phiGround
      hL hground ⟨p.start, hpSource⟩
  rcases J.start_of_mem_lambda_source p hpSource with
      ⟨x, hxFinite, hstart⟩ | ⟨i, hstart⟩
  · let xs : L.groundedFiniteTerminalSet := ⟨x, hxFinite⟩
    have hindex : U.f ⟨p.start, hpSource⟩ =
        L.finiteTerminalIndex xs := by
      have hs : (⟨p.start, hpSource⟩ : J.lambda.source) =
          ⟨.old xs.1, (J.mem_lambda_source_old xs.1).2 xs.2⟩ :=
        Subtype.ext hstart
      rw [congrArg U.f hs]
      rfl
    have ha : L.finiteTerminalIndex xs ∈ L.phiGround := hindex ▸ hpGround
    let xs' : L.finiteTerminalSet :=
      ⟨xs.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xs.2⟩
    obtain ⟨_hfinite, parent, hchosen, hterminal⟩ :=
      L.finiteTerminalStage_spec xs'
    have hstage : L.finiteTerminalStage xs' = L.finiteTerminalIndex xs := rfl
    rw [hstage] at hchosen
    have hsource : parent.initial ∈ Gamma.source := by
      obtain ⟨q, hq, hqSource⟩ := ha
      have hpq : parent = q := Option.some.inj (hchosen.symm.trans hq)
      exact hpq ▸ hqSource
    have htrace : (selectedRequestTrace U S K r).initial ∈ parent.support := by
      rw [L.splitGroundedSelectedRequestTrace_initial_of_start_old
        hL hground S K r x hstart]
      exact Gamma.terminal_mem_support hterminal
    refine ⟨L.finiteTerminalIndex xs, parent, ha, hchosen, ?_, htrace,
      hsource, hindex.symm⟩
    apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
    change (L.finiteTerminalIndex xs).1 + 1 ≤ kappa.ord
    exact (Order.add_one_le_iff).2 (L.finiteTerminalIndex xs).2
  · have hindex : U.f ⟨p.start, hpSource⟩ =
        L.groundedInfiniteStage i := by
      have hs : (⟨p.start, hpSource⟩ : J.lambda.source) =
          ⟨.proxy i, J.mem_lambda_source_proxy i⟩ := Subtype.ext hstart
      rw [congrArg U.f hs]
      rfl
    have ha : L.groundedInfiniteStage i ∈ L.phiGround := hindex ▸ hpGround
    have hchosen := (L.groundedInfiniteStage_spec i).2
    have hsource : i.1.initial ∈ Gamma.source := by
      obtain ⟨q, hq, hqSource⟩ := ha
      have hiq : i.1 = q := Option.some.inj (hchosen.symm.trans hq)
      exact hiq ▸ hqSource
    refine ⟨L.groundedInfiniteStage i, i.1, ha, hchosen, ?_, ?_,
      hsource, hindex.symm⟩
    · apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
      change (L.groundedInfiniteStage i).1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 (L.groundedInfiniteStage i).2
    · exact L.splitGroundedSelectedRequestTrace_initial_mem_proxyPath
        hL hground S K r i hstart

namespace SplitGroundedUnusedRecord

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

/-- No selected request starts at the auxiliary source representing the
unused grounded stage. -/
theorem auxiliarySource_ne_selectedPath_start
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (r : Request (SplitGroundedRootInput L hL) S.cut) :
    R.auxiliarySource.1 ≠
      (strongSelectedPath
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).start := by
  intro heq
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let W := strongSelectedWarp U S K
  let p := strongSelectedPath U S K r
  have hp : p ∈ W.paths := ⟨r, rfl⟩
  apply R.stage_unused
  refine ⟨p, hp, ?_⟩
  have hs : (⟨p.start, W.starts_in_source hp⟩ :
      (SplitGroundedRootInput L hL).lambda.source) = R.auxiliarySource :=
    Subtype.ext heq.symm
  exact (congrArg U.f hs).trans R.source_index

/-- Distinct grounded auxiliary sources represent limiting-ladder parents
with distinct genuine initial vertices. -/
theorem record_initial_ne_parent_initial_of_source_ne
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (x : (SplitGroundedRootInput L hL).lambda.source)
    (a : Ladder.Stage kappa) (parent : Gamma.DPath)
    (hx : x ≠ R.auxiliarySource)
    (hindex : (L.splitGroundedPopularAuxiliaryIndexed hL hground).f x = a)
    (hchosen : L.chosen a = some parent)
    (hparent : parent ∈ L.limitWarp) :
    R.record.initial ≠ parent.initial := by
  intro hroot
  have hparentRecord : parent = R.record :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa)) hparent
      R.limit_inessential.1 parent.initial_mem_support
      (hroot ▸ R.record.initial_mem_support)
  have ha : a = R.stage := by
    apply L.bookkeeping.chosen_stage_unique hL.legal.validBookkeeping
    · exact hchosen
    · rw [hparentRecord]
      exact R.chosen
  apply hx
  apply L.splitGroundedPopularAuxiliaryIndexed_sourceIndexed hL hground
  exact (hindex.trans ha).trans R.source_index.symm

/-- The grounded parent of a selected request starts at an allowed source,
different from the source reserved by stationary subtraction. -/
theorem exists_selectedRequest_parent_with_allowed_root
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (r : Request (SplitGroundedRootInput L hL) S.cut) :
    ∃ (a : Ladder.Stage kappa) (parent : Gamma.DPath),
      a ∈ L.phiGround ∧ L.chosen a = some parent ∧
        parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        (selectedRequestTrace
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial ∈
          parent.support ∧
        parent.initial ∈ Gamma.source \ {R.record.initial} := by
  obtain ⟨a, parent, ha, hchosen, hparent, htrace, hsource, hindex⟩ :=
    L.splitGroundedSelectedRequestTrace_grounded_record_data
      hL hground S K r
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let W := strongSelectedWarp U S K
  let p := strongSelectedPath U S K r
  have hp : p ∈ W.paths := ⟨r, rfl⟩
  let x : (SplitGroundedRootInput L hL).lambda.source :=
    ⟨p.start, W.starts_in_source hp⟩
  have hx : x ≠ R.auxiliarySource := by
    intro heq
    exact R.auxiliarySource_ne_selectedPath_start r
      (congrArg Subtype.val heq.symm)
  have hrootNe : R.record.initial ≠ parent.initial :=
    R.record_initial_ne_parent_initial_of_source_ne x a parent hx
      hindex.symm hchosen hparent.1
  exact ⟨a, parent, ha, hchosen, hparent, htrace,
    ⟨hsource, fun heq ↦ hrootNe (Set.mem_singleton_iff.mp heq).symm⟩⟩

/-- Finite allowed-source prefix of a selected request trace. -/
theorem exists_selectedRequest_allowedRootPrefix
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (r : Request (SplitGroundedRootInput L hL) S.cut) :
    ∃ (parent : Gamma.DPath) (q : FinitePath Gamma.graph),
      parent ∈ Gamma.inessentialPaths L.limitWarp ∧
        q.start ∈ Gamma.source \ {R.record.initial} ∧
        q.finish = (selectedRequestTrace
          (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial ∧
        q.support ⊆ parent.support ∧ q.edgeSet ⊆ parent.edgeSet := by
  obtain ⟨_a, parent, _ha, _hchosen, hparent, htrace, hsource⟩ :=
    R.exists_selectedRequest_parent_with_allowed_root r
  obtain ⟨q, hstart, hfinish, hsupport, hedges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix parent htrace
  refine ⟨parent, q, hparent, ?_, hfinish, hsupport, hedges⟩
  simpa only [hstart] using hsource

/-- A finite old source lying in the popular cut has a canonical finite
parent whose initial vertex is an allowed original source. -/
theorem exists_cutFiniteSource_parent_with_allowed_root
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    {b : V}
    (hb : b ∈ (SplitGroundedRootInput L hL).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ∃ p : FinitePath Gamma.graph,
      L.chosen (L.finiteTerminalIndex ⟨b, hb⟩) =
          some (.inl p : Gamma.DPath) ∧
        p.finish = b ∧ p.start ∈ Gamma.source \ {R.record.initial} ∧
        (.inl p : Gamma.DPath) ∈
          Gamma.inessentialPaths L.limitWarp := by
  let x : L.groundedFiniteTerminalSet := ⟨b, hb⟩
  let x' : L.finiteTerminalSet :=
    ⟨b, L.groundedFiniteTerminalSet_subset_finiteTerminalSet hb⟩
  obtain ⟨_hfinite, parent, hchosen, hterminal⟩ :=
    L.finiteTerminalStage_spec x'
  have hindexStage : L.finiteTerminalIndex x =
      L.finiteTerminalStage x' := rfl
  rw [hindexStage]
  rcases parent with p | ray
  · have hfinish : p.finish = b := Option.some.inj hterminal
    have hparent : (.inl p : Gamma.DPath) ∈
        Gamma.inessentialPaths L.limitWarp := by
      apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
      change (L.finiteTerminalStage x').1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 (L.finiteTerminalStage x').2
    have hbWitness := hb
    obtain ⟨a, ha, recorded, hrecorded, hrecordedTerminal⟩ := hbWitness
    have hstageEq : L.finiteTerminalStage x' = a :=
      L.finiteTerminalStage_eq_of_split hL.legal hrecorded
        hrecordedTerminal
        (L.groundedFiniteTerminalSet_subset_finiteTerminalSet hb)
    have hstageGround : L.finiteTerminalStage x' ∈ L.phiGround :=
      hstageEq ▸ ha.1
    obtain ⟨groundedParent, hgroundedChosen, hgroundedSource⟩ :=
      hstageGround
    have hparentEq : groundedParent = (.inl p : Gamma.DPath) :=
      Option.some.inj (hgroundedChosen.symm.trans hchosen)
    have hsource : p.start ∈ Gamma.source := by
      simpa only [hparentEq, Path.initial] using hgroundedSource
    let source : (SplitGroundedRootInput L hL).lambda.source :=
      ⟨.old b,
        ((SplitGroundedRootInput L hL).mem_lambda_source_old b).2 hb⟩
    have hsourceIndex :
        (L.splitGroundedPopularAuxiliaryIndexed hL hground).f source =
          L.finiteTerminalIndex x := rfl
    have hsourceNe : source ≠ R.auxiliarySource := by
      intro heq
      apply R.auxiliarySource_not_mem_cut
      exact congrArg Subtype.val heq ▸ hbCut
    have hrootNe : R.record.initial ≠ p.start := by
      apply R.record_initial_ne_parent_initial_of_source_ne
        source (L.finiteTerminalIndex x) (.inl p)
        hsourceNe hsourceIndex
      · simpa only [hindexStage] using hchosen
      · exact hparent.1
    refine ⟨p, ?_, hfinish, ⟨hsource, ?_⟩, hparent⟩
    · simpa only [hindexStage] using hchosen
    · exact fun heq ↦ hrootNe (Set.mem_singleton_iff.mp heq).symm
  · change (none : Option V) = some b at hterminal
    cases hterminal

end SplitGroundedUnusedRecord
end DWeb.KappaLadder
end Erdos599
