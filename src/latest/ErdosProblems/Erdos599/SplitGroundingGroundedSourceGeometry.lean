/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedAssertion819
import ErdosProblems.Erdos599.GroundingErasedSourceGeometry

/-!
# Source geometry of grounded split selected requests

Every source gadget of the grounded split auxiliary names a recorded
inessential limiting-ladder component whose initial vertex is an original
source.  This remains true for every control package: controls select a path
inside a request fan but do not change the meaning of its source gadget.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

private abbrev SplitGroundedSourceInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

variable (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
  (hground : Stationary.IsStationaryBelow kappa L.phiGround)

/-- A selected grounded-split request which starts at an old source gadget
decodes from that original vertex. -/
theorem splitGroundedSelectedRequestTrace_initial_of_start_old
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S)
    (r : Request (SplitGroundedSourceInput L hL) S.cut) (x : V)
    (hstart : (strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).start =
        .old x) :
    (selectedRequestTrace
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial = x := by
  let J := SplitGroundedSourceInput L hL
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change (J.decodeFinitePathToExit p hpSource y.1 _).initial = x
      exact J.decodeFinitePathToExit_initial_of_start_old p hpSource y.1 x _
        hstart
  | inr e =>
      change (J.decodeFinitePathToEdgeEntry p hpSource e.1.1 e.1.2 _).initial = x
      exact J.decodeFinitePathToEdgeEntry_initial_of_start_old
        p hpSource e.1.1 e.1.2 x _ hstart

/-- The proxy-source counterpart: the selected trace starts on the recorded
grounded ray represented by that proxy. -/
theorem splitGroundedSelectedRequestTrace_initial_mem_proxyPath
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S)
    (r : Request (SplitGroundedSourceInput L hL) S.cut)
    (i : L.groundedInfiniteRecords)
    (hstart : (strongSelectedPath
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).start =
        .proxy i) :
    (selectedRequestTrace
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial ∈
        i.1.support := by
  let J := SplitGroundedSourceInput L hL
  let U := L.splitGroundedPopularAuxiliaryIndexed hL hground
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  cases r with
  | inl y =>
      change (J.decodeFinitePathToExit p hpSource y.1 _).initial ∈
        (J.proxyPath i).support
      exact J.decodeFinitePathToExit_initial_mem_proxyPath_of_start_proxy
        p hpSource y.1 i _ hstart
  | inr e =>
      change (J.decodeFinitePathToEdgeEntry p hpSource e.1.1 e.1.2 _).initial ∈
        (J.proxyPath i).support
      exact J.decodeFinitePathToEdgeEntry_initial_mem_proxyPath_of_start_proxy
        p hpSource e.1.1 e.1.2 i _ hstart

/-- The original limiting-ladder component represented by a selected
grounded-split request. -/
theorem splitGroundedSelectedRequestTrace_grounded_record
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S)
    (r : Request (SplitGroundedSourceInput L hL) S.cut) :
    ∃ parent : Gamma.DPath,
      parent ∈ Gamma.inessentialPaths L.limitWarp ∧
      (selectedRequestTrace
        (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial ∈
          parent.support ∧
      parent.initial ∈ Gamma.source := by
  let J := SplitGroundedSourceInput L hL
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
    have hindex : U.f ⟨p.start, hpSource⟩ = L.finiteTerminalIndex xs := by
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
    have hparentSource : parent.initial ∈ Gamma.source := by
      obtain ⟨q, hq, hqSource⟩ := ha
      have hpq : parent = q := Option.some.inj (hchosen.symm.trans hq)
      exact hpq ▸ hqSource
    have htraceInitial :
        (selectedRequestTrace U S K r).initial = x :=
      L.splitGroundedSelectedRequestTrace_initial_of_start_old
        hL hground S K r x hstart
    refine ⟨parent, ?_, ?_, hparentSource⟩
    · apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
      change (L.finiteTerminalIndex xs).1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 (L.finiteTerminalIndex xs).2
    · rw [htraceInitial]
      exact Gamma.terminal_mem_support hterminal
  · have ha : L.groundedInfiniteStage i ∈ L.phiGround := by
      have hindex : U.f ⟨p.start, hpSource⟩ =
          L.groundedInfiniteStage i := by
        have hs : (⟨p.start, hpSource⟩ : J.lambda.source) =
            ⟨.proxy i, J.mem_lambda_source_proxy i⟩ := Subtype.ext hstart
        rw [congrArg U.f hs]
        rfl
      exact hindex ▸ hpGround
    have hchosen := (L.groundedInfiniteStage_spec i).2
    have hparentSource : i.1.initial ∈ Gamma.source := by
      obtain ⟨q, hq, hqSource⟩ := ha
      have hiq : i.1 = q := Option.some.inj (hchosen.symm.trans hq)
      exact hiq ▸ hqSource
    refine ⟨i.1, ?_, ?_, hparentSource⟩
    · apply L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
      change (L.groundedInfiniteStage i).1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 (L.groundedInfiniteStage i).2
    · exact L.splitGroundedSelectedRequestTrace_initial_mem_proxyPath
        hL hground S K r i hstart

/-- A finite original-source prefix ending at the selected erased trace's
initial vertex. -/
structure SplitGroundedSelectedRequestRootPrefix
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S)
    (r : Request (SplitGroundedSourceInput L hL) S.cut) where
  parent : Gamma.DPath
  parent_inessential : parent ∈ Gamma.inessentialPaths L.limitWarp
  path : FinitePath Gamma.graph
  start_eq : path.start = parent.initial
  start_mem_source : path.start ∈ Gamma.source
  finish_eq : path.finish =
    (selectedRequestTrace
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) S K r).initial
  support_subset : path.support ⊆ parent.support
  edgeSet_subset : path.edgeSet ⊆ parent.edgeSet

theorem splitGroundedSelectedRequestRootPrefix_nonempty
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (K : GroundingSelection.Controls S)
    (r : Request (SplitGroundedSourceInput L hL) S.cut) :
    Nonempty (L.SplitGroundedSelectedRequestRootPrefix hL hground S K r) := by
  obtain ⟨parent, hparent, hinitial, hsource⟩ :=
    L.splitGroundedSelectedRequestTrace_grounded_record
      hL hground S K r
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix parent hinitial
  refine ⟨{
    parent := parent
    parent_inessential := hparent
    path := q
    start_eq := hqStart
    start_mem_source := ?_
    finish_eq := hqFinish
    support_subset := hqSupport
    edgeSet_subset := hqEdges }⟩
  simpa only [hqStart] using hsource

end DWeb.KappaLadder
end Erdos599
