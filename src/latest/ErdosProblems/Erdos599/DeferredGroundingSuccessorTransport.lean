/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingChronology
import ErdosProblems.Erdos599.GroundingSuccessorTransport

/-!
# Initial successor-roof geometry for deferred grounding

Deferred bookkeeping changes only which successor-inessential component is
recorded.  The geometric conclusions used at the start of source Lemma 7.17
are therefore unchanged: a finite terminal recorded at `a`, and the whole
support of a grounded recorded ray, lie in the strict roof of the frontier
at `a + 1`.

The last theorem packages the exact remaining propagation obligation on the
lossless Lambda decoder.  It is deliberately path-local: once every decoded
signed micro-step preserves the selected roof, the already formalized
list induction supplies `Lemma717SuccessorRoofTransport`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open _root_.Erdos599.DirectedPath

namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The ordinary deferred successor stage represents exactly the extended
successor used by the accumulated-warp recursion. -/
@[simp]
theorem warpAt_successorStage
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (a : Ladder.Stage kappa) :
    L.warpAt (successorStage L hlegal a) = L.successorWarp a := by
  rfl

/-- A deferred finite record terminal is strictly roofed by the corrected
successor frontier. -/
theorem finiteTerminal_mem_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (x : finiteTerminalSet L) :
    x.1 ∈ Gamma.strictRoof
      (L.frontier (successorStage L hlegal (finiteTerminalStage L x))) := by
  obtain ⟨_, p, hp, hpx⟩ := finiteTerminalStage_spec L x
  have hpAvailable :
      p ∈ (bookkeeping L).available (finiteTerminalStage L x) :=
    (bookkeeping L).chosen_mem_available hlegal.validBookkeeping hp
  have hxRaw : x.1 ∈ Gamma.strictRoof
      (Gamma.terminalFrontier
        (L.successorWarp (finiteTerminalStage L x))) :=
    Gamma.terminal_mem_strictRoof_of_mem_inessentialPaths
      hpAvailable.1.1 hpx
  rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages,
    Gamma.strictRoof_essential,
    warpAt_successorStage L hlegal]
  exact hxRaw

/-- Every point of a selected ray is strictly roofed by `T_(a+1)` as soon
as its initial vertex is roofed there.  This form also applies to hanging
records after their earlier-marker provenance is used. -/
theorem chosen_ray_support_subset_strictRoof_successorFrontier_of_initial
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    {a : Ladder.Stage kappa} {r : Ray Gamma.graph}
    (hchosen : L.chosen a = some (.inr r : Gamma.DPath))
    (hinitial : r.initial ∈ Gamma.roof
      (Gamma.terminalFrontier (L.successorWarp a))) :
    r.support ⊆ Gamma.strictRoof
      (L.frontier (successorStage L hlegal a)) := by
  have hpAvailable :
      (.inr r : Gamma.DPath) ∈ (bookkeeping L).available a :=
    (bookkeeping L).chosen_mem_available hlegal.validBookkeeping hchosen
  let T := Gamma.terminalFrontier (L.successorWarp a)
  have hsupportDisjoint : Disjoint r.support T := by
    apply Set.disjoint_left.2
    intro z hzr hzT
    obtain ⟨q, hqWarp, hqTerminal⟩ := hzT
    have hrq : (.inr r : Gamma.DPath) ≠ q := by
      intro hrq
      have hterminal := congrArg Gamma.terminal? hrq
      rw [Gamma.terminal?_ray, hqTerminal] at hterminal
      cases hterminal
    exact Set.disjoint_left.1
      (hlegal.warpStages (Ladder.Stage.succExtended a)
        hpAvailable.1.1.1 hqWarp hrq)
      hzr (Gamma.terminal_mem_support hqTerminal)
  have hsupportRoof : r.support ⊆ Gamma.roof T := by
    apply Gamma.pathSupportRoof (.inr r : Gamma.DPath) T
    · exact hinitial
    · intro t ht
      rw [Gamma.terminal?_ray] at ht
      cases ht
    · intro z hz
      exact False.elim
        (Set.disjoint_left.1 hsupportDisjoint hz.1 hz.2)
  intro z hzr
  have hzRoof : z ∈ Gamma.roof
      (L.frontier (successorStage L hlegal a)) := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      Gamma.roof_essential,
      warpAt_successorStage L hlegal]
    exact hsupportRoof hzr
  refine ⟨hzRoof, ?_⟩
  intro hzEssential
  have hzFrontier : z ∈ L.frontier (successorStage L hlegal a) := by
    rw [← hlegal.frontiersEssential (successorStage L hlegal a)]
    exact hzEssential
  have hzT : z ∈ T := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      warpAt_successorStage L hlegal] at hzFrontier
    exact hzFrontier.1
  exact Set.disjoint_left.1 hsupportDisjoint hzr hzT

/-- Every point of a grounded ray selected by deferred bookkeeping at `a`
is strictly roofed by `T_(a+1)`. -/
theorem chosen_grounded_ray_support_subset_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    {a : Ladder.Stage kappa} {r : Ray Gamma.graph}
    (hchosen : L.chosen a = some (.inr r : Gamma.DPath))
    (hground : r.initial ∈ Gamma.source) :
    r.support ⊆ Gamma.strictRoof
      (L.frontier (successorStage L hlegal a)) := by
  apply chosen_ray_support_subset_strictRoof_successorFrontier_of_initial
    L hlegal hchosen
  exact hlegal.roofsSourceAtStages (Ladder.Stage.succExtended a) hground

/-- A marker inserted at `b` is roofed by the immediately following
deferred frontier. -/
theorem marker_mem_roof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    {b : Ladder.Stage kappa} {y : V} (hy : L.marker b = some y) :
    y ∈ Gamma.roof (L.frontier (successorStage L hlegal b)) := by
  have hyWarp : Gamma.trivialPath y ∈ L.successorWarp b :=
    (hlegal.freshMarkers.2 b y hy).2
  have hyTerminal : y ∈ Gamma.terminalFrontier (L.successorWarp b) :=
    ⟨Gamma.trivialPath y, hyWarp, Gamma.terminal?_trivialPath y⟩
  rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages,
    Gamma.roof_essential,
    warpAt_successorStage L hlegal]
  exact Gamma.subset_roof _ hyTerminal

/-- The represented path of every deferred infinite proxy is strictly
roofed by the successor of its record stage. -/
theorem infinitePath_support_subset_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (i : infiniteRecords L) :
    (infinitePath L hlegal i).support ⊆ Gamma.strictRoof
      (L.frontier (successorStage L hlegal (infiniteStage L i))) := by
  obtain ⟨r, hr⟩ := infinitePath_isRay L hlegal i
  have hchosen : L.chosen (infiniteStage L i) =
      some (.inr r : Gamma.DPath) := by
    rw [← hr]
    exact (infiniteStage_spec L i).2
  have hir : i.1 = (.inr r : Gamma.DPath) := by
    simpa [infinitePath] using hr
  have hpInitialRoof : r.initial ∈ Gamma.roof
      (Gamma.terminalFrontier (L.successorWarp (infiniteStage L i))) := by
    by_cases hground : r.initial ∈ Gamma.source
    · exact hlegal.roofsSourceAtStages
        (Ladder.Stage.succExtended (infiniteStage L i)) hground
    · have haDeferredHanging : infiniteStage L i ∈ phiHanging L := by
        refine ⟨(infiniteStage_spec L i).1.1, ?_⟩
        rintro ⟨p, hp, hpGround⟩
        have hpr : p = (.inr r : Gamma.DPath) :=
          Option.some.inj (hp.symm.trans hchosen)
        rw [hpr] at hpGround
        exact hground hpGround
      have haLegacyHanging : infiniteStage L i ∈ L.phiHanging :=
        phiHanging_subset_legacy L hlegal.validBookkeeping haDeferredHanging
      obtain ⟨b, hba, hbMarker⟩ :=
        hlegal.hangingProvenance (infiniteStage L i) haLegacyHanging
          (.inr r : Gamma.DPath) hchosen
      have hbRoof : r.initial ∈ Gamma.roof
          (L.frontier (successorStage L hlegal b)) :=
        marker_mem_roof_successorFrontier L hlegal hbMarker
      have hsucc : successorStage L hlegal b <
          successorStage L hlegal (infiniteStage L i) := by
        change b.1 + 1 < (infiniteStage L i).1 + 1
        rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
        exact Order.succ_lt_succ hba
      have haRoof : r.initial ∈ Gamma.roof
          (L.frontier (successorStage L hlegal (infiniteStage L i))) :=
        Gamma.roof_cut (hlegal.frontierChronology hsucc) hbRoof
      rw [L.frontier_eq_essential_terminalFrontier
          hlegal.roofsSourceAtStages,
        Gamma.roof_essential,
        warpAt_successorStage L hlegal] at haRoof
      exact haRoof
  rw [hr]
  exact chosen_ray_support_subset_strictRoof_successorFrontier_of_initial
    L hlegal hchosen hpInitialRoof

/-- Input-level form of the deferred proxy start-point result. -/
theorem popularAuxiliary_proxyPath_support_subset_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (i : infiniteRecords L) :
    ((popularAuxiliaryInput L hlegal).proxyPath i).support ⊆
      Gamma.strictRoof
        (L.frontier (successorStage L hlegal (infiniteStage L i))) := by
  exact infinitePath_support_subset_strictRoof_successorFrontier L hlegal i

namespace Decoder

open PopularAuxiliary

/-- The lossless decoder retains an old Lambda source as its initial
original vertex. -/
theorem initial_eq_of_start_eq_old
    (I : Input Gamma (infiniteRecords L))
    (q : FinitePath I.lambda.graph)
    (hs : q.start ∈ I.lambda.source) (ht : q.finish ∈ I.lambda.target)
    {x : V} (hqx : q.start = .old x) :
    (I.decodeFinitePath q hs ht).initial = x := by
  classical
  unfold Input.decodeFinitePath
  split
  · rename_i z hz
    change z.1 = x
    exact Input.LambdaVertex.old.inj (z.2.2.symm.trans hqx)
  · rename_i i hi
    have hbad := i.2.symm.trans hqx
    cases hbad

/-- The lossless decoder starts a proxy path at an actual point of the
represented ray. -/
theorem initial_mem_proxyPath_of_start_eq_proxy
    (I : Input Gamma (infiniteRecords L))
    (q : FinitePath I.lambda.graph)
    (hs : q.start ∈ I.lambda.source) (ht : q.finish ∈ I.lambda.target)
    {i : infiniteRecords L} (hqi : q.start = .proxy i) :
    (I.decodeFinitePath q hs ht).initial ∈ (I.proxyPath i).support := by
  classical
  unfold Input.decodeFinitePath
  split
  · rename_i x hx
    have hbad := x.2.2.symm.trans hqi
    cases hbad
  · rename_i j hj
    have hji : j.1 = i :=
      Input.LambdaVertex.proxy.inj (j.2.symm.trans hqi)
    subst i
    unfold Input.decodeFinitePathFromProxy
    dsimp only
    exact (Classical.choice (show Nonempty
        {x : V // x ∈ (I.proxyPath j.1).support ∧
          Input.RunsFromTo x (I.chooseTargetEndpoint q ht).1
            (I.decodeWalkSteps q.walk)} from by
      rcases I.decodeWalkSteps_runs_from_eq_proxy q.walk j.2
          (I.finish_old_gadget q
            (I.chooseTargetEndpoint q ht).2.2).2 with
        ⟨x, hxRay, hrun⟩
      exact ⟨⟨x, hxRay, hrun⟩⟩)).2.1

/-- The lossless decoder retains an old Lambda target as its terminal
original vertex. -/
theorem terminal_eq_of_finish_eq_old
    (I : Input Gamma (infiniteRecords L))
    (q : FinitePath I.lambda.graph)
    (hs : q.start ∈ I.lambda.source) (ht : q.finish ∈ I.lambda.target)
    {y : V} (hqy : q.finish = .old y) :
    (I.decodeFinitePath q hs ht).terminal = y := by
  classical
  have hy : (I.chooseTargetEndpoint q ht).1 = y :=
    Input.LambdaVertex.old.inj
      ((I.chooseTargetEndpoint q ht).2.2.symm.trans hqy)
  unfold Input.decodeFinitePath
  split <;> exact hy

end Decoder

/-- Boundary-aware signed-step form of the local Lemma 7.17 obligation.

The start points are already in the strict roof by the preceding theorems.
A step whose entry is still off the essential stage frontier must preserve
the full roof.  At an essential-frontier entry the local statement is
allowed to escape; that contact is retained explicitly by
`DecodedSuccessorRoofOrEssentialEntry` and is discharged only by the
separate source-bookkeeping recovery below. -/
structure DecodedSuccessorRoofStepClosed
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) : Prop where
  finite : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (x : finiteTerminalSet L), q.start = .old x.1 →
      let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
      ∀ s ∈ T.steps,
        s.entry ∈ Gamma.roof
            (L.frontier (successorStage L hlegal (finiteTerminalStage L x))) →
          s.exit ∈ Gamma.roof
              (L.frontier
                (successorStage L hlegal (finiteTerminalStage L x))) ∨
            s.entry ∈ Gamma.essential
              (L.frontier
                (successorStage L hlegal (finiteTerminalStage L x)))
  proxy : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (i : infiniteRecords L), q.start = .proxy i →
      let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
      ∀ s ∈ T.steps,
        s.entry ∈ Gamma.roof
            (L.frontier (successorStage L hlegal (infiniteStage L i))) →
          s.exit ∈ Gamma.roof
              (L.frontier (successorStage L hlegal (infiniteStage L i))) ∨
            s.entry ∈ Gamma.essential
              (L.frontier (successorStage L hlegal (infiniteStage L i)))

/-- The only local step geometry not supplied by abstract roof calculus:
a decoded backward ladder step whose entry is in the strict roof returns to
the full roof.  Keeping this separate prevents the false assertion that a
forward connector from an essential frontier point must preserve the roof. -/
structure DecodedSuccessorBackwardStepClosed
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) : Prop where
  finite : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (x : finiteTerminalSet L), q.start = .old x.1 →
      let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
      ∀ s ∈ T.steps, s.direction = .backward →
        s.entry ∈ Gamma.strictRoof
            (L.frontier
              (successorStage L hlegal (finiteTerminalStage L x))) →
          s.exit ∈ Gamma.roof
            (L.frontier
              (successorStage L hlegal (finiteTerminalStage L x)))
  proxy : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (i : infiniteRecords L), q.start = .proxy i →
      let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
      ∀ s ∈ T.steps, s.direction = .backward →
        s.entry ∈ Gamma.strictRoof
            (L.frontier (successorStage L hlegal (infiniteStage L i))) →
          s.exit ∈ Gamma.roof
            (L.frontier (successorStage L hlegal (infiniteStage L i)))

/-- Abstract forward-roof calculus plus the genuine backward-ladder
obligation yields the boundary-aware local step invariant. -/
theorem decodedSuccessorRoofStepClosed_of_backward
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (H : DecodedSuccessorBackwardStepClosed L hlegal) :
    DecodedSuccessorRoofStepClosed L hlegal := by
  constructor
  · intro q hs ht x hqx
    let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
    change ∀ s ∈ T.steps,
      s.entry ∈ Gamma.roof
          (L.frontier
            (successorStage L hlegal (finiteTerminalStage L x))) →
        s.exit ∈ Gamma.roof
            (L.frontier
              (successorStage L hlegal (finiteTerminalStage L x))) ∨
          s.entry ∈ Gamma.essential
            (L.frontier
              (successorStage L hlegal (finiteTerminalStage L x)))
    intro s hsT hsRoof
    by_cases hsEssential : s.entry ∈ Gamma.essential
        (L.frontier
          (successorStage L hlegal (finiteTerminalStage L x)))
    · exact Or.inr hsEssential
    · left
      have hsStrict : s.entry ∈ Gamma.strictRoof
          (L.frontier
            (successorStage L hlegal (finiteTerminalStage L x))) :=
        ⟨hsRoof, hsEssential⟩
      cases hdirection : s.direction with
      | forward =>
          exact s.exit_mem_roof_of_forward
            (hlegal.frontiersEssential _) (T.valid s hsT) hdirection hsStrict
      | backward => exact H.finite q hs ht x hqx s hsT hdirection hsStrict
  · intro q hs ht i hqi
    let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
    change ∀ s ∈ T.steps,
      s.entry ∈ Gamma.roof
          (L.frontier (successorStage L hlegal (infiniteStage L i))) →
        s.exit ∈ Gamma.roof
            (L.frontier (successorStage L hlegal (infiniteStage L i))) ∨
          s.entry ∈ Gamma.essential
            (L.frontier (successorStage L hlegal (infiniteStage L i)))
    intro s hsT hsRoof
    by_cases hsEssential : s.entry ∈ Gamma.essential
        (L.frontier (successorStage L hlegal (infiniteStage L i)))
    · exact Or.inr hsEssential
    · left
      have hsStrict : s.entry ∈ Gamma.strictRoof
          (L.frontier (successorStage L hlegal (infiniteStage L i))) :=
        ⟨hsRoof, hsEssential⟩
      cases hdirection : s.direction with
      | forward =>
          exact s.exit_mem_roof_of_forward
            (hlegal.frontiersEssential _) (T.valid s hsT) hdirection hsStrict
      | backward => exact H.proxy q hs ht i hqi s hsT hdirection hsStrict

/-- The exact global invariant obtained from boundary-aware local closure:
the decoded endpoint is roofed, or the trace records an entry into the
essential successor frontier. -/
structure DecodedSuccessorRoofOrEssentialEntry
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) : Prop where
  finite : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (x : finiteTerminalSet L), q.start = .old x.1 →
      let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
      T.terminal ∈ Gamma.roof
          (L.frontier (successorStage L hlegal (finiteTerminalStage L x))) ∨
        ∃ s ∈ T.steps,
          s.entry ∈ Gamma.essential
            (L.frontier
              (successorStage L hlegal (finiteTerminalStage L x)))
  proxy : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (i : infiniteRecords L), q.start = .proxy i →
      let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
      T.terminal ∈ Gamma.roof
          (L.frontier (successorStage L hlegal (infiniteStage L i))) ∨
        ∃ s ∈ T.steps,
          s.entry ∈ Gamma.essential
            (L.frontier (successorStage L hlegal (infiniteStage L i)))

/-- Boundary-aware local closure gives the precise roof-or-frontier-entry
invariant, without pretending that an arbitrary connector can leave an
essential frontier point while preserving the roof. -/
theorem decodedSuccessorRoofOrEssentialEntry_of_stepClosed
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (H : DecodedSuccessorRoofStepClosed L hlegal) :
    DecodedSuccessorRoofOrEssentialEntry L hlegal := by
  let I := popularAuxiliaryInput L hlegal
  constructor
  · intro q hs ht x hqx
    let T := I.decodeFinitePath q hs ht
    have hinit : T.initial ∈ Gamma.roof
        (L.frontier (successorStage L hlegal (finiteTerminalStage L x))) := by
      rw [show T.initial = x.1 from Decoder.initial_eq_of_start_eq_old
        I q hs ht hqx]
      exact Gamma.strictRoof_subset_roof _
        (finiteTerminal_mem_strictRoof_successorFrontier L hlegal x)
    exact T.terminal_mem_or_exists_entry _ _ hinit
      (H.finite q hs ht x hqx)
  · intro q hs ht i hqi
    let T := I.decodeFinitePath q hs ht
    have hinit : T.initial ∈ Gamma.roof
        (L.frontier (successorStage L hlegal (infiniteStage L i))) := by
      exact Gamma.strictRoof_subset_roof _
        (popularAuxiliary_proxyPath_support_subset_strictRoof_successorFrontier
          L hlegal i
          (Decoder.initial_mem_proxyPath_of_start_eq_proxy I q hs ht hqi))
    exact T.terminal_mem_or_exists_entry _ _ hinit
      (H.proxy q hs ht i hqi)

/-- The source-bookkeeping recovery obligation at an essential successor
frontier entry.  This is deliberately separate from local connector
closure: its proof may use the record which owns the frontier entry (or
route that record into the equal/separator branch). -/
structure DecodedSuccessorEssentialEntryRecovered
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) : Prop where
  finite : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (x : finiteTerminalSet L), q.start = .old x.1 →
      let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
      (∃ s ∈ T.steps,
        s.entry ∈ Gamma.essential
          (L.frontier
            (successorStage L hlegal (finiteTerminalStage L x)))) →
        T.terminal ∈ Gamma.roof
          (L.frontier (successorStage L hlegal (finiteTerminalStage L x)))
  proxy : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (i : infiniteRecords L), q.start = .proxy i →
      let T := (popularAuxiliaryInput L hlegal).decodeFinitePath q hs ht
      (∃ s ∈ T.steps,
        s.entry ∈ Gamma.essential
          (L.frontier (successorStage L hlegal (infiniteStage L i)))) →
        T.terminal ∈ Gamma.roof
          (L.frontier (successorStage L hlegal (infiniteStage L i)))

/-- Boundary-aware step closure plus source-bookkeeping recovery completes
the successor-roof transport. -/
theorem lemma717SuccessorRoofTransport_of_decodedStepClosed
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (H : DecodedSuccessorRoofStepClosed L hlegal)
    (Hrecover : DecodedSuccessorEssentialEntryRecovered L hlegal) :
    Lemma717SuccessorRoofTransport L hlegal := by
  let I := popularAuxiliaryInput L hlegal
  let Hclosed := decodedSuccessorRoofOrEssentialEntry_of_stepClosed
    L hlegal H
  constructor
  · intro q hs ht x y hqx hqy
    let T := I.decodeFinitePath q hs ht
    have hinit : T.initial ∈ Gamma.roof
        (L.frontier (successorStage L hlegal (finiteTerminalStage L x))) := by
      rw [show T.initial = x.1 from Decoder.initial_eq_of_start_eq_old
        I q hs ht hqx]
      exact Gamma.strictRoof_subset_roof _
        (finiteTerminal_mem_strictRoof_successorFrontier L hlegal x)
    have hterminal : T.terminal ∈ Gamma.roof
        (L.frontier (successorStage L hlegal (finiteTerminalStage L x))) := by
      rcases Hclosed.finite q hs ht x hqx with hroof | hentry
      · exact hroof
      · exact Hrecover.finite q hs ht x hqx hentry
    have hTy : T.terminal = y :=
      Decoder.terminal_eq_of_finish_eq_old I q hs ht hqy
    rwa [hTy] at hterminal
  · intro q hs ht i y hqi hqy
    let T := I.decodeFinitePath q hs ht
    have hinit : T.initial ∈ Gamma.roof
        (L.frontier (successorStage L hlegal (infiniteStage L i))) := by
      exact Gamma.strictRoof_subset_roof _
        (popularAuxiliary_proxyPath_support_subset_strictRoof_successorFrontier
          L hlegal i
          (Decoder.initial_mem_proxyPath_of_start_eq_proxy I q hs ht hqi))
    have hterminal : T.terminal ∈ Gamma.roof
        (L.frontier (successorStage L hlegal (infiniteStage L i))) := by
      rcases Hclosed.proxy q hs ht i hqi with hroof | hentry
      · exact hroof
      · exact Hrecover.proxy q hs ht i hqi hentry
    have hTy : T.terminal = y :=
      Decoder.terminal_eq_of_finish_eq_old I q hs ht hqy
    rwa [hTy] at hterminal

/-- Convenient two-layer constructor: the local backward-edge geometry is
first combined with the unconditional forward-edge roof calculus, and only
then with the independent source-bookkeeping recovery. -/
theorem lemma717SuccessorRoofTransport_of_backward_and_recovery
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L)
    (Hbackward : DecodedSuccessorBackwardStepClosed L hlegal)
    (Hrecover : DecodedSuccessorEssentialEntryRecovered L hlegal) :
    Lemma717SuccessorRoofTransport L hlegal :=
  lemma717SuccessorRoofTransport_of_decodedStepClosed L hlegal
    (decodedSuccessorRoofStepClosed_of_backward L hlegal Hbackward)
    Hrecover

end Deferred
end KappaLadder
end DWeb
end Erdos599
