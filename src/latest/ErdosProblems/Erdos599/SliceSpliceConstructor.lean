/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ExtensionClause
import ErdosProblems.Erdos599.Normalization
import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.SliceSpliceSource
import ErdosProblems.Erdos599.LadderSplitProvenance

/-!
# Constructing the regular controlled-slice splice

This file supplies the constructor side of `SliceSplice`.  The recursion
retains the whole partial source--frontier linkage.  A right-tight annular
slice is starred onto that linkage at a successor stage; at a limit stage
the family is the threadwise direct limit from `Ladder`.  Thus unfinished
threads are not discarded.  A maverick slice component is requested at the
next successor and then reaches the original target.  A thread which is
never maverick follows one component of the limiting ladder warp; the
closed frontier-hit argument supplies its terminal at a limit stage.

The lemmas below separate the four local invariants (tight linkage,
forward extension, closure in `Z`, and the frontier roof) from the final
ordinary/maverick limit dichotomy.  In particular, no completed splice or
`LocalSpliceOperation` is taken as a premise.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceSpliceConstructor

open DirectedPath
open RegularCardinal
open SliceSpliceSource

universe u v

variable {V : Type u}

/-- A path has completed its source thread exactly when it has an original
target terminal.  This proposition is shared by the ordinary and the
completed/pending splice constructors. -/
def ReachesTarget (Gamma : DWeb V) (p : Gamma.DPath) : Prop :=
  ∃ b ∈ Gamma.target, Gamma.terminal? p = some b

/-- Enumerate any source subtype of cardinality at most `kappa` by the
canonical ladder-stage order.  The request is partial because the stage
order can be strictly larger than the source. -/
theorem exists_coveringSourceRequest
    {kappa : Cardinal.{u}} {A : Set V} (hA : #A ≤ kappa) :
    ∃ request : Ladder.Stage kappa → Option ↑A,
      ∀ a : ↑A, ∃ i, request i = some a := by
  let e : A ↪ Ladder.Stage kappa :=
    Classical.choice
      (RegularCardinal.nonempty_embedding_stage_of_mk_le hA)
  let request : Ladder.Stage kappa → Option A := fun i ↦ by
    classical
    exact if h : ∃ a : A, e a = i then some (Classical.choose h) else none
  refine ⟨request, ?_⟩
  intro a
  refine ⟨e a, ?_⟩
  dsimp only [request]
  split
  next h =>
    exact congrArg some (e.injective (Classical.choose_spec h))
  next h =>
    exact (h ⟨a, rfl⟩).elim

/-- The exact ladder geometry used by the regular slice splice.  The
recursive constructor runs on `canonicalLadderCore`, before the independent
bookkeeping choice is installed, so its interface must not require valid
bookkeeping or any record-provenance law. -/
structure SpliceLadderGeometry {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa) : Prop where
  regular : kappa.IsRegular
  initialStage : L.HasInitialStage
  limitStages : L.HasLimitStages
  warpStages : L.HasWarpStages
  frontiersEssential : L.FrontiersAreEssential
  frontierChronology : L.HasFrontierChronology
  strictFrontierChronology : L.HasStrictFrontierChronology

/-- Every vertex of `Z` is roofed by every sufficiently late ladder
frontier.  This is the correct pointwise consequence of `Z ⊆ L.limitRoof`;
literal eventual membership in the frontiers holds only outside the limit
strict roof and is too strong for the regular closing-up set. -/
def IsEventuallyRoofed {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa) (Z : Set V) : Prop :=
  ∀ x ∈ Z, ∃ a : Ladder.Stage kappa,
    ∀ b : Ladder.Stage kappa, a ≤ b → x ∈ Gamma.roof (L.frontier b)

theorem isEventuallyRoofed_of_subset_limitRoof
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} (hL : SpliceLadderGeometry Gamma L)
    {Z : Set V} (hZ : Z ⊆ L.limitRoof) :
    IsEventuallyRoofed Gamma L Z := by
  intro x hxZ
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp (hZ hxZ)
  refine ⟨a, ?_⟩
  intro b hab
  rcases hab.lt_or_eq with hab | rfl
  · exact Gamma.roof_cut (hL.frontierChronology hab) hxa
  · exact hxa

/-- Fewer than `kappa` eventually roofed vertices are roofed by one member
of any prescribed club. -/
theorem exists_club_roof_superset
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z S : Set V} (hkappa : kappa.IsRegular)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hroofed : IsEventuallyRoofed Gamma L Z)
    (hSZ : S ⊆ Z) (hS : #S < kappa) :
    ∃ a ∈ Sigma, S ⊆ Gamma.roof (L.frontier a) := by
  let witness : forall x : S, exists a : Ladder.Stage kappa,
      forall b : Ladder.Stage kappa, a ≤ b ->
        x.1 ∈ Gamma.roof (L.frontier b) :=
    fun x => hroofed x.1 (hSZ x.2)
  let bound : S -> Ladder.Stage kappa :=
    fun x => Classical.choose (witness x)
  have hbound : forall x : S, bound x < kappa.ord :=
    fun x => (bound x).2
  let o : Ordinal.{u} := iSup (fun x : S => (bound x).1 + 1)
  have ho : o < kappa.ord :=
    Stationary.iSup_add_one_lt_ord_of_lt hkappa hS hbound
  let c : Ladder.Stage kappa :=
    RegularCardinal.nextInClub hkappa Sigma hSigma ⟨o, ho⟩
  refine ⟨c, RegularCardinal.nextInClub_mem hkappa Sigma hSigma ⟨o, ho⟩, ?_⟩
  intro x hxS
  let xs : S := ⟨x, hxS⟩
  have hbc : bound xs ≤ c := by
    apply le_trans ?_ (RegularCardinal.lt_nextInClub
      hkappa Sigma hSigma ⟨o, ho⟩).le
    change (bound xs).1 ≤ o
    exact (Order.lt_succ (bound xs).1).le.trans
      (Ordinal.le_iSup (fun y : S => (bound y).1 + 1) xs)
  exact (Classical.choose_spec (witness xs)) c hbc

/-- A frontier-to-frontier linkage meets its source frontier only at the
initial vertex of each member. -/
theorem slice_meets_frontier_only_at_initial
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hT : ControlledSlices.SliceGood Gamma L T alpha beta U) :
    ∀ q ∈ T, ∀ x ∈ q.support, x ∈ L.frontier alpha →
      q.initial = x := by
  intro q hq x hxq hxfrontier
  obtain ⟨r, rfl, _hends, hsource⟩ := hT.1.2.2.2.2 q hq
  have hx : x ∈ r.support ∩ L.frontier alpha := ⟨hxq, hxfrontier⟩
  rw [hsource] at hx
  exact (Set.mem_singleton_iff.mp hx).symm

/-- Annularity and the boundary invariant give exactly the compatibility
hypothesis for the concrete source-star operation. -/
theorem starCompatible_of_annular
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {W T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hessential : Gamma.essential (L.frontier alpha) = L.frontier alpha)
    (hWroof : Gamma.vertexSet W ⊆ Gamma.roof (L.frontier alpha))
    (hboundary : MeetsOnlyAtTerminal Gamma W (L.frontier alpha))
    (hT : SliceSplice.IsAnnularSlice Gamma L T alpha beta U) :
    Gamma.StarCompatible W T := by
  intro p hp q hq x hxp hxq
  have hxfrontier : x ∈ L.frontier alpha :=
    SliceSplice.vertexSet_inter_subset_frontier_of_annular
      hessential hWroof hT ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩
  exact ⟨hboundary p hp x hxp hxfrontier,
    slice_meets_frontier_only_at_initial hT.1 q hq x hxq hxfrontier⟩

/-- The source-star of a closed partial family with a controlled slice
introduces no vertex outside the regular closing-up set. -/
theorem vertexSet_star_subset_of_controlledSlice
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z Ureq : Set V}
    {alpha beta : Ladder.Stage kappa} {W T : Set Gamma.DPath}
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hWZ : Gamma.vertexSet W ⊆ Z)
    (hT : RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta Ureq T)
    (hcompat : Gamma.StarCompatible W T) :
    Gamma.vertexSet (Gamma.star hcompat) ⊆ Z := by
  rintro x ⟨r, ⟨p, rfl⟩, hxr⟩
  rcases Gamma.mem_support_starPath_cases hcompat p hxr with hxold | hxnew
  · exact hWZ ⟨p.1, p.2, hxold⟩
  · obtain ⟨t, q, hpt, hqT, hqstart, hxq⟩ := hxnew
    have htZ : t ∈ Z := hWZ ⟨p.1, p.2, Gamma.terminal_mem_support hpt⟩
    have hqZ : (q.support ∩ Z).Nonempty := by
      refine ⟨t, ?_, htZ⟩
      rw [← hqstart]
      exact q.initial_mem_support
    exact SliceSplice.controlledSlice_path_support_subset
      hclosed hT hqT hqZ hxq

/-! ## The small request contributed by one slice

At the next successor stage Assertion 9.11 requests the terminal of every
maverick member of the current slice.  The following elementary cardinal
lemma is stated for an arbitrary path family: choosing one witnessing path
for each terminal is injective because one path has at most one terminal.
This avoids any unnecessary finiteness assumption on the ambient family. -/

noncomputable def terminalWitness
    (Gamma : DWeb V) (W : Set Gamma.DPath)
    (x : Gamma.terminalFrontier W) : W :=
  ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩

@[simp]
theorem terminal?_terminalWitness
    (Gamma : DWeb V) (W : Set Gamma.DPath)
    (x : Gamma.terminalFrontier W) :
    Gamma.terminal? (terminalWitness Gamma W x) = some x.1 :=
  (Classical.choose_spec x.2).2

theorem terminalWitness_injective
    (Gamma : DWeb V) (W : Set Gamma.DPath) :
    Function.Injective (terminalWitness Gamma W) := by
  intro x y hxy
  apply Subtype.ext
  exact Option.some.inj <| calc
    some x.1 = Gamma.terminal? (terminalWitness Gamma W x) :=
      (terminal?_terminalWitness Gamma W x).symm
    _ = Gamma.terminal? (terminalWitness Gamma W y) :=
      congrArg Gamma.terminal? (congrArg Subtype.val hxy)
    _ = some y.1 := terminal?_terminalWitness Gamma W y

theorem mk_terminalFrontier_le
    (Gamma : DWeb V) (W : Set Gamma.DPath) :
    #(Gamma.terminalFrontier W) ≤ #W :=
  Cardinal.mk_le_of_injective (terminalWitness_injective Gamma W)

/-- Terminals of the maverick members of one slice.  These, rather than
the internal vertices of the mavericks, are the vertices inserted in the
next request set of the splice recursion. -/
def maverickTerminals {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (T : Set Gamma.DPath) : Set V :=
  Gamma.terminalFrontier
    (ControlledSlices.sliceMavericks Gamma L.limitWarp T)

theorem maverickTerminals_small
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hT : RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T) :
    #(maverickTerminals Gamma L T) < kappa :=
  (mk_terminalFrontier_le Gamma
    (ControlledSlices.sliceMavericks Gamma L.limitWarp T)).trans_lt hT.2.1

theorem maverickTerminals_subset_frontier
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hT : RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T) :
    maverickTerminals Gamma L T ⊆ L.frontier beta := by
  rintro x ⟨p, hpM, hpx⟩
  exact hT.1.1.terminalFrontier_subset ⟨p, hpM.1, hpx⟩

theorem maverickTerminals_subset_closure
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hT : RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T) :
    maverickTerminals Gamma L T ⊆ Z := by
  rintro x ⟨p, hpM, hpx⟩
  exact hT.2.2 <| Set.mem_iUnion.2 ⟨p,
    Set.mem_iUnion.2 ⟨hpM, Gamma.terminal_mem_support hpx⟩⟩

/-- The stage-relative version is the actual one-step pending set in the
source recursion.  A member which is already a fragment of `warpAt beta`
has the exact prefix certificate `IsStageInterval`; all other members are
scheduled immediately. -/
abbrev stageMaverickTerminals {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (beta : Ladder.Stage kappa) (T : Set Gamma.DPath) : Set V :=
  SliceSplice.stageMaverickTerminals Gamma L beta T

theorem stageMaverickTerminals_small
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      Gamma L Z alpha beta U T) :
    #(stageMaverickTerminals Gamma L beta T) < kappa :=
  (mk_terminalFrontier_le Gamma
    (ControlledSlices.sliceMavericks Gamma (L.warpAt beta) T)).trans_lt
      hT.2.2.1

theorem stageMaverickTerminals_subset_frontier
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      Gamma L Z alpha beta U T) :
    stageMaverickTerminals Gamma L beta T ⊆ L.frontier beta := by
  rintro x ⟨p, hpM, hpx⟩
  exact hT.1.1.1.1.1.terminalFrontier_subset ⟨p, hpM.1, hpx⟩

theorem stageMaverickTerminals_subset_closure
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      Gamma L Z alpha beta U T) :
    stageMaverickTerminals Gamma L beta T ⊆ Z := by
  rintro x ⟨p, hpM, hpx⟩
  exact hT.2.2.2 ⟨p, hpM, Gamma.terminal_mem_support hpx⟩

/-- If the current source thread ends at a requested frontier vertex, the
annular slice makes its starred image reach the original target.  In a
normalized web the target hit promised by `LinksToTarget` is necessarily
the terminal of the slice member. -/
theorem star_realizes_requested_terminal
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {W T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hNorm : Gamma.IsNormalized)
    (hT : ControlledSlices.SliceGood Gamma L T alpha beta U)
    (hcompat : Gamma.StarCompatible W T)
    {p : Gamma.DPath} (hpW : p ∈ W) {u : V}
    (hpu : Gamma.terminal? p = some u) (hu : u ∈ U)
    (huFrontier : u ∈ L.frontier alpha) :
    ∃ r ∈ Gamma.star hcompat,
      r.initial = p.initial ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? r = some b := by
  obtain ⟨q, hqT, f, hqf, hfpure, hfsuffix⟩ := hT.2 u hu
  subst q
  have huf : u ∈ f.support := by
    have huInter : u ∈ f.support ∩ U := by
      rw [hfpure]
      exact Set.mem_singleton u
    exact huInter.1
  have hqinitial :
      DirectedPath.Path.initial (Sum.inl f : Gamma.DPath) = u :=
    slice_meets_frontier_only_at_initial hT (Sum.inl f) hqT u
      huf huFrontier
  obtain ⟨_before, _after, hsupport, b, hbTarget, hbAfter⟩ := hfsuffix
  have hbf : b ∈ f.support := by
    change b ∈ f.walk.support
    rw [hsupport]
    exact List.mem_append_right _ hbAfter
  have hbfinish : b = f.finish :=
    hNorm.eq_finish_of_mem_walk f.walk hbf hbTarget
  rcases p with g | ray
  · have hgfinish : g.finish = u := Option.some.inj hpu
    let old : W := ⟨Sum.inl g, hpW⟩
    refine ⟨Gamma.starPath hcompat old, ⟨old, rfl⟩,
      Gamma.initial_starPath hcompat old, b, hbTarget, ?_⟩
    dsimp only [old]
    simp only [DWeb.starPath]
    split
    next hex =>
      let q' := Classical.choose hex
      have hq'T : q' ∈ T := (Classical.choose_spec hex).1
      have hq'start : q'.initial = g.finish :=
        (Classical.choose_spec hex).2
      have hqeq : q' = (Sum.inl f : Gamma.DPath) := by
        apply DWeb.IsWarp.eq_of_initial_eq Gamma hT.1.1 hq'T hqT
        exact hq'start.trans (hgfinish.trans hqinitial.symm)
      subst q'
      calc
        Gamma.terminal? (DirectedPath.Path.appendFinite g
            (Classical.choose hex) _ _) =
            (Classical.choose hex).terminal? :=
          DirectedPath.Path.terminal?_appendFinite g
            (Classical.choose hex) _ _
        _ = some b := by
          rw [hqeq]
          exact congrArg some hbfinish.symm
    next hnone =>
      exfalso
      apply hnone
      exact ⟨Sum.inl f, hqT, hqinitial.trans hgfinish.symm⟩
  · simp at hpu

/-! ## Tight annular source-star steps

The candidate table records its boundary condition under the name
`RightBoundaryTight`, while the recursive source-star lemmas call the same
condition `MeetsOnlyAtTerminal`.  The following two forgetful maps keep that
purely notational distinction out of the recursion. -/

theorem sourceTightAnnularSlice_of_candidate
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hT : SliceCandidate.IsTightAnnularSlice Gamma L T alpha beta U) :
    SliceSpliceSource.IsTightAnnularSlice Gamma L T alpha beta U := by
  refine ⟨hT.1, ?_⟩
  simpa only [SliceCandidate.RightBoundaryTight,
    SliceSpliceSource.MeetsOnlyAtTerminal] using hT.2

theorem sourceControlledSlice_of_candidate
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {T : Set Gamma.DPath}
    {Z U : Set V} {alpha beta : Ladder.Stage kappa}
    (hT : RegularCardinal.IsControlledSlice
      (SliceCandidate.IsTightAnnularSlice Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T) :
    RegularCardinal.IsControlledSlice
      (SliceSpliceSource.IsTightAnnularSlice Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T :=
  ⟨sourceTightAnnularSlice_of_candidate hT.1, hT.2⟩

/-! ## Exact ladder-prefix propagation

The ordinary branch of the limit argument is driven by a stronger
invariant than support containment.  An unfinished source path is exactly
an essential finite component of the accumulated ladder warp at the
current stage.  `IsStageInterval` then says that starring an ordinary
slice member onto it produces the corresponding component at the next
stage. -/

abbrev IsStagePrefix {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (alpha : Ladder.Stage kappa) (p : Gamma.DPath) : Prop :=
  SliceSplice.StagePrefix Gamma L alpha p

/-- One concrete starred thread either follows the exact accumulated
ladder prefix at `beta`, or its chosen slice member is one of the small
stage-relative mavericks whose terminal is scheduled at the next step. -/
theorem starPath_stagePrefix_or_maverickTerminal
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {W T : Set Gamma.DPath}
    (hL : SpliceLadderGeometry Gamma L)
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      Gamma L Z alpha beta U T)
    (hcompat : Gamma.StarCompatible W T)
    (p : W) (hpPrefix : IsStagePrefix Gamma L alpha p.1) :
    IsStagePrefix Gamma L beta (Gamma.starPath hcompat p) ∨
      ∃ x ∈ stageMaverickTerminals Gamma L beta T,
        Gamma.terminal? (Gamma.starPath hcompat p) = some x := by
  obtain ⟨fp, hpfp, hfpEssential, hfpFrontier⟩ := hpPrefix
  have hpW : (Sum.inl fp : Gamma.DPath) ∈ W := hpfp ▸ p.2
  have peq : p = ⟨Sum.inl fp, hpW⟩ := Subtype.ext hpfp
  subst p
  have hlinkT : IsLinkageBetween Gamma (L.frontier alpha)
      (L.frontier beta) T := hT.1.1.1.1.1
  have hmatch : ∃ q ∈ T, q.initial = fp.finish := by
    have hfinitial : fp.finish ∈ Gamma.initialSet T := by
      rw [hlinkT.initialSet_eq]
      exact hfpFrontier
    obtain ⟨q, hqT, hqinitial⟩ := hfinitial
    exact ⟨q, hqT, hqinitial⟩
  let q : Gamma.DPath := Classical.choose hmatch
  have hqT : q ∈ T := (Classical.choose_spec hmatch).1
  have hqstart : q.initial = fp.finish :=
    (Classical.choose_spec hmatch).2
  have hinter : fp.support ∩ q.support ⊆ {fp.finish} := by
    intro x hx
    have hx' := hcompat (.inl fp) hpW q hqT x hx.1 hx.2
    exact Set.mem_singleton_iff.mpr (Option.some.inj hx'.1).symm
  have hstar :
      Gamma.starPath hcompat (⟨Sum.inl fp, hpW⟩ : W) =
        DirectedPath.Path.appendFinite fp q hqstart hinter := by
    dsimp only [DWeb.starPath]
    split
    next hex =>
      let q' := Classical.choose hex
      have hq'T : q' ∈ T := (Classical.choose_spec hex).1
      have hq'start : q'.initial = fp.finish :=
        (Classical.choose_spec hex).2
      have hq'eq : q' = q :=
        DWeb.IsWarp.eq_of_initial_eq Gamma hlinkT.isWarp hq'T hqT
          (hq'start.trans hqstart.symm)
      dsimp only [q'] at hq'eq ⊢
    next hnone => exact (hnone hmatch).elim
  by_cases hqOrdinary :
      ControlledSlices.IsLadderFragment Gamma (L.warpAt beta) q
  · obtain ⟨left, right, segment, hqsegment, hleftEssential,
        hrightEssential, hleftFrontier, hrightFrontier,
        hsegmentStart, hsegmentInter, _hinterEq, happend⟩ :=
      hT.2.1 q hqT hqOrdinary
    have hfinish : fp.finish = left.finish := by
      exact hqstart.symm.trans (hqsegment ▸ hsegmentStart)
    have hfpLeftPath :
        (Sum.inl fp : Gamma.DPath) = Sum.inl left := by
      exact DWeb.IsWarp.eq_of_terminal_eq Gamma
        (hL.warpStages (Ladder.Stage.toExtended alpha)).essentialWarpPart
        hfpEssential hleftEssential rfl (congrArg some hfinish.symm)
    have hfpLeft : fp = left := Sum.inl.inj hfpLeftPath
    left
    refine ⟨right, ?_, hrightEssential, hrightFrontier⟩
    rw [hstar]
    subst left
    simpa only [hqsegment] using happend
  · right
    have hqMaverick : q ∈
        ControlledSlices.sliceMavericks Gamma (L.warpAt beta) T :=
      ⟨hqT, hqOrdinary⟩
    obtain ⟨fq, hqfinite⟩ := hlinkT.finiteCharacter hqT
    have hqterminal : Gamma.terminal? q = some fq.finish := by
      rw [hqfinite]
      rfl
    refine ⟨fq.finish, ⟨q, hqMaverick, hqterminal⟩, ?_⟩
    rw [hstar]
    exact (DirectedPath.Path.terminal?_appendFinite fp q
      hqstart hinter).trans hqterminal

/-- The zero-based tight annular slice gives the genuine initial partial
linkage of Assertion 9.11.  This is constructed from the legal ladder and
the controlled slice itself; no partial linkage is accepted as a premise. -/
theorem exists_initialTightLinkage_of_firstControlledSlice
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hNorm : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (hL : SpliceLadderGeometry Gamma L)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hT : RegularCardinal.IsControlledSlice
      (SliceCandidate.IsTightAnnularSlice Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z
      ⟨0, hL.regular.ord_pos⟩ beta U T) :
    ∃ W : Set Gamma.DPath,
      TightLinkageBetween Gamma (Gamma.source ∩ Z) (L.frontier beta) W ∧
        Gamma.vertexSet W ⊆ Z ∧
        Gamma.vertexSet W ⊆ Gamma.roof (L.frontier beta) := by
  let A : Set V := Gamma.source ∩ Z
  let W : Set Gamma.DPath := initialRestriction Gamma T A
  have hfirst : L.frontier ⟨0, hL.regular.ord_pos⟩ = Gamma.source :=
    frontier_zero_eq_source_of_initialStage hNorm hUnhindered
      hL.regular hL.initialStage
  have hsourceT := sourceTightAnnularSlice_of_candidate hT.1
  have hlinkT : TightLinkageBetween Gamma Gamma.source
      (L.frontier beta) T := by
    simpa only [hfirst] using
      (tightLinkageBetween_of_tightAnnularSlice hsourceT)
  have hlinkW : TightLinkageBetween Gamma A (L.frontier beta) W :=
    hlinkT.initialRestriction Set.inter_subset_left
  refine ⟨W, hlinkW, ?_, ?_⟩
  · apply vertexSet_initialRestriction_subset_of_controlledSlice
      hclosed Set.inter_subset_right
    exact SliceSplice.controlledSlice_of_annularControlledSlice
      ⟨hT.1.1, hT.2⟩
  · exact (vertexSet_initialRestriction_subset Gamma T A).trans
      (fun _ hx ↦ (hT.1.1.2 hx).2)

/-- A tight partial source--frontier linkage can be advanced across one
right-tight annular controlled slice.  All four invariants needed by the
transfinite recursion are proved here: tight linkage, forward extension,
closure in `Z`, and containment below the new frontier roof. -/
theorem tightAnnularSuccessor
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U A : Set V}
    {alpha beta : Ladder.Stage kappa} {W T : Set Gamma.DPath}
    (hNorm : Gamma.IsNormalized) (hL : SpliceLadderGeometry Gamma L)
    (hA : A ⊆ Gamma.source)
    (hab : alpha < beta)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hW : TightLinkageBetween Gamma A (L.frontier alpha) W)
    (hWZ : Gamma.vertexSet W ⊆ Z)
    (hWroof : Gamma.vertexSet W ⊆ Gamma.roof (L.frontier alpha))
    (hT : RegularCardinal.IsControlledSlice
      (SliceCandidate.IsTightAnnularSlice Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T) :
    let hcompat : Gamma.StarCompatible W T :=
      starCompatible_of_annular (hL.frontiersEssential alpha) hWroof hW.2
        hT.1.1
    TightLinkageBetween Gamma A (L.frontier beta) (Gamma.star hcompat) ∧
      Gamma.ForwardExtension W (Gamma.star hcompat) ∧
      Gamma.vertexSet (Gamma.star hcompat) ⊆ Z ∧
      Gamma.vertexSet (Gamma.star hcompat) ⊆
        Gamma.roof (L.frontier beta) := by
  let hcompat : Gamma.StarCompatible W T :=
    starCompatible_of_annular (hL.frontiersEssential alpha) hWroof hW.2
      hT.1.1
  have hWR : MeetsOnlyAtTerminal Gamma W (L.frontier beta) :=
    meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      (hL.frontiersEssential alpha) hWroof hW.2
      (hL.strictFrontierChronology hab)
  have hsourceT : TightLinkageBetween Gamma (L.frontier alpha)
      (L.frontier beta) T :=
    tightLinkageBetween_of_tightAnnularSlice
      (sourceTightAnnularSlice_of_candidate hT.1)
  dsimp only
  refine ⟨tightLinkageBetween_star hNorm hA hW hsourceT hWR hcompat,
    Gamma.forwardExtension_star hcompat, ?_, ?_⟩
  · exact vertexSet_star_subset_of_controlledSlice hclosed hWZ
      ⟨hT.1.1.1, hT.2⟩ hcompat
  · exact vertexSet_star_subset_roof hcompat (hL.frontierChronology hab)
      hWroof (fun _ hx ↦ (hT.1.1.2 hx).2)

/-! ## The direct-limit step

At a limit stage the genuinely graph-specific assertion is that every
thread meets the new frontier.  It is strictly weaker than postulating a
finite limit path or a linkage.  Once a thread contains such a point at
some finite stage, boundary tightness makes that point its terminal at all
later stages, which is precisely terminal cofinality. -/

/-- A target vertex roofed by a set must itself belong to that set: its
length-zero target path has no other possible meeting point. -/
theorem target_mem_of_mem_roof
    {Gamma : DWeb V} {S : Set V} {b : V}
    (hbTarget : b ∈ Gamma.target) (hbRoof : b ∈ Gamma.roof S) :
    b ∈ S := by
  let p : DirectedPath.FinitePath Gamma.graph :=
    { start := b
      finish := b
      walk := .nil
      isPath := DirectedPath.Walk.isPath_nil b }
  obtain ⟨x, hxp, hxS⟩ := hbRoof p ⟨rfl, hbTarget⟩
  have hxb : x = b := by
    have hsupport := Gamma.support_trivialPath b
    change p.support = ({b} : Set V) at hsupport
    rw [hsupport] at hxp
    exact Set.mem_singleton_iff.1 hxp
  exact hxb ▸ hxS

/-- A target point on one ladder frontier remains on every later
frontier.  Chronology gives roofing, and the preceding zero-path argument
upgrades roofing to literal frontier membership. -/
theorem target_frontier_persists
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} (hL : SpliceLadderGeometry Gamma L)
    {alpha beta : Ladder.Stage kappa} (hab : alpha < beta)
    {b : V} (hbTarget : b ∈ Gamma.target)
    (hb : b ∈ L.frontier alpha) :
    b ∈ L.frontier beta :=
  target_mem_of_mem_roof hbTarget (hL.frontierChronology hab hb)

/-- One target-ending member of a growing-warp thread already makes that
target terminal cofinal.  At a common later stage, warp uniqueness
identifies the extensions of the completed member and an arbitrary thread
member; normalization says that the common extension still terminates at
the target point. -/
theorem terminalCofinal_of_thread_member_target
    {I : Type v} [LinearOrder I]
    {Gamma : DWeb V} (hNorm : Gamma.IsNormalized)
    (C : Gamma.GrowingWarpChain I) (a : C.initialUnion)
    {i : I} {p : Gamma.DPath} (hpi : p ∈ C.stage i)
    (hpinitial : p.initial = a.1) {b : V}
    (hbTarget : b ∈ Gamma.target)
    (hpterm : Gamma.terminal? p = some b) :
    DirectedPath.Path.TerminalCofinal (C.thread Gamma a.1) b := by
  intro q hqThread
  obtain ⟨j, hqj, hqinitial⟩ := hqThread
  let k : I := max i j
  obtain ⟨p', hp'k, hpp'⟩ :=
    C.grows (show i ≤ k from le_max_left _ _) p hpi
  obtain ⟨q', hq'k, hqq'⟩ :=
    C.grows (show j ≤ k from le_max_right _ _) q hqj
  have hp'initial : p'.initial = a.1 :=
    (Gamma.extends_initial hpp').symm.trans hpinitial
  have hq'initial : q'.initial = a.1 :=
    (Gamma.extends_initial hqq').symm.trans hqinitial
  have hp'q' : p' = q' :=
    DWeb.IsWarp.eq_of_initial_eq Gamma (C.isWarp k) hp'k hq'k
      (hp'initial.trans hq'initial.symm)
  have hbp' : b ∈ p'.support :=
    Gamma.support_mono_of_extends hpp' (Gamma.terminal_mem_support hpterm)
  have hp'term : Gamma.terminal? p' = some b :=
    hNorm.terminal?_eq_of_mem_path p' hbp' hbTarget
  exact ⟨q', ⟨k, hq'k, hq'initial⟩, hqq', hp'q' ▸ hp'term⟩

/-- The easy half of the source limit dichotomy.  If a thread has already
reached the original target at an earlier stage, its terminal lies both on
the limiting frontier and in the support of the direct-limit thread. -/
theorem threadLimit_meets_frontier_of_completed
    {I : Type v} [LinearOrder I]
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {A : Set V}
    (hL : SpliceLadderGeometry Gamma L)
    (C : Gamma.GrowingWarpChain I)
    (stageIndex : I → Ladder.Stage kappa)
    (beta : Ladder.Stage kappa) (hindex : ∀ i, stageIndex i < beta)
    (htight : ∀ i,
      TightLinkageBetween Gamma A (L.frontier (stageIndex i)) (C.stage i))
    (a : C.initialUnion) {i : I} {p : Gamma.DPath}
    (hpi : p ∈ C.stage i) (hpinitial : p.initial = a.1)
    {b : V} (hbTarget : b ∈ Gamma.target)
    (hpterm : Gamma.terminal? p = some b) :
    (L.frontier beta ∩ (C.threadLimit Gamma a).support).Nonempty := by
  have hbOld : b ∈ L.frontier (stageIndex i) :=
    (htight i).1.terminalFrontier_subset ⟨p, hpi, hpterm⟩
  have hbBeta : b ∈ L.frontier beta :=
    target_frontier_persists hL (hindex i) hbTarget hbOld
  refine ⟨b, hbBeta, ?_⟩
  exact (C.mem_support_threadLimit_iff Gamma a b).2
    ⟨i, p, hpi, hpinitial, Gamma.terminal_mem_support hpterm⟩

theorem terminalCofinal_of_threadLimit_meets_boundary
    {I : Type v} [LinearOrder I]
    {Gamma : DWeb V} {R : Set V}
    (C : Gamma.GrowingWarpChain I)
    (hboundary : ∀ i, MeetsOnlyAtTerminal Gamma (C.stage i) R)
    (a : C.initialUnion) {x : V} (hxR : x ∈ R)
    (hx : x ∈ (C.threadLimit Gamma a).support) :
    DirectedPath.Path.TerminalCofinal (C.thread Gamma a.1) x := by
  obtain ⟨i, p, hpi, hpinitial, hxp⟩ :=
    (C.mem_support_threadLimit_iff Gamma a x).1 hx
  have hpThread : p ∈ C.thread Gamma a.1 := ⟨i, hpi, hpinitial⟩
  have hpterm : Gamma.terminal? p = some x :=
    hboundary i p hpi x hxp hxR
  intro q hqThread
  rcases eq_or_ne q p with rfl | hqp
  · exact ⟨q, hqThread, Gamma.extends_refl q, hpterm⟩
  · rcases C.thread_isChain Gamma a.1 hqThread hpThread hqp with
      hqpExt | hpqExt
    · exact ⟨p, hpThread, hqpExt, hpterm⟩
    · obtain ⟨j, hqj, _hqinitial⟩ := hqThread
      have hxq : x ∈ q.support := Gamma.support_mono_of_extends hpqExt hxp
      exact ⟨q, ⟨j, hqj, _hqinitial⟩, Gamma.extends_refl q,
        hboundary j q hqj x hxq hxR⟩

/-- A monotone family of closed hit stages also hits at its supremum.  This
is the order-theoretic invocation of source Lemma 7.28 used in the ordinary
thread branch. -/
theorem frontier_hit_at_lub_of_closed
    {I : Type v} [LinearOrder I] [Nonempty I]
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    (stageIndex : I → Ladder.Stage kappa) (beta : Ladder.Stage kappa)
    (hmono : Monotone stageIndex)
    (hLUB : IsLUB (Set.range stageIndex) beta)
    {y : Gamma.DPath}
    (hclosed : DirSupClosed (L.hitStages Sigma y))
    (hhit : ∀ i, stageIndex i ∈ L.hitStages Sigma y) :
    (L.frontier beta ∩ y.support).Nonempty := by
  let d : Set (Ladder.Stage kappa) := Set.range stageIndex
  have hd : d ⊆ L.hitStages Sigma y := by
    rintro _ ⟨i, rfl⟩
    exact hhit i
  have hdne : d.Nonempty := by
    let i : I := Classical.choice inferInstance
    exact ⟨stageIndex i, ⟨i, rfl⟩⟩
  have hddir : DirectedOn (· ≤ ·) d := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    refine ⟨stageIndex (max i j), ⟨max i j, rfl⟩, ?_, ?_⟩
    · exact hmono (le_max_left i j)
    · exact hmono (le_max_right i j)
  exact (hclosed hd hdne hddir hLUB).2

/-- A direct limit of earlier tight partial linkages is again a tight
partial linkage at the limiting frontier, provided every limit thread
actually meets that frontier.  The latter is the exact point at which the
ordinary/maverick dichotomy and source Lemma 7.28 enter the construction. -/
theorem tightAnnularLimit_of_threads_meet_frontier
    {I : Type v} [LinearOrder I] [Nonempty I]
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {A Z : Set V}
    (hNorm : Gamma.IsNormalized) (hL : SpliceLadderGeometry Gamma L)
    (hA : A ⊆ Gamma.source)
    (C : Gamma.GrowingWarpChain I)
    (stageIndex : I → Ladder.Stage kappa)
    (beta : Ladder.Stage kappa)
    (hindex : ∀ i, stageIndex i < beta)
    (htight : ∀ i,
      TightLinkageBetween Gamma A (L.frontier (stageIndex i)) (C.stage i))
    (hroof : ∀ i, Gamma.vertexSet (C.stage i) ⊆
      Gamma.roof (L.frontier (stageIndex i)))
    (hZ : ∀ i, Gamma.vertexSet (C.stage i) ⊆ Z)
    (hhit : ∀ a : C.initialUnion,
      (L.frontier beta ∩ (C.threadLimit Gamma a).support).Nonempty) :
    TightLinkageBetween Gamma A (L.frontier beta) (C.limitPaths Gamma) ∧
      Gamma.vertexSet (C.limitPaths Gamma) ⊆ Z ∧
      Gamma.vertexSet (C.limitPaths Gamma) ⊆
        Gamma.roof (L.frontier beta) ∧
      ∀ i, Gamma.ForwardExtension (C.stage i) (C.limitPaths Gamma) := by
  have hinitial : C.initialUnion = A := by
    apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
      rw [(htight i).1.initialSet_eq] at hxi
      exact hxi
    · intro x hx
      let i : I := Classical.choice inferInstance
      exact Set.mem_iUnion.2 ⟨i, (htight i).1.initialSet_eq.symm ▸ hx⟩
  have hboundary : ∀ i,
      MeetsOnlyAtTerminal Gamma (C.stage i) (L.frontier beta) := by
    intro i
    exact meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      (hL.frontiersEssential (stageIndex i)) (hroof i) (htight i).2
      (hL.strictFrontierChronology (hindex i))
  have hterminal : ∀ a : C.initialUnion,
      ∃ b ∈ L.frontier beta,
        DirectedPath.Path.TerminalCofinal (C.thread Gamma a.1) b := by
    intro a
    obtain ⟨x, hxR, hxlimit⟩ := hhit a
    exact ⟨x, hxR,
      terminalCofinal_of_threadLimit_meets_boundary C hboundary a hxR hxlimit⟩
  refine ⟨tightLinkageBetween_limitPaths_of_terminalCofinal C hNorm hA
      hinitial hterminal hboundary,
    vertexSet_limitPaths_subset_of_stages hZ, ?_, ?_⟩
  · rw [C.vertexSet_limitPaths Gamma]
    rintro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact Gamma.roof_cut (hL.frontierChronology (hindex i)) (hroof i hxi)
  · intro i
    constructor
    · exact C.grows_limitPaths Gamma i
    · intro q hq
      have hqA : q.initial ∈ A := by
        rw [← hinitial, ← C.initialSet_limitPaths Gamma]
        exact ⟨q, hq, rfl⟩
      have hqStageInitial : q.initial ∈ Gamma.initialSet (C.stage i) := by
        rw [(htight i).1.initialSet_eq]
        exact hqA
      obtain ⟨p, hp, hpinitial⟩ := hqStageInitial
      obtain ⟨r, hr, hpr⟩ := C.grows_limitPaths Gamma i p hp
      have hrq : r = q :=
        DWeb.IsWarp.eq_of_initial_eq Gamma (C.isWarp_limitPaths Gamma)
          hr hq ((Gamma.extends_initial hpr).symm.trans hpinitial)
      exact ⟨p, hp, hrq ▸ hpr⟩

/-! ## From local tight families to the executable splice operation

The preceding lemmas are the graph-theoretic base, successor, and limit
steps.  The remaining interface issue is proof-theoretic: the recursive
operation in `SliceSplice` must choose its payload before it is handed the
proof that the earlier payloads are valid.  We therefore package the
stage-local *data* separately from its conditional soundness theorem and
use classical choice only on that data.  No completed operation or global
splice chain occurs in the hypothesis below.

The small path lemma first records an important consequence of
normalization.  A path which already ends in the original target cannot be
properly extended.  This turns the forward-extension conclusions of the
successor and limit lemmas into the literal `preserves_completed` field of
`SliceSplice.IsValidStage`. -/

namespace LocalConstruction

private theorem Walk.eq_of_support_eq
    {D : Digraph V} {a b : V}
    (p q : DirectedPath.Walk D a b) (h : p.support = q.support) : p = q := by
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | @cons _ c _ e q =>
          simp only [DirectedPath.Walk.support_nil,
            DirectedPath.Walk.support_cons] at h
          have hlen := congrArg List.length h
          simp at hlen
  | @cons a c b e p ih =>
      cases q with
      | nil =>
          simp only [DirectedPath.Walk.support_cons,
            DirectedPath.Walk.support_nil] at h
          have hlen := congrArg List.length h
          simp at hlen
      | @cons _ d _ f q =>
          simp only [DirectedPath.Walk.support_cons] at h
          have htail : p.support = q.support := (List.cons.inj h).2
          have hhead := congrArg List.head? htail
          rw [List.head?_eq_some_head p.support_ne_nil, p.head_support,
            List.head?_eq_some_head q.support_ne_nil,
            q.head_support] at hhead
          have hcd : c = d := Option.some.inj hhead
          subst d
          have hpq : p = q := ih q htail
          subst q
          rfl

private theorem FinitePath.eq_of_prefix_of_finish_eq
    {D : Digraph V} {p q : DirectedPath.FinitePath D}
    (hpq : p.IsPrefixOf q) (hfinish : p.finish = q.finish) : p = q := by
  have hstart : p.start = q.start := hpq.start_eq
  cases p with
  | mk ps pf pw ppath =>
      cases q with
      | mk qs qf qw qpath =>
          dsimp at hstart hfinish hpq ⊢
          subst qs
          subst qf
          have hs : pw.support = qw.support :=
            DirectedPath.FinitePath.IsPrefixOf.eq_support_of_finish_eq hpq rfl
          have hw : pw = qw := Walk.eq_of_support_eq pw qw hs
          subst qw
          rfl

/-- A normalized target-ending path is fixed by every extension. -/
theorem eq_of_extends_of_terminal_mem_target
    {Gamma : DWeb V} (hNorm : Gamma.IsNormalized)
    {p q : Gamma.DPath} {b : V}
    (hpq : Gamma.Extends p q) (hpterm : Gamma.terminal? p = some b)
    (hb : b ∈ Gamma.target) : p = q := by
  have hbq : b ∈ q.support :=
    Gamma.support_mono_of_extends hpq (Gamma.terminal_mem_support hpterm)
  have hqterm : Gamma.terminal? q = some b :=
    hNorm.terminal?_eq_of_mem_path q hbq hb
  rcases p with p | r <;> rcases q with q | s
  · congr 1
    apply FinitePath.eq_of_prefix_of_finish_eq hpq
    exact Option.some.inj (hpterm.trans hqterm.symm)
  · simp at hqterm
  · exact hpq.elim
  · simp at hpterm

/-- A target-ending member of a tight partial source linkage already has
the endpoint-purity required by the final `A`--target linkage. -/
theorem targetPathPure_of_tightLinkage
    {Gamma : DWeb V} (hNorm : Gamma.IsNormalized)
    {A R : Set V} (hA : A ⊆ Gamma.source)
    {W : Set Gamma.DPath} (hW : TightLinkageBetween Gamma A R W)
    {p : Gamma.DPath} (hp : p ∈ W) {b : V}
    (hb : b ∈ Gamma.target) (hpterm : Gamma.terminal? p = some b) :
    IsPathBetween Gamma A Gamma.target p := by
  obtain ⟨q, rfl, _hends, hsource⟩ := hW.1.endpointPure p hp
  have hfinish : q.finish = b := Option.some.inj hpterm
  have hstartA : q.start ∈ A := by
    rw [← hW.1.initialSet_eq]
    exact ⟨Sum.inl q, hp, rfl⟩
  have hfinishTarget : q.finish ∈ Gamma.target := hfinish ▸ hb
  refine ⟨q, rfl, ?_, hsource⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxq, hxA | hxTarget⟩
    · have hxsingle : x ∈ ({q.start} : Set V) := by
        rw [← hsource]
        exact ⟨hxq, hxA⟩
      exact Set.mem_insert_iff.2 <| Or.inl (Set.mem_singleton_iff.1 hxsingle)
    · have hxterm :=
        hNorm.terminal?_eq_of_mem_path (Sum.inl q) hxq hxTarget
      exact Set.mem_insert_iff.2 <| Or.inr <|
        Set.mem_singleton_iff.2 (Option.some.inj hxterm).symm
  · rintro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx
    · exact ⟨q.start_mem_support, Or.inl hstartA⟩
    · have hxf : x = q.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.finish_mem_support, Or.inr hfinishTarget⟩

/-- The concrete data chosen at one recursive stage.  It consists of the
club coordinate, the small scheduled set, an actual right-tight annular
controlled slice, and the partial family produced from earlier families.
Its controlled-slice field is precisely the upstream existence assertion;
it contains neither an operation nor a global recursion. -/
structure TightStageData {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (Sigma : Set (Ladder.Stage kappa)) (Z : Set V) where
  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  scheduled : Set V
  scheduled_subset : scheduled ⊆ L.frontier stageIndex ∩ Z
  scheduled_small : #scheduled < kappa
  nextIndex : Ladder.Stage kappa
  next_mem : nextIndex ∈ Sigma
  index_lt_next : stageIndex < nextIndex
  slice : Set Gamma.DPath
  sliceControlled : SliceCandidate.IsTrackedTightAnnularControlledSlice
    Gamma L Z stageIndex nextIndex scheduled slice
  family : Set Gamma.DPath

namespace TightStageData

variable {kappa : Cardinal.{u}} {Gamma : DWeb V}
variable {L : Gamma.KappaLadder kappa}
variable {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
variable {request : Ladder.Stage kappa → Option A}

/-- Forget the right-tight annular refinements when installing a stage in
the generic splice recursion. -/
noncomputable def payload
    (D : TightStageData Gamma L Sigma Z) :
    SliceSplice.StagePayload Gamma L Sigma Z where
  stageIndex := D.stageIndex
  stageIndex_mem := D.stageIndex_mem
  scheduled := D.scheduled
  scheduled_subset := D.scheduled_subset
  scheduled_small := D.scheduled_small
  nextIndex := D.nextIndex
  next_mem := D.next_mem
  index_lt_next := D.index_lt_next
  slice := D.slice
  sliceControlled :=
    SliceSplice.controlledSlice_of_annularControlledSlice
      ⟨D.sliceControlled.1.1.1, D.sliceControlled.1.2⟩
  stageMavericks_small := D.sliceControlled.2.2.1
  stageMavericks_closed := D.sliceControlled.2.2.2
  family := D.family

/-- Soundness conditions on the partial family produced by one piece of
stage data.  These are exactly what the base/successor/limit lemmas prove:
a tight partial linkage, closure, forward extension of every earlier
family, and realization of the source scheduled at this recursion index. -/
def IsSound (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z)
    (D : TightStageData Gamma L Sigma Z) : Prop :=
  TightLinkageBetween Gamma A (L.frontier D.nextIndex) D.family ∧
    Gamma.vertexSet D.family ⊆ Z ∧
    Gamma.vertexSet D.family ⊆ Gamma.roof (L.frontier D.nextIndex) ∧
    (∀ j (hji : j < i),
      (previous j hji).nextIndex ≤ D.stageIndex) ∧
    (∀ p ∈ D.family,
      (∃ b ∈ Gamma.target, Gamma.terminal? p = some b) ∨
        SliceSplice.StagePrefix Gamma L D.nextIndex p ∨
        ∃ x ∈ stageMaverickTerminals Gamma L D.nextIndex D.slice,
          Gamma.terminal? p = some x) ∧
    (∀ j (hji : j < i),
      Gamma.ForwardExtension (previous j hji).family D.family) ∧
    (∀ j (hji : j < i), ∀ p ∈ (previous j hji).family,
      (∃ x ∈ (previous j hji).pendingTerminals,
        Gamma.terminal? p = some x) →
      ∃ q ∈ D.family, Gamma.Extends p q ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? q = some b) ∧
    ∀ a : A, request i = some a →
      ∃ p ∈ D.family, p.initial = a.1 ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? p = some b

/-- Tight stage soundness implies every law expected by
`SliceSplice.IsValidStage`.  In particular, preservation of a completed
path is derived rather than included as an extra stage hypothesis. -/
theorem validStage_of_isSound
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z}
    (D : TightStageData Gamma L Sigma Z)
    (hD : D.IsSound (A := A) (request := request) hNorm hA i previous) :
    SliceSplice.IsValidStage request i previous D.payload := by
  rcases hD with
    ⟨hlink, hclosed, hroof, hindices, hstatus, hextends,
      hresolves, hrequest⟩
  refine {
    linkage := hlink.1
    meets_frontier_only_at_terminal := hlink.2
    vertices_roof := hroof
    isWarp := hlink.1.isWarp
    initial_subset := ?_
    vertices_closed := hclosed
    targetPathPure := ?_
    previous_index_le := hindices
    path_status := hstatus
    extends_previous := ?_
    preserves_completed := ?_
    resolves_previous_pending := hresolves
    realizes_request := hrequest }
  · change Gamma.initialSet D.family ⊆ A
    rw [hlink.1.initialSet_eq]
  · intro p hp b hb hpterm
    exact targetPathPure_of_tightLinkage hNorm hA hlink hp hb hpterm
  · intro j hji
    exact (hextends j hji).1
  · intro j hji p hp ⟨b, hb, hpterm⟩
    obtain ⟨q, hq, hpq⟩ := (hextends j hji).1 p hp
    have hpqeq : p = q :=
      eq_of_extends_of_terminal_mem_target hNorm hpq hpterm hb
    exact hpqeq.symm ▸ hq

/-- For linkages with the same initial set, the one-sided extension law is
already a full forward extension.  The reverse matching is forced by
initial-set coverage and uniqueness in the later warp. -/
theorem forwardExtension_of_linkages
    {Gamma : DWeb V} {A R S : Set V}
    {W W' : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A R W)
    (hW' : IsLinkageBetween Gamma A S W')
    (hext : ∀ p ∈ W, ∃ q ∈ W', Gamma.Extends p q) :
    Gamma.ForwardExtension W W' := by
  refine ⟨hext, ?_⟩
  intro q hq
  have hqA : q.initial ∈ A := by
    rw [← hW'.initialSet_eq]
    exact ⟨q, hq, rfl⟩
  have hqOld : q.initial ∈ Gamma.initialSet W := by
    rw [hW.initialSet_eq]
    exact hqA
  obtain ⟨p, hp, hpinitial⟩ := hqOld
  obtain ⟨r, hr, hpr⟩ := hext p hp
  have hrq : r = q :=
    DWeb.IsWarp.eq_of_initial_eq Gamma hW'.isWarp hr hq
      ((Gamma.extends_initial hpr).symm.trans hpinitial)
  exact ⟨p, hp, hrq ▸ hpr⟩

/-- The concrete successor-stage constructor.  The scheduler supplies a
small set `U` of old terminals, together with the fact that it contains a
terminal on the thread requested at this recursion index.  A tracked
annular controlled slice then gives sound stage data by source star. -/
theorem exists_sound_successorData
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized) (hL : SpliceLadderGeometry Gamma L)
    (hA : A ⊆ Gamma.source)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    {i j : Ladder.Stage kappa} (hji : j < i)
    {previous : ∀ l : Ladder.Stage kappa, l < i →
      SliceSplice.StagePayload Gamma L Sigma Z}
    (hprevious : ∀ l (hli : l < i),
      SliceSplice.IsValidStage request l
        (fun m hml ↦ previous m (lt_trans hml hli))
        (previous l hli))
    (hmax : ∀ l (hli : l < i), l ≤ j)
    {U : Set V}
    (hUsub : U ⊆ L.frontier (previous j hji).nextIndex ∩ Z)
    (hUsmall : #U < kappa)
    {beta : Ladder.Stage kappa} (hbeta : beta ∈ Sigma)
    (hab : (previous j hji).nextIndex < beta)
    {T : Set Gamma.DPath}
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      Gamma L Z (previous j hji).nextIndex beta U T)
    (hPendingSub : (previous j hji).pendingTerminals ⊆ U)
    (hrequestOld : ∀ a : A, request i = some a →
      ∃ p ∈ (previous j hji).family, p.initial = a.1 ∧
        ∃ u ∈ U, Gamma.terminal? p = some u) :
    ∃ D : TightStageData Gamma L Sigma Z,
      D.IsSound (A := A) (request := request) hNorm hA i previous := by
  let P := previous j hji
  have hP := hprevious j hji
  have hPtight : TightLinkageBetween Gamma A
      (L.frontier P.nextIndex) P.family :=
    ⟨hP.linkage, hP.meets_frontier_only_at_terminal⟩
  let hcompat : Gamma.StarCompatible P.family T :=
    starCompatible_of_annular (hL.frontiersEssential P.nextIndex)
      hP.vertices_roof hPtight.2 hT.1.1.1
  let W : Set Gamma.DPath := Gamma.star hcompat
  have hstep :
      TightLinkageBetween Gamma A (L.frontier beta) W ∧
        Gamma.ForwardExtension P.family W ∧
        Gamma.vertexSet W ⊆ Z ∧
        Gamma.vertexSet W ⊆ Gamma.roof (L.frontier beta) := by
    simpa only [P, hcompat, W] using
      (tightAnnularSuccessor hNorm hL hA hab hclosed hPtight
        hP.vertices_closed hP.vertices_roof hT.1)
  let D : TightStageData Gamma L Sigma Z := {
    stageIndex := P.nextIndex
    stageIndex_mem := P.next_mem
    scheduled := U
    scheduled_subset := hUsub
    scheduled_small := hUsmall
    nextIndex := beta
    next_mem := hbeta
    index_lt_next := hab
    slice := T
    sliceControlled := hT
    family := W }
  refine ⟨D, ?_⟩
  change TightLinkageBetween Gamma A (L.frontier beta) W ∧
    Gamma.vertexSet W ⊆ Z ∧
    Gamma.vertexSet W ⊆ Gamma.roof (L.frontier beta) ∧
    (∀ l (hli : l < i), (previous l hli).nextIndex ≤ P.nextIndex) ∧
    (∀ r ∈ W,
      (∃ b ∈ Gamma.target, Gamma.terminal? r = some b) ∨
        IsStagePrefix Gamma L beta r ∨
        ∃ x ∈ stageMaverickTerminals Gamma L beta T,
          Gamma.terminal? r = some x) ∧
    (∀ l (hli : l < i),
      Gamma.ForwardExtension (previous l hli).family W) ∧
    (∀ l (hli : l < i), ∀ p ∈ (previous l hli).family,
      (∃ x ∈ (previous l hli).pendingTerminals,
        Gamma.terminal? p = some x) →
      ∃ q ∈ W, Gamma.Extends p q ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? q = some b) ∧
    ∀ a : A, request i = some a →
      ∃ p ∈ W, p.initial = a.1 ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? p = some b
  refine ⟨hstep.1, hstep.2.2.1, hstep.2.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hli
    rcases (hmax l hli).lt_or_eq with hlj | hlj
    · exact (hP.previous_index_le l hlj).trans P.index_lt_next.le
    · subst l
      exact le_rfl
  · intro r hr
    obtain ⟨p, rfl⟩ := hr
    rcases hP.path_status p p.2 with hcompleted | hprefix | hpending
    · left
      obtain ⟨b, hbTarget, hpterm⟩ := hcompleted
      have hpeq : p.1 = Gamma.starPath hcompat p :=
        eq_of_extends_of_terminal_mem_target hNorm
          (Gamma.extends_starPath hcompat p) hpterm hbTarget
      exact ⟨b, hbTarget, hpeq ▸ hpterm⟩
    · rcases starPath_stagePrefix_or_maverickTerminal hL hT hcompat p
        hprefix with hnewPrefix | hnewPending
      · exact Or.inr (Or.inl hnewPrefix)
      · exact Or.inr (Or.inr hnewPending)
    · obtain ⟨x, hxPending, hpterm⟩ := hpending
      obtain ⟨r, hr, hrinitial, b, hbTarget, hrterm⟩ :=
        star_realizes_requested_terminal hNorm hT.1.1.1.1 hcompat p.2
          hpterm (hPendingSub hxPending)
          (hPtight.1.terminalFrontier_subset ⟨p.1, p.2, hpterm⟩)
      have heq : Gamma.starPath hcompat p = r :=
        DWeb.IsWarp.eq_of_initial_eq Gamma hstep.1.1.isWarp
          ⟨p, rfl⟩ hr ((Gamma.initial_starPath hcompat p).trans hrinitial.symm)
      exact Or.inl ⟨b, hbTarget, heq ▸ hrterm⟩
  · intro l hli
    have hlP : Gamma.ForwardExtension (previous l hli).family P.family := by
      rcases (hmax l hli).lt_or_eq with hlj | hlj
      · exact forwardExtension_of_linkages
          (hprevious l hli).linkage hP.linkage
          (hP.extends_previous l hlj)
      · subst l
        exact Gamma.forwardExtension_refl P.family
    exact Gamma.forwardExtension_trans hlP hstep.2.1
  · intro l hli p hp hpending
    rcases (hmax l hli).lt_or_eq with hlj | hlj
    · obtain ⟨q, hqP, hpq, b, hbTarget, hqterm⟩ :=
        hP.resolves_previous_pending l hlj p hp hpending
      let qs : P.family := ⟨q, hqP⟩
      have hqeq : q = Gamma.starPath hcompat qs :=
        eq_of_extends_of_terminal_mem_target hNorm
          (Gamma.extends_starPath hcompat qs) hqterm hbTarget
      refine ⟨q, ?_, hpq, b, hbTarget, hqterm⟩
      exact hqeq.symm ▸ (show Gamma.starPath hcompat qs ∈ W from ⟨qs, rfl⟩)
    · subst l
      obtain ⟨x, hxPending, hpterm⟩ := hpending
      obtain ⟨q, hqW, hqinitial, b, hbTarget, hqterm⟩ :=
        star_realizes_requested_terminal hNorm hT.1.1.1.1 hcompat hp
          hpterm (hPendingSub hxPending)
          (hPtight.1.terminalFrontier_subset ⟨p, hp, hpterm⟩)
      let ps : P.family := ⟨p, hp⟩
      have hstarq : Gamma.starPath hcompat ps = q :=
        DWeb.IsWarp.eq_of_initial_eq Gamma hstep.1.1.isWarp
          ⟨ps, rfl⟩ hqW ((Gamma.initial_starPath hcompat ps).trans hqinitial.symm)
      exact ⟨q, hqW, (hstarq ▸ Gamma.extends_starPath hcompat ps),
        b, hbTarget, hqterm⟩
  · intro a ha
    obtain ⟨p, hp, hpinitial, u, hu, hpterm⟩ := hrequestOld a ha
    obtain ⟨r, hr, hrinitial, b, hb, hrterm⟩ :=
      star_realizes_requested_terminal hNorm hT.1.1.1.1 hcompat hp
        hpterm hu (hUsub hu).1
    exact ⟨r, hr, hrinitial.trans hpinitial, b, hb, hrterm⟩

end TightStageData

/-- The genuinely local hypothesis left after the graph-theoretic
constructor lemmas: for each history, choose concrete stage data whose
family is sound whenever that history is sound.  Crucially, the chosen
object is only one controlled slice and one family, not a recursive
operation or a completed chain. -/
def HasTightStageData {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (Sigma : Set (Ladder.Stage kappa)) (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source) : Prop :=
  ∀ (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z),
    ∃ D : TightStageData Gamma L Sigma Z,
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
        D.IsSound (A := A) (request := request) hNorm hA i previous

/-- Tracked controlled slices supply unconditional dummy stage data.  The
family is irrelevant on an invalid history; its sole purpose is to let the
operation choose its data before receiving the proof that the history is
valid. -/
theorem exists_tightStageData_of_trackedSlices
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (hkappa : kappa.IsRegular)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma L Sigma Z) :
    Nonempty (TightStageData Gamma L Sigma Z) := by
  let zero : Ladder.Stage kappa := ⟨0,
    (Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hkappa.aleph0_le))⟩
  let alpha := RegularCardinal.nextInClub hkappa Sigma hSigma zero
  have halpha : alpha ∈ Sigma :=
    RegularCardinal.nextInClub_mem hkappa Sigma hSigma zero
  have hemptySub : (∅ : Set V) ⊆ L.frontier alpha ∩ Z :=
    Set.empty_subset _
  have hemptySmall : #(∅ : Set V) < kappa := by
    rw [Cardinal.mk_emptyCollection]
    exact Cardinal.aleph0_pos.trans_le hkappa.aleph0_le
  obtain ⟨beta, hbeta, hab, T, hT⟩ :=
    hslices alpha halpha ∅ hemptySub hemptySmall
  exact ⟨{
    stageIndex := alpha
    stageIndex_mem := halpha
    scheduled := ∅
    scheduled_subset := hemptySub
    scheduled_small := hemptySmall
    nextIndex := beta
    next_mem := hbeta
    index_lt_next := hab
    slice := T
    sliceControlled := hT
    family := ∅ }⟩

/-- Assemble `HasTightStageData` from the mathematically natural positive
existence theorem.  Invalid histories use the dummy tracked slice above;
valid histories use the supplied base/successor/limit construction. -/
theorem hasTightStageData_of_sound_exists
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    (hkappa : kappa.IsRegular)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma L Sigma Z)
    (hsound : ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z),
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm hA i previous) :
    HasTightStageData Gamma L Sigma Z A request hNorm hA := by
  let fallback : TightStageData Gamma L Sigma Z :=
    Classical.choice
      (exists_tightStageData_of_trackedSlices hkappa hSigma hslices)
  intro i previous
  by_cases hprevious : ∀ j (hji : j < i),
      SliceSplice.IsValidStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)
  · obtain ⟨D, hD⟩ := hsound i previous hprevious
    exact ⟨D, fun _ ↦ hD⟩
  · exact ⟨fallback, fun h ↦ (hprevious h).elim⟩

/-! ### Dispatching the local construction by the stage ordinal

The mathematical construction has three genuinely different local steps:
the first stage, a successor stage with a last earlier payload, and a
nonzero limit stage.  `hasTightStageData_of_sound_exists` deliberately
forgets that distinction, since its consumer only needs one sound-stage
theorem.  The following dispatcher restores the source-faithful interface:
the three compilers receive exactly the same valid history, while the
successor compiler additionally receives the actual predecessor as a
`Ladder.Stage` and the limit compiler receives the ordinal limit proof.

The tracked-slice hypothesis is used only through the existing assembler:
it provides the unconditional fallback data needed on an invalid history.
Thus none of the three positive compilers is asked to construct dummy data,
and no recursive splice operation is hidden in their hypotheses. -/

/-- Assemble tight stage data from separate zero, successor, and limit
sound-stage compilers.  This is the proof-theoretic base/successor/limit
case split used by the regular source recursion. -/
theorem hasTightStageData_of_stageCaseCompilers
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    (hkappa : kappa.IsRegular)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma L Sigma Z)
    (hzero : ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z),
      i.1 = 0 →
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm hA i previous)
    (hsucc : ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z)
      (j : Ladder.Stage kappa) (hji : j < i),
      Order.succ j.1 = i.1 →
      (∀ l (hli : l < i),
        SliceSplice.IsValidStage request l
          (fun m hml ↦ previous m (lt_trans hml hli))
          (previous l hli)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm hA i previous)
    (hlimit : ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z),
      Order.IsSuccLimit i.1 →
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm hA i previous) :
    HasTightStageData Gamma L Sigma Z A request hNorm hA := by
  apply hasTightStageData_of_sound_exists hNorm hA hkappa hSigma hslices
  intro i previous hprevious
  rcases Ordinal.zero_or_succ_or_isSuccLimit i.1 with
      hi | ⟨j, hj⟩ | hi
  · exact hzero i previous hi hprevious
  · have hjiValue : j < i.1 := by
      rw [← hj]
      exact Order.lt_succ j
    let j' : Ladder.Stage kappa :=
      ⟨j, hjiValue.trans i.2⟩
    have hji : j' < i := hjiValue
    exact hsucc i previous j' hji hj hprevious
  · exact hlimit i previous hi hprevious

/-- Classical choice turns the local base/successor/limit data into the
executable well-founded splice operation. -/
noncomputable def localSpliceOperation_of_tightStageData
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    (hstage : HasTightStageData Gamma L Sigma Z A request hNorm hA) :
    SliceSplice.LocalSpliceOperation Gamma L Sigma Z A request where
  build i previous :=
    (Classical.choose (hstage i previous)).payload
  valid i previous hprevious := by
    let D : TightStageData Gamma L Sigma Z :=
      Classical.choose (hstage i previous)
    have hD : D.IsSound (A := A) (request := request) hNorm hA i previous :=
      Classical.choose_spec (hstage i previous) hprevious
    exact D.validStage_of_isSound hNorm hA hD

/-- Direct constructor form of Assertion 9.11 with no
`LocalSpliceOperation` premise.  The only recursive input is the local
controlled-slice/family existence predicate above. -/
theorem exists_internal_linkage_of_tightStageData
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    (hstage : HasTightStageData Gamma L Sigma Z A request hNorm hA)
    (hkappa : kappa.IsRegular)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hrequest : ∀ a : A, ∃ i, request i = some a) :
    ∃ P : Set Gamma.DPath,
      IsLinkageBetween Gamma A Gamma.target P ∧
        Gamma.vertexSet P ⊆ Z := by
  exact SliceSplice.LocalSpliceOperation.exists_internal_linkage_of_localSpliceOperation
    (localSpliceOperation_of_tightStageData hNorm hA hstage)
    hkappa hSigma hrequest

end LocalConstruction


end SliceSpliceConstructor
end CardinalInduction
end Erdos599
