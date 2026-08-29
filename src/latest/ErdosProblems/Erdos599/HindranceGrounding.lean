/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Ladder
import ErdosProblems.Erdos599.LadderFrontierInvariants
import ErdosProblems.Erdos599.InfiniteKonig
import ErdosProblems.Erdos599.Popular
import ErdosProblems.Erdos599.PopularAuxiliary
import ErdosProblems.Erdos599.PopularLayers
import ErdosProblems.Erdos599.PopularSwitching

/-!
# Grounding a stationary ladder obstruction

This file develops the concrete interfaces used by the grounding argument
in Sections 7--8 of Aharoni--Berger.

The elementary lemma below is the final step of that argument.  Once the
grounding construction has produced a genuine wave with an inessential
member, essential trimming retains the same terminal frontier but omits the
initial vertex of that member.  The trimmed wave is therefore a hindrance.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-! ## The auxiliary-web input attached to a legal obstruction -/

/-- Infinite paths selected at grounded obstruction stages.  These paths,
rather than the ordinal stages themselves, index the fresh proxies.  This
keeps the proxy type in the vertex universe; the unique selecting stage is
recovered below from bookkeeping. -/
abbrev KappaLadder.groundedInfiniteRecords
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa) :=
  {p : Gamma.DPath // ∃ a : Ladder.Stage kappa,
    a ∈ L.phiGround ∩ L.phiInfinite ∧ L.chosen a = some p}

/-- Terminals of the finite records selected at grounded obstruction
stages.  This is the source set `X_fin` used in Section 8: a finite record
is represented in the grounding auxiliary only when its initial vertex is
in the original source. -/
def KappaLadder.groundedFiniteTerminalSet
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa) : Set V :=
  {x | ∃ a : Ladder.Stage kappa, a ∈ L.phiGround ∩ L.phiFinite ∧
    ∃ p : Gamma.DPath,
      L.chosen a = some p ∧ Gamma.terminal? p = some x}

/-- Forgetting groundedness gives an ordinary recorded finite terminal. -/
theorem KappaLadder.groundedFiniteTerminalSet_subset_finiteTerminalSet
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa) :
    L.groundedFiniteTerminalSet ⊆ L.finiteTerminalSet := by
  rintro x ⟨a, ha, p, hchosen, hterminal⟩
  exact ⟨a, ha.2, p, hchosen, hterminal⟩

/-- The troublesome ray represented by a grounded infinite proxy. -/
noncomputable def KappaLadder.groundedInfinitePath
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (_hlegal : L.IsLegal) (p : L.groundedInfiniteRecords) : Gamma.DPath :=
  p.1

/-- Ray priority guarantees that every grounded infinite proxy really
represents a ray, rather than a finite path with an omitted terminal. -/
theorem KappaLadder.groundedInfinitePath_isRay
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) (p : L.groundedInfiniteRecords) :
    ∃ r : DirectedPath.Ray Gamma.graph,
      L.groundedInfinitePath hlegal p = .inr r := by
  obtain ⟨a, ha, hchosen⟩ := p.2
  obtain ⟨q, hq, hqRay⟩ :=
    L.bookkeeping.chosen_isRay_of_mem_phiInfinite
      hlegal.validBookkeeping ha.2
  have hpq : p.1 = q := Option.some.inj (hchosen.symm.trans hq)
  have hpath : L.groundedInfinitePath hlegal p = q := by
    simpa only [KappaLadder.groundedInfinitePath] using hpq
  rw [hpath]
  rcases q with q | r
  · change (some q.finish : Option V) = none at hqRay
    cases hqRay
  · exact ⟨r, rfl⟩

/-- The literal `Theta`/`Lambda` input determined by a legal ladder.  Its
finite sources are the grounded recorded finite terminals; its fresh proxy
sources are exactly the grounded recorded rays; and its target markers are
supplied by the ladder chronology. -/
noncomputable def KappaLadder.popularAuxiliaryInput
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) :
    PopularAuxiliary.Input Gamma L.groundedInfiniteRecords where
  ladder :=
    ⟨L.limitWarp, hlegal.warpStages (Ladder.finalStage kappa)⟩
  finiteSource := L.groundedFiniteTerminalSet
  markerSet := L.markerSet
  proxyPath := L.groundedInfinitePath hlegal
  proxy_isRay := L.groundedInfinitePath_isRay hlegal

/-- The unique obstruction stage represented by a recorded finite
terminal.  Existence is part of `finiteTerminalSet`; uniqueness follows
from persistence and warp disjointness. -/
noncomputable def KappaLadder.finiteTerminalStage
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (x : L.finiteTerminalSet) : Ladder.Stage kappa :=
  Classical.choose x.2

theorem KappaLadder.finiteTerminalStage_spec
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (x : L.finiteTerminalSet) :
    L.finiteTerminalStage x ∈ L.phiFinite ∧
      ∃ p : Gamma.DPath,
        L.chosen (L.finiteTerminalStage x) = some p ∧
          Gamma.terminal? p = some x.1 :=
  Classical.choose_spec x.2

theorem KappaLadder.finiteTerminalStage_eq
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) {a : Ladder.Stage kappa} {p : Gamma.DPath}
    {x : V} (hchosen : L.chosen a = some p)
    (hterminal : Gamma.terminal? p = some x)
    (hx : x ∈ L.finiteTerminalSet) :
    L.finiteTerminalStage ⟨x, hx⟩ = a := by
  obtain ⟨_, q, hq, hqterminal⟩ := L.finiteTerminalStage_spec ⟨x, hx⟩
  exact hlegal.recordedStage_eq_of_same_terminal
    hq hqterminal hchosen hterminal

/-- The finite-record stage map is injective on all recorded finite
terminals. -/
theorem KappaLadder.finiteTerminalStage_injective
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa) :
    Function.Injective L.finiteTerminalStage := by
  intro x y hxy
  obtain ⟨_, p, hp, hpx⟩ := L.finiteTerminalStage_spec x
  obtain ⟨_, q, hq, hqy⟩ := L.finiteTerminalStage_spec y
  have hpq : p = q := by
    apply Option.some.inj
    exact hp.symm.trans ((congrArg L.chosen hxy).trans hq)
  apply Subtype.ext
  exact Option.some.inj (hpx.symm.trans (hpq ▸ hqy))

/-- The stage-valued index of a grounded finite source of the auxiliary
web. -/
noncomputable def KappaLadder.finiteTerminalIndex
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa) :
    L.groundedFiniteTerminalSet → Stationary.Below kappa :=
  fun x ↦ L.finiteTerminalStage
    ⟨x.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2⟩

/-- The index of a grounded finite terminal is itself a grounded
obstruction stage. -/
theorem KappaLadder.finiteTerminalStage_mem_phiGround
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) (x : L.groundedFiniteTerminalSet) :
    L.finiteTerminalIndex x ∈ L.phiGround := by
  obtain ⟨a, ha, p, hchosen, hterminal⟩ := x.2
  have hstage :
      L.finiteTerminalStage
          ⟨x.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2⟩ = a :=
    L.finiteTerminalStage_eq hlegal hchosen hterminal
      (L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2)
  simpa only [KappaLadder.finiteTerminalIndex, hstage] using ha.1

theorem KappaLadder.finiteTerminalIndex_injective
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa) :
    Function.Injective L.finiteTerminalIndex := by
  intro x y hxy
  apply Subtype.ext
  have hxy' :
      (⟨x.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2⟩ :
        L.finiteTerminalSet) =
      ⟨y.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet y.2⟩ :=
    L.finiteTerminalStage_injective hxy
  exact congrArg (fun z : L.finiteTerminalSet ↦ z.1) hxy'

/-- Recover the unique stage at which an infinite proxy path was selected. -/
noncomputable def KappaLadder.groundedInfiniteStage
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa) :
    L.groundedInfiniteRecords → Ladder.Stage kappa :=
  fun p ↦ Classical.choose p.2

theorem KappaLadder.groundedInfiniteStage_spec
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (p : L.groundedInfiniteRecords) :
    L.groundedInfiniteStage p ∈ L.phiGround ∩ L.phiInfinite ∧
      L.chosen (L.groundedInfiniteStage p) = some p.1 :=
  Classical.choose_spec p.2

theorem KappaLadder.groundedInfiniteStage_eq
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) (p : L.groundedInfiniteRecords)
    {a : Ladder.Stage kappa} (ha : L.chosen a = some p.1) :
    L.groundedInfiniteStage p = a := by
  exact L.bookkeeping.chosen_stage_unique hlegal.validBookkeeping
    (L.groundedInfiniteStage_spec p).2 ha

/-- A fresh marker born at stage `a` lies outside the roof of that stage's
frontier.  This is the endpoint half of the chronology argument in source
Lemma 7.17: marker eligibility puts the vertex outside the quotient source
and outside the old strict roof, while the frontier is the essential old
terminal frontier. -/
theorem KappaLadder.marker_not_mem_roof_frontier
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) {a : Ladder.Stage kappa} {y : V}
    (hy : L.marker a = some y) :
    y ∉ Gamma.roof (L.frontier a) := by
  have hyCandidate : y ∈ L.markerCandidates a :=
    (hlegal.freshMarkers.2 a y hy).1
  have hyNotFrontier : y ∉ L.frontier a := by
    intro hyFrontier
    exact hyCandidate.2 (Or.inl hyFrontier)
  have hyNotStrictOld :
      y ∉ Gamma.strictRoof (Gamma.terminalFrontier (L.warpAt a)) :=
    by
      have hyQuotient : y ∈ Gamma.quotientVertexSet
          (Gamma.terminalFrontier (L.warpAt a)) := hyCandidate.1.2
      exact hyQuotient
  intro hyRoof
  have hyNotEssential : y ∉ Gamma.essential (L.frontier a) := by
    rw [hlegal.frontiersEssential a]
    exact hyNotFrontier
  have hyStrict : y ∈ Gamma.strictRoof (L.frontier a) :=
    ⟨hyRoof, hyNotEssential⟩
  apply hyNotStrictOld
  rw [L.frontier_eq_essential_terminalFrontier
    hlegal.roofsSourceAtStages a, Gamma.strictRoof_essential] at hyStrict
  exact hyStrict

/-- The index of an infinite proxy is its unique obstruction stage. -/
noncomputable def KappaLadder.groundedInfiniteIndex
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa) :
    L.groundedInfiniteRecords → Stationary.Below kappa :=
  L.groundedInfiniteStage

/-- The target-marker index used in Assertion 8.12.  The target markers of
the auxiliary web are a subtype of the ladder's marker set, so the
injective marker chronology restricts directly. -/
noncomputable def KappaLadder.targetMarkerIndex
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) :
    (L.popularAuxiliaryInput hlegal).targetMarkers ↪
      Stationary.Below kappa where
  toFun y := L.markerStage ⟨y.1, y.2.1⟩
  inj' := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun w : L.markerSet ↦ w.1)
      (L.markerStage.injective hyz)

/-- The source-stage map on the tagged sources of the auxiliary web.  It is
kept separately from `Input.sourceIndex` so that the stationary-range proof
can use the ladder bookkeeping without repeatedly unfolding its dependent
case split. -/
noncomputable def KappaLadder.auxiliarySourceIndex
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) :
    (L.popularAuxiliaryInput hlegal).lambda.source →
      Stationary.Below kappa :=
  fun x ↦ match h : x.1 with
    | .old a => L.finiteTerminalIndex ⟨a, by
        have hx := h ▸ x.2
        exact ((L.popularAuxiliaryInput hlegal).mem_lambda_source_old a).1 hx⟩
    | .edge a b => False.elim <| by
        have hx := h ▸ x.2
        exact (L.popularAuxiliaryInput hlegal).not_mem_lambda_source_edge a b hx
    | .proxy i => L.groundedInfiniteIndex i

/-- Finite terminals and infinite proxies have distinct, unique obstruction
indices.  Thus the natural source-stage map is injective, the exact
source-boundedness input used in the popular-separator argument. -/
theorem KappaLadder.auxiliarySourceIndex_injective
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) :
    Function.Injective (L.auxiliarySourceIndex hlegal) := by
  let I := L.popularAuxiliaryInput hlegal
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  apply Subtype.ext
  cases x with
  | old a =>
      cases y with
      | old b =>
          let xa : L.groundedFiniteTerminalSet :=
            ⟨a, (I.mem_lambda_source_old a).1 hx⟩
          let yb : L.groundedFiniteTerminalSet :=
            ⟨b, (I.mem_lambda_source_old b).1 hy⟩
          change L.finiteTerminalIndex xa = L.finiteTerminalIndex yb at hxy
          exact congrArg PopularAuxiliary.Input.LambdaVertex.old
            (congrArg Subtype.val (L.finiteTerminalIndex_injective hxy))
      | edge c d => exact False.elim (I.not_mem_lambda_source_edge c d hy)
      | proxy i =>
          let xa : L.groundedFiniteTerminalSet :=
            ⟨a, (I.mem_lambda_source_old a).1 hx⟩
          let xa' : L.finiteTerminalSet :=
            ⟨xa.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xa.2⟩
          change L.finiteTerminalStage xa' = L.groundedInfiniteStage i at hxy
          have hfinite := (L.finiteTerminalStage_spec xa').1.2
          have hinfinite := (L.groundedInfiniteStage_spec i).1.2
          exact False.elim (hfinite (hxy ▸ hinfinite))
  | edge a b => exact False.elim (I.not_mem_lambda_source_edge a b hx)
  | proxy i =>
      cases y with
      | old b =>
          let yb : L.groundedFiniteTerminalSet :=
            ⟨b, (I.mem_lambda_source_old b).1 hy⟩
          let yb' : L.finiteTerminalSet :=
            ⟨yb.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet yb.2⟩
          change L.groundedInfiniteStage i = L.finiteTerminalStage yb' at hxy
          have hfinite := (L.finiteTerminalStage_spec yb').1.2
          have hinfinite := (L.groundedInfiniteStage_spec i).1.2
          exact False.elim (hfinite (hxy.symm ▸ hinfinite))
      | edge c d => exact False.elim (I.not_mem_lambda_source_edge c d hy)
      | proxy j =>
          change L.groundedInfiniteStage i = L.groundedInfiniteStage j at hxy
          apply congrArg PopularAuxiliary.Input.LambdaVertex.proxy
          apply Subtype.ext
          have hi := (L.groundedInfiniteStage_spec i).2
          have hj := (L.groundedInfiniteStage_spec j).2
          rw [hxy] at hi
          exact Option.some.inj (hi.symm.trans hj)

/-- The source-index range in the Section 8 auxiliary web is stationary.
This is the range half of Assertion 8.12.  Every grounded obstruction stage
is represented either by its finite terminal or by its infinite proxy. -/
theorem KappaLadder.auxiliarySourceRange_isStationary
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hL : L.IsKappaHindrance) :
    Stationary.IsStationaryBelow kappa
      (Set.range (L.auxiliarySourceIndex hL.legal)) := by
  let I := L.popularAuxiliaryInput hL.legal
  have hground : Stationary.IsStationaryBelow kappa L.phiGround :=
    KappaLadder.IsKappaHindrance.phiGround_isStationary L hL
      hL.legal.regular hL.legal.uncountable
  apply hground.mono
  intro a ha
  obtain ⟨p, hchosen, hpSource⟩ := ha
  have haPhi : a ∈ L.phi :=
    (L.bookkeeping.mem_phi_iff_exists_chosen
      hL.legal.validBookkeeping).2 ⟨p, hchosen⟩
  rcases p with p | r
  · have haFinite : a ∈ L.phiFinite := by
      refine ⟨haPhi, ?_⟩
      intro haInfinite
      obtain ⟨q, hq, hqRay⟩ :=
        L.bookkeeping.chosen_isRay_of_mem_phiInfinite
          hL.legal.validBookkeeping haInfinite
      have hqp : q = (.inl p : Gamma.DPath) :=
        Option.some.inj (hq.symm.trans hchosen)
      subst q
      change (some p.finish : Option V) = none at hqRay
      cases hqRay
    let x : L.groundedFiniteTerminalSet :=
      ⟨p.finish, a, ⟨⟨.inl p, hchosen, hpSource⟩, haFinite⟩,
        .inl p, hchosen, rfl⟩
    let s : I.lambda.source :=
      ⟨.old x.1,
        (I.mem_lambda_source_old x.1).2 x.2⟩
    refine ⟨s, ?_⟩
    change L.finiteTerminalIndex x = a
    exact L.finiteTerminalStage_eq hL.legal hchosen rfl
      (L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2)
  · have haInfinite : a ∈ L.phiInfinite := by
      refine ⟨haPhi, .inr r, ?_, rfl⟩
      exact L.bookkeeping.chosen_mem_available
        hL.legal.validBookkeeping hchosen
    let i : L.groundedInfiniteRecords :=
      ⟨.inr r, ⟨a, ⟨⟨.inr r, hchosen, hpSource⟩, haInfinite⟩,
        hchosen⟩⟩
    let s : I.lambda.source :=
      ⟨.proxy i,
        I.mem_lambda_source_proxy i⟩
    refine ⟨s, ?_⟩
    change L.groundedInfiniteStage i = a
    exact L.groundedInfiniteStage_eq hL.legal i hchosen

/-! ## The unbalanced auxiliary web (Assertion 8.12) -/

/-- The source map used directly in the ladder argument is definitionally
the source map installed in the generic auxiliary-web package.  Recording
the equality avoids repeatedly unfolding the dependent case split on
tagged source vertices. -/
theorem KappaLadder.auxiliarySourceIndex_eq_sourceIndex
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) :
    L.auxiliarySourceIndex hlegal =
      (L.popularAuxiliaryInput hlegal).sourceIndex
        L.finiteTerminalIndex L.groundedInfiniteIndex := by
  funext x
  apply Subtype.ext
  rcases x with ⟨x, hx⟩
  cases x <;> rfl

/-- The unconditional ordinal indexing of the auxiliary web.  Unlike the
strict `KappaUnbalanced` wrapper below, this package does not assert the
published (and successor-index-sensitive) strict descent inequality. -/
noncomputable def KappaLadder.popularAuxiliaryIndexed
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hL : L.IsKappaHindrance) :
    Popular.KappaIndexed
      (L.popularAuxiliaryInput hL.legal).lambda kappa where
  regular := hL.legal.regular
  uncountable := hL.legal.uncountable
  f := (L.popularAuxiliaryInput hL.legal).sourceIndex
    L.finiteTerminalIndex L.groundedInfiniteIndex
  g := (L.popularAuxiliaryInput hL.legal).targetIndex
    (L.targetMarkerIndex hL.legal)
  f_range_stationary := by
    rw [← L.auxiliarySourceIndex_eq_sourceIndex hL.legal]
    exact L.auxiliarySourceRange_isStationary hL

/-- The natural obstruction-stage indexing of auxiliary sources is
injective, hence supplies the source bound needed by the indexed popularity
dichotomy independently of strict descent. -/
theorem KappaLadder.popularAuxiliaryIndexed_sourceIndexed
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hL : L.IsKappaHindrance) :
    (L.popularAuxiliaryIndexed hL).SourceIndexed := by
  change Function.Injective
    ((L.popularAuxiliaryInput hL.legal).sourceIndex
      L.finiteTerminalIndex L.groundedInfiniteIndex)
  rw [← L.auxiliarySourceIndex_eq_sourceIndex hL.legal]
  exact L.auxiliarySourceIndex_injective hL.legal

/-- Package all of Assertion 8.12 once the pathwise chronology inequality
from source Lemma 7.17 has been established.  The other four fields are
already consequences of legal ladder bookkeeping. -/
noncomputable def KappaLadder.popularAuxiliaryIndexData
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hL : L.IsKappaHindrance)
    (hdescends : ∀
      (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
      (hstart : p.start ∈
        (L.popularAuxiliaryInput hL.legal).lambda.source)
      (hfinish : p.finish ∈
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (L.popularAuxiliaryInput hL.legal).targetIndex
          (L.targetMarkerIndex hL.legal) ⟨p.finish, hfinish⟩ <
        (L.popularAuxiliaryInput hL.legal).sourceIndex
          L.finiteTerminalIndex L.groundedInfiniteIndex
          ⟨p.start, hstart⟩) :
    (L.popularAuxiliaryInput hL.legal).IndexData kappa where
  regular := hL.legal.regular
  uncountable := hL.legal.uncountable
  finiteIndex := L.finiteTerminalIndex
  proxyIndex := L.groundedInfiniteIndex
  markerIndex := L.targetMarkerIndex hL.legal
  sourceRange_stationary := by
    rw [← L.auxiliarySourceIndex_eq_sourceIndex hL.legal]
    exact L.auxiliarySourceRange_isStationary hL
  descends := hdescends

/-- The concrete `kappa`-unbalanced auxiliary web obtained from Assertion
8.12. -/
noncomputable def KappaLadder.popularAuxiliaryUnbalanced
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hL : L.IsKappaHindrance)
    (hdescends : ∀
      (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
      (hstart : p.start ∈
        (L.popularAuxiliaryInput hL.legal).lambda.source)
      (hfinish : p.finish ∈
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (L.popularAuxiliaryInput hL.legal).targetIndex
          (L.targetMarkerIndex hL.legal) ⟨p.finish, hfinish⟩ <
        (L.popularAuxiliaryInput hL.legal).sourceIndex
          L.finiteTerminalIndex L.groundedInfiniteIndex
          ⟨p.start, hstart⟩) :
    Popular.KappaUnbalanced
      (L.popularAuxiliaryInput hL.legal).lambda kappa :=
  { toKappaIndexed := L.popularAuxiliaryIndexed hL
    descends := hdescends }

/-- The source chronology of the concrete auxiliary web is injective.
This is the source-cardinality hypothesis missing from the printed generic
statement of Theorem 8.4. -/
theorem KappaLadder.popularAuxiliaryUnbalanced_sourceIndexed
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hL : L.IsKappaHindrance)
    (hdescends : ∀
      (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
      (hstart : p.start ∈
        (L.popularAuxiliaryInput hL.legal).lambda.source)
      (hfinish : p.finish ∈
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (L.popularAuxiliaryInput hL.legal).targetIndex
          (L.targetMarkerIndex hL.legal) ⟨p.finish, hfinish⟩ <
        (L.popularAuxiliaryInput hL.legal).sourceIndex
          L.finiteTerminalIndex L.groundedInfiniteIndex
          ⟨p.start, hstart⟩) :
    (L.popularAuxiliaryUnbalanced hL hdescends).SourceIndexed := by
  exact L.popularAuxiliaryIndexed_sourceIndexed hL

/-- The actual popular separator used by the grounding argument, with all
fields of source Theorem 8.4 available by projection. -/
noncomputable def KappaLadder.popularAuxiliarySeparator
    {kappa : Cardinal.{u}} (L : Gamma.KappaLadder kappa)
    (hL : L.IsKappaHindrance)
    (hdescends : ∀
      (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
      (hstart : p.start ∈
        (L.popularAuxiliaryInput hL.legal).lambda.source)
      (hfinish : p.finish ∈
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (L.popularAuxiliaryInput hL.legal).targetIndex
          (L.targetMarkerIndex hL.legal) ⟨p.finish, hfinish⟩ <
        (L.popularAuxiliaryInput hL.legal).sourceIndex
          L.finiteTerminalIndex L.groundedInfiniteIndex
          ⟨p.start, hstart⟩) :
    Popular.PopularSeparator (L.popularAuxiliaryIndexed hL) :=
  Popular.theorem8_4_of_sourceIndexed
    (L.popularAuxiliaryUnbalanced hL hdescends)
    (L.popularAuxiliaryUnbalanced_sourceIndexed hL hdescends)

/-! ## Essential trimming produces an ordinary hindrance -/

/-- A separating finite terminal frontier supplies exactly the roof clause
in the definition of a wave. -/
theorem isWave_of_terminalFrontier_isSeparator
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W ⊆ Gamma.source)
    (hsep : Popular.IsSeparator Gamma (Gamma.terminalFrontier W)) :
    Gamma.IsWave W := by
  refine ⟨hW, hsource, ?_⟩
  intro a ha p hp
  exact hsep p (by simpa only [hp.1] using ha) hp.2

/-- A wave with an inessential member becomes a hindrance after essential
trimming.  The omitted member starts in the original source, while warp
disjointness prevents its initial vertex from being the initial vertex of
any retained essential member. -/
theorem essentialWarpPart_isHindrance_of_inessentialPath
    {W : Set Gamma.DPath} (hW : Gamma.IsWave W) {p : Gamma.DPath}
    (hp : p ∈ Gamma.inessentialPaths W) :
    Gamma.IsHindrance (Gamma.essentialWarpPart W) := by
  refine ⟨hW.essentialWarpPart, ?_⟩
  intro heq
  have hpSource : p.initial ∈ Gamma.source :=
    hW.2.1 ⟨p, hp.1, rfl⟩
  have hpEssentialInitial :
      p.initial ∈ Gamma.initialSet (Gamma.essentialWarpPart W) := by
    rw [heq]
    exact hpSource
  obtain ⟨q, hq, hqInitial⟩ := hpEssentialInitial
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hp.2 hq
  exact Set.disjoint_left.1 (hW.1 hp.1 hq.1 hpq)
    p.initial_mem_support (hqInitial ▸ q.initial_mem_support)

/-- The reusable final grounding bridge: a source-starting warp with a
separating frontier and an inessential component yields a hindrance. -/
theorem exists_hindrance_of_groundingWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W ⊆ Gamma.source)
    (hsep : Popular.IsSeparator Gamma (Gamma.terminalFrontier W))
    (hinessential : (Gamma.inessentialPaths W).Nonempty) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  obtain ⟨p, hp⟩ := hinessential
  exact ⟨Gamma.essentialWarpPart W,
    essentialWarpPart_isHindrance_of_inessentialPath
      (isWave_of_terminalFrontier_isSeparator hW hsource hsep) hp⟩

#print axioms isWave_of_terminalFrontier_isSeparator
#print axioms exists_hindrance_of_groundingWarp

end DWeb
end Erdos599
