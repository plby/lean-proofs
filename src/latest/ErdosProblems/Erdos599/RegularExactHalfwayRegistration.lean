/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayExactFrontierInduction
import ErdosProblems.Erdos599.RegularWeakHalfwayRegistration

/-!
# Causal registration of exact-frontier half-way payloads

The regular construction needs the half-way row itself to be terminal-clean
at its recorded stop-over.  This module retains the exact terminal-frontier
equality supplied by the simultaneous lower-cardinal induction, and chooses
the height/selected-carrier registration through an extensional predicate.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExactHalfwayRegistration

open SliceSpliceSource

universe u

variable {V : Type u}

/-- A regular half-way payload with the exact terminal frontier retained. -/
structure ExactHalfwayPayload
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) extends SliceCandidate.HalfwayPayload L alpha U where
  exactFrontier : (L.stageWeb alpha).terminalFrontier W = C

/-- Exact lower induction supplies the source-faithful half-way payload even
for a finite request, after the same countable padding used by the ordinary
regular construction. -/
theorem exists_exactHalfwayPayload_of_lower
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) (h : SliceCandidate.HalfwayChoiceEligible L alpha U) :
    Nonempty (ExactHalfwayPayload L alpha U) := by
  obtain ⟨U', hUU', hU'sub, hU'infinite, hU'card⟩ :=
    SliceCandidate.exists_infinite_enlargement h.request_subset
      h.frontier_infinite
  have hmax : max (#U) aleph0 < kappa :=
    max_lt_iff.mpr ⟨h.request_small, huncountable⟩
  have hU'lt : #U' < kappa := hU'card.trans_lt hmax
  have hhalfway := hlower.exactHalfway hU'lt (L.stageWeb alpha)
    h.stageUnhindered hU'infinite
  obtain ⟨W, C, hstop, hexact, hlinks, X, hX, hXle⟩ :=
    hhalfway U' hU'sub rfl
  obtain ⟨hXsource, R, hR, hroof⟩ := hX
  exact ⟨⟨⟨W, C, X, R, hstop.linkage, hstop.separator, hstop.minimal,
    hstop.quotient_unhindered,
    ControlledSlices.linksToTarget_mono (L.stageWeb alpha) W hUU' hlinks,
    hXsource, hR, hroof, hXle.trans_lt hU'lt⟩, hexact⟩⟩

/-- Extensional exact registration witness at a visible pair coordinate. -/
def IsExactHalfwayRegistrationWitness
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U Z : Set V) : Prop :=
  SliceCandidate.HalfwayChoiceEligible L alpha U ∧
    ∃ (X : Set V) (W : Set (L.stageWeb alpha).DPath) (C : Set V)
        (R : Set ((L.stageWeb alpha).quotient X).DPath),
      IsLinkageBetween (L.stageWeb alpha) (L.frontier alpha) C W ∧
      IsSeparatorFrom (L.stageWeb alpha) (L.frontier alpha) C ∧
      IsTrimmedSeparator (L.stageWeb alpha) C ∧
      ((L.stageWeb alpha).quotient C).IsUnhindered ∧
      LinksToTarget (L.stageWeb alpha) W U ∧
      X ⊆ (L.frontier alpha)ᶜ ∧
      ((L.stageWeb alpha).quotient X).IsWave R ∧
      C ⊆ (L.stageWeb alpha).roof
        (((L.stageWeb alpha).quotient X).terminalFrontier R) ∧
      #X < kappa ∧
      (L.stageWeb alpha).terminalFrontier W = C ∧
      Z = X ∪ (L.stageWeb alpha).vertexSet
        (initialRestriction (L.stageWeb alpha) W U)

def exactHalfwayRegistrationSets
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) : Set (Set V) :=
  {Z | IsExactHalfwayRegistrationWitness L alpha U Z}

/-- The causal exact-frontier registration.  The lower hypothesis is an
argument so the coordinate has the same dependency shape as the row rule;
the choice itself depends only on visible stage data. -/
noncomputable def registrationAt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (_hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (_huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa) : Set V :=
  SliceCandidate.chooseVertexSet
    (exactHalfwayRegistrationSets L delta (request delta gamma))

theorem exactHalfwayRegistrationSets_nonempty_of_eligible
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) (h : SliceCandidate.HalfwayChoiceEligible L alpha U) :
    (exactHalfwayRegistrationSets L alpha U).Nonempty := by
  let D := Classical.choice
    (exists_exactHalfwayPayload_of_lower hlower huncountable L alpha U h)
  refine ⟨D.X ∪ (L.stageWeb alpha).vertexSet
      (initialRestriction (L.stageWeb alpha) D.W U), h,
    D.X, D.W, D.C, D.R, D.linkage, D.separator, D.trimmed,
    D.quotientUnhindered, D.links, D.heightAwayFromSource,
    D.heightWave, D.stopoverRoof, D.heightSmall, D.exactFrontier, rfl⟩

/-- Recover the exact payload selected by its causal registration. -/
theorem exists_exactHalfwayPayload_with_registration
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa)
    (h : SliceCandidate.HalfwayChoiceEligible L delta
      (request delta gamma)) :
    ∃ D : ExactHalfwayPayload L delta (request delta gamma),
      registrationAt hlower huncountable L request delta gamma =
        D.X ∪ (L.stageWeb delta).vertexSet
          (initialRestriction (L.stageWeb delta) D.W
            (request delta gamma)) := by
  have hnonempty := exactHalfwayRegistrationSets_nonempty_of_eligible
    hlower huncountable L delta (request delta gamma) h
  have hchosen := SliceCandidate.chooseVertexSet_mem hnonempty
  change IsExactHalfwayRegistrationWitness L delta (request delta gamma)
    (registrationAt hlower huncountable L request delta gamma) at hchosen
  rcases hchosen with ⟨_, X, W, C, R, hW, hsep, htrim, hquotient,
      hlinks, hXsource, hR, hroof, hXsmall, hexact, hregistration⟩
  exact ⟨⟨⟨W, C, X, R, hW, hsep, htrim, hquotient, hlinks,
    hXsource, hR, hroof, hXsmall⟩, hexact⟩, hregistration⟩

/-- The exact registration is causal: it depends only on the visible stage
web, frontier, and request. -/
theorem registrationAt_congr_stageData
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    {L L' : Gamma.KappaLadder kappa}
    {request request' : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta gamma : Ladder.Stage kappa}
    (hwarp : L.warpAt delta = L'.warpAt delta)
    (hrequest : request delta gamma = request' delta gamma) :
    registrationAt hlower huncountable L request delta gamma =
      registrationAt hlower huncountable L' request' delta gamma := by
  have hstage : L.stageWeb delta = L'.stageWeb delta := by
    simp only [DWeb.KappaLadder.stageWeb, DWeb.stageWebOf, hwarp]
  have hfrontier : L.frontier delta = L'.frontier delta :=
    congrArg DWeb.source hstage
  have heligible :
      SliceCandidate.HalfwayChoiceEligible L delta
          (request delta gamma) ↔
        SliceCandidate.HalfwayChoiceEligible L' delta
          (request' delta gamma) := by
    constructor
    · rintro ⟨hunhindered, hsubset, hsmall, hinfinite⟩
      refine ⟨hstage ▸ hunhindered, ?_, ?_, ?_⟩
      · simpa only [hrequest, hfrontier] using hsubset
      · simpa only [hrequest] using hsmall
      · simpa only [hfrontier] using hinfinite
    · rintro ⟨hunhindered, hsubset, hsmall, hinfinite⟩
      refine ⟨hstage.symm ▸ hunhindered, ?_, ?_, ?_⟩
      · simpa only [hrequest, hfrontier] using hsubset
      · simpa only [hrequest] using hsmall
      · simpa only [hfrontier] using hinfinite
  have hfamilies :
      exactHalfwayRegistrationSets L delta (request delta gamma) =
        exactHalfwayRegistrationSets L' delta (request' delta gamma) := by
    ext Z
    change IsExactHalfwayRegistrationWitness L delta
        (request delta gamma) Z ↔
      IsExactHalfwayRegistrationWitness L' delta
        (request' delta gamma) Z
    unfold IsExactHalfwayRegistrationWitness
    rw [heligible, hrequest, hstage, hfrontier]
  simp only [registrationAt, hfamilies]

/-- Every exact causal registration is bounded by the regular induction
cardinal. -/
theorem mk_registrationAt_le
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa) :
    #(registrationAt hlower huncountable L request delta gamma) ≤ kappa := by
  by_cases hnonempty :
      (exactHalfwayRegistrationSets L delta
        (request delta gamma)).Nonempty
  · have hchosen := SliceCandidate.chooseVertexSet_mem hnonempty
    change IsExactHalfwayRegistrationWitness L delta
      (request delta gamma)
      (registrationAt hlower huncountable L request delta gamma) at hchosen
    rcases hchosen with ⟨heligible, X, W, C, R, hW, hsep, htrim,
        hquotient, hlinks, hXsource, hR, hroof, hXsmall, hexact,
        hregistration⟩
    let D : SliceCandidate.HalfwayPayload L delta
        (request delta gamma) :=
      ⟨W, C, X, R, hW, hsep, htrim, hquotient, hlinks, hXsource,
        hR, hroof, hXsmall⟩
    rw [hregistration]
    exact (RegularCardinal.mk_union_lt hregular hXsmall
      (RegularWeakHalfwayRegistration.mk_selectedCarrier_lt
        huncountable D heligible.request_subset
          heligible.request_small)).le
  · simp only [registrationAt, SliceCandidate.chooseVertexSet,
      dif_neg hnonempty, Cardinal.mk_emptyCollection]
    exact bot_le

/-! ## Recovery from the row's exact-preferential registration -/

/-- Under exact lower induction, the exact-frontier subcollection used by
the ordinary weak row's preferred registration is inhabited. -/
theorem weakExactRegistrationSets_nonempty_of_eligible
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) (h : SliceCandidate.HalfwayChoiceEligible L alpha U) :
    (RegularWeakHalfwayRegistration.exactHalfwayRegistrationSets
      L alpha U).Nonempty := by
  let D := Classical.choice
    (exists_exactHalfwayPayload_of_lower hlower huncountable L alpha U h)
  let Z := D.X ∪ (L.stageWeb alpha).vertexSet
    (initialRestriction (L.stageWeb alpha) D.W U)
  refine ⟨Z, ?_, ?_⟩
  · exact ⟨h, D.X, D.W, D.C, D.R, D.linkage, D.separator, D.trimmed,
      D.quotientUnhindered, D.links, D.heightAwayFromSource,
      D.heightWave, D.stopoverRoof, D.heightSmall, rfl⟩
  · exact ⟨D.X, D.W, D.C, D.R, D.linkage, D.separator, D.trimmed,
      D.quotientUnhindered, D.links, D.heightAwayFromSource,
      D.heightWave, D.stopoverRoof, D.heightSmall, D.exactFrontier, rfl⟩

/-- The payload recovered from the registration already present in
`weakSplitRowRule` has the exact frontier promised by the stronger lower
induction. -/
theorem exists_exactHalfwayPayload_with_weakRegistration
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa)
    (h : SliceCandidate.HalfwayChoiceEligible L delta
      (request delta gamma)) :
    ∃ D : SliceCandidate.HalfwayPayload L delta (request delta gamma),
      (L.stageWeb delta).terminalFrontier D.W = D.C ∧
      RegularWeakHalfwayRegistration.registrationAt
          hlower.toUniversalCardinalInductionBelow huncountable L request
            delta gamma =
        D.X ∪ (L.stageWeb delta).vertexSet
          (initialRestriction (L.stageWeb delta) D.W
            (request delta gamma)) := by
  let hlowerOrdinary := hlower.toUniversalCardinalInductionBelow
  have hexact := weakExactRegistrationSets_nonempty_of_eligible
    hlower huncountable L delta (request delta gamma) h
  have hpref :
      (RegularWeakHalfwayRegistration.preferredHalfwayRegistrationSets
        L delta (request delta gamma)).Nonempty := by
    simpa only
      [RegularWeakHalfwayRegistration.preferredHalfwayRegistrationSets,
        if_pos hexact] using hexact
  have hchosen := SliceCandidate.chooseVertexSet_mem hpref
  have hchosenExact :
      RegularWeakHalfwayRegistration.registrationAt hlowerOrdinary
          huncountable L request delta gamma ∈
        RegularWeakHalfwayRegistration.exactHalfwayRegistrationSets
          L delta (request delta gamma) := by
    simpa only [RegularWeakHalfwayRegistration.registrationAt,
      RegularWeakHalfwayRegistration.preferredHalfwayRegistrationSets,
      if_pos hexact] using hchosen
  rcases hchosenExact.2 with
    ⟨X, W, C, R, hW, hsep, htrim, hquotient, hlinks, hXsource,
      hR, hroof, hXsmall, hexactFrontier, hregistration⟩
  exact ⟨⟨W, C, X, R, hW, hsep, htrim, hquotient, hlinks,
    hXsource, hR, hroof, hXsmall⟩, hexactFrontier, hregistration⟩

end RegularExactHalfwayRegistration
end CardinalInduction
end Erdos599
