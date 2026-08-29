/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularHalfwaySplit
import ErdosProblems.Erdos599.RegularCardinal
import ErdosProblems.Erdos599.SingularSafeCarrierCardinal
import ErdosProblems.Erdos599.SliceCandidateChoice

/-!
# Causal registration of a half-way payload and its selected carrier

The regular construction must choose the half-way row before choosing its
later annular boundary.  Registering only the height witness is insufficient:
the small subfamily rooted at the current request can leave the roof of a
later boundary.  This file makes the whole small carrier causally visible.

As with `SliceCandidate.halfwayHeightSets`, the choice is made through an
extensional predicate which mentions a ladder only through its visible stage
web and frontier.  Consequently it is stable under replacement of a ladder
prefix by the completed ladder.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakHalfwayRegistration

open SliceSpliceSource

universe u

variable {V : Type u}

/-- A registered set is the union of the half-way height witness and the
carrier of the components of the half-way row rooted in the current request.
This raw formulation is deliberately extensional in the visible stage data. -/
def IsHalfwayRegistrationWitness
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
      Z = X ∪ (L.stageWeb alpha).vertexSet
        (initialRestriction (L.stageWeb alpha) W U)

/-- All extensional half-way registrations at one visible coordinate. -/
def halfwayRegistrationSets
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) : Set (Set V) :=
  {Z | IsHalfwayRegistrationWitness L alpha U Z}

/-- The exact-frontier subcollection.  This predicate is still extensional
in the visible stage data, so it can be preferred by the causal choice
without adding the lower-induction proof to the stored coordinate. -/
def exactHalfwayRegistrationSets
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) : Set (Set V) :=
  {Z | IsHalfwayRegistrationWitness L alpha U Z ∧
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
        (initialRestriction (L.stageWeb alpha) W U)}

/-- The registered coordinate is chosen from the exact-frontier witnesses.
The lower half-way theorem always supplies such a witness at an eligible
coordinate, so no weaker fallback is needed. -/
def preferredHalfwayRegistrationSets
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) : Set (Set V) :=
  exactHalfwayRegistrationSets L alpha U

/-- The causal choice of a combined height-and-selected-carrier set. -/
noncomputable def registrationAt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (_hlower : UniversalCardinalInductionBelow V kappa)
    (_huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa) : Set V :=
  SliceCandidate.chooseVertexSet
    (preferredHalfwayRegistrationSets L delta (request delta gamma))

theorem halfwayRegistrationSets_nonempty_of_eligible
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) (h : SliceCandidate.HalfwayChoiceEligible L alpha U) :
    (halfwayRegistrationSets L alpha U).Nonempty := by
  let D := Classical.choice
    (SliceCandidate.exists_halfwayPayload_of_lower
      hlower huncountable L alpha U h)
  refine ⟨D.X ∪ (L.stageWeb alpha).vertexSet
      (initialRestriction (L.stageWeb alpha) D.W U), h,
    D.X, D.W, D.C, D.R, D.linkage, D.separator, D.trimmed,
    D.quotientUnhindered, D.links, D.heightAwayFromSource,
    D.heightWave, D.stopoverRoof, D.heightSmall, rfl⟩

theorem exactHalfwayRegistrationSets_nonempty_of_eligible
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) (h : SliceCandidate.HalfwayChoiceEligible L alpha U) :
    (exactHalfwayRegistrationSets L alpha U).Nonempty := by
  let D := Classical.choice
    (SliceCandidate.exists_halfwayPayload_of_lower
      hlower huncountable L alpha U h)
  refine ⟨D.X ∪ (L.stageWeb alpha).vertexSet
      (initialRestriction (L.stageWeb alpha) D.W U), ?_, ?_⟩
  · exact ⟨h, D.X, D.W, D.C, D.R, D.linkage, D.separator,
      D.trimmed, D.quotientUnhindered, D.links,
      D.heightAwayFromSource, D.heightWave, D.stopoverRoof,
      D.heightSmall, rfl⟩
  · exact ⟨D.X, D.W, D.C, D.R, D.linkage, D.separator,
      D.trimmed, D.quotientUnhindered, D.links,
      D.heightAwayFromSource, D.heightWave, D.stopoverRoof,
      D.heightSmall, D.terminalFrontier_eq, rfl⟩

theorem preferredHalfwayRegistrationSets_nonempty_of_eligible
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) (h : SliceCandidate.HalfwayChoiceEligible L alpha U) :
    (preferredHalfwayRegistrationSets L alpha U).Nonempty := by
  exact exactHalfwayRegistrationSets_nonempty_of_eligible
    hlower huncountable L alpha U h

/-- At an eligible coordinate, recover a genuine payload whose height and
selected carrier are exactly the pre-chosen registration. -/
theorem exists_halfwayPayload_with_registration
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa)
    (h : SliceCandidate.HalfwayChoiceEligible L delta
      (request delta gamma)) :
    ∃ D : SliceCandidate.HalfwayPayload L delta (request delta gamma),
      registrationAt hlower huncountable L request delta gamma =
        D.X ∪ (L.stageWeb delta).vertexSet
          (initialRestriction (L.stageWeb delta) D.W
            (request delta gamma)) := by
  have hnonempty := preferredHalfwayRegistrationSets_nonempty_of_eligible
    hlower huncountable L delta (request delta gamma) h
  have hchosen := SliceCandidate.chooseVertexSet_mem hnonempty
  have hexact : registrationAt hlower huncountable L request
      delta gamma ∈ exactHalfwayRegistrationSets L delta
        (request delta gamma) := by
    simpa only [registrationAt, preferredHalfwayRegistrationSets] using
      hchosen
  rcases hexact.2 with
    ⟨X, W, C, R, hW, hsep, htrim, hquotient, hlinks,
      hXsource, hR, hroof, hXsmall, hterminal, hregistration⟩
  exact ⟨⟨W, C, X, R, hW, htrim, hquotient, hsep, hlinks,
    hterminal, hXsource, hR, hroof, hXsmall⟩, hregistration⟩

/-- The combined causal coordinate depends only on the visible accumulated
warp and the request at that coordinate. -/
theorem registrationAt_congr_stageData
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
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
      · simpa only [hrequest, hstage] using hsubset
      · simpa only [hrequest] using hsmall
      · simpa only [hstage] using hinfinite
    · rintro ⟨hunhindered, hsubset, hsmall, hinfinite⟩
      refine ⟨hstage.symm ▸ hunhindered, ?_, ?_, ?_⟩
      · simpa only [hrequest, hstage] using hsubset
      · simpa only [hrequest] using hsmall
      · simpa only [hstage] using hinfinite
  have hfamilies :
      halfwayRegistrationSets L delta (request delta gamma) =
        halfwayRegistrationSets L' delta (request' delta gamma) := by
    ext Z
    change IsHalfwayRegistrationWitness L delta (request delta gamma) Z ↔
      IsHalfwayRegistrationWitness L' delta (request' delta gamma) Z
    unfold IsHalfwayRegistrationWitness
    rw [heligible, hrequest, hstage, hfrontier]
  have hexactFamilies :
      exactHalfwayRegistrationSets L delta (request delta gamma) =
        exactHalfwayRegistrationSets L' delta (request' delta gamma) := by
    ext Z
    change (IsHalfwayRegistrationWitness L delta
        (request delta gamma) Z ∧ _) ↔
      (IsHalfwayRegistrationWitness L' delta
        (request' delta gamma) Z ∧ _)
    unfold IsHalfwayRegistrationWitness
    rw [heligible, hrequest, hstage, hfrontier]
  simp only [registrationAt, preferredHalfwayRegistrationSets,
    hexactFamilies]

/-- The selected subfamily in a recovered registration has small carrier. -/
theorem mk_selectedCarrier_lt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} {alpha : Ladder.Stage kappa}
    {U : Set V} (D : SliceCandidate.HalfwayPayload L alpha U)
    (hUsource : U ⊆ L.frontier alpha)
    (hU : #U < kappa) :
    #((L.stageWeb alpha).vertexSet
      (initialRestriction (L.stageWeb alpha) D.W U)) < kappa := by
  have hrestricted : IsLinkageBetween (L.stageWeb alpha) U D.C
      (initialRestriction (L.stageWeb alpha) D.W U) :=
    isLinkageBetween_initialRestriction D.linkage hUsource
  exact SingularSafeCarrierCardinal.mk_vertexSet_lt_of_mk_initial_lt
    huncountable hrestricted hU

/-- Every causal registration is bounded by the induction cardinal. -/
theorem mk_registrationAt_le
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa) :
    #(registrationAt hlower huncountable L request delta gamma) ≤ kappa := by
  by_cases hnonempty :
      (preferredHalfwayRegistrationSets L delta
        (request delta gamma)).Nonempty
  · have hchosen := SliceCandidate.chooseVertexSet_mem hnonempty
    have hexact : registrationAt hlower huncountable L request
        delta gamma ∈ exactHalfwayRegistrationSets L delta
          (request delta gamma) := by
      simpa only [registrationAt, preferredHalfwayRegistrationSets] using
        hchosen
    rcases hexact with ⟨⟨heligible, _⟩,
      X, W, C, R, hW, hsep, htrim, hquotient, hlinks,
      hXsource, hR, hroof, hXsmall, hterminal, hregistration⟩
    let D : SliceCandidate.HalfwayPayload L delta (request delta gamma) :=
      ⟨W, C, X, R, hW, htrim, hquotient, hsep, hlinks, hterminal,
        hXsource, hR, hroof, hXsmall⟩
    rw [hregistration]
    exact (RegularCardinal.mk_union_lt hregular hXsmall
      (mk_selectedCarrier_lt huncountable D heligible.request_subset
        heligible.request_small)).le
  · have hempty : registrationAt hlower huncountable L request
        delta gamma = (∅ : Set V) := by
      rw [registrationAt, SliceCandidate.chooseVertexSet,
        dif_neg hnonempty]
    rw [hempty, Cardinal.mk_emptyCollection]
    exact (bot_le : (0 : Cardinal) ≤ kappa)

end RegularWeakHalfwayRegistration
end CardinalInduction
end Erdos599
