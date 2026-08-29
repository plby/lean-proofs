/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ControlledSlices
import ErdosProblems.Erdos599.SliceHalfwayCore
import ErdosProblems.Erdos599.SliceAuxiliaryCore
import ErdosProblems.Erdos599.SliceSplice
import ErdosProblems.Erdos599.SliceSpliceSource
import ErdosProblems.Erdos599.RegularSliceComponentClosure

/-!
# Candidate slices in the regular-cardinal construction

This file starts the construction used to fill the candidate table in
Assertion 9.15.  In particular, it removes a small but important mismatch
between the source proof and the simultaneous induction interface: the
half-way clause is only an induction clause at infinite cardinals, whereas
the request presented to the slice lemma may be finite.  If the stage
frontier is infinite, a finite request is padded inside the frontier to a
countably infinite request.  Thus the lower half-way clause applies and
still links the original request.

The finite-frontier branch is intentionally kept separate: there the lower
extension clause is applied to the whole stage source, so no fictitious
finite instance of the half-way clause is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

open DirectedPath
open ControlledSlices

universe u

variable {V : Type u}

/-- A finite subset of an infinite set can be enlarged, inside that set, to
one of cardinality exactly `aleph0`.  This is the padding step implicit in
the finite-request case of Assertion 9.15. -/
theorem exists_countable_enlargement
    {A U : Set V} (hU : U ⊆ A) (hUfinite : #U < ℵ₀)
    (hAinfinite : ℵ₀ ≤ #A) :
    ∃ U' : Set V, U ⊆ U' ∧ U' ⊆ A ∧ #U' = ℵ₀ := by
  obtain ⟨C, hCA, hCcard⟩ :=
    Cardinal.le_mk_iff_exists_subset.mp hAinfinite
  refine ⟨U ∪ C, Set.subset_union_left, Set.union_subset hU hCA, ?_⟩
  apply le_antisymm
  · exact Cardinal.mk_union_le_aleph0.mpr ⟨hUfinite.le, hCcard.le⟩
  · rw [← hCcard]
    exact Cardinal.mk_subtype_mono Set.subset_union_right

/-- Uniform padding: an already infinite request is left unchanged, while a
finite request in an infinite ambient source is enlarged to a countably
infinite one.  The output cardinal is infinite and is no larger than
`max (#U) aleph0`. -/
theorem exists_infinite_enlargement
    {A U : Set V} (hU : U ⊆ A) (hAinfinite : ℵ₀ ≤ #A) :
    ∃ U' : Set V, U ⊆ U' ∧ U' ⊆ A ∧
      ℵ₀ ≤ #U' ∧ #U' ≤ max (#U) ℵ₀ := by
  by_cases hUinfinite : ℵ₀ ≤ #U
  · exact ⟨U, Set.Subset.rfl, hU, hUinfinite,
      le_max_left (#U) ℵ₀⟩
  · have hUfinite : #U < ℵ₀ := lt_of_not_ge hUinfinite
    obtain ⟨U', hUU', hU'A, hU'card⟩ :=
      exists_countable_enlargement hU hUfinite hAinfinite
    refine ⟨U', hUU', hU'A, hU'card.ge, ?_⟩
    rw [hU'card]
    exact le_max_right (#U) ℵ₀

/-- The lower half-way induction clause applies to every `< kappa` request
in an infinite ladder frontier, including finite requests.  The explicit
height witness is bounded by the padded request and hence is still
`< kappa`.

This is the exact half-way payload needed before the roof-capture and
component-replacement steps of the candidate construction. -/
theorem exists_stageExplicitHalfwayData_of_lower_small
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappaUncountable : ℵ₀ < kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (hstage : (L.stageWeb alpha).IsUnhindered)
    {U : Set V} (hUsub : U ⊆ L.frontier alpha)
    (hU : #U < kappa) (hfrontierInfinite : ℵ₀ ≤ #(L.frontier alpha)) :
    ∃ (W : Set (L.stageWeb alpha).DPath) (C X : Set V)
        (R : Set ((L.stageWeb alpha).quotient X).DPath),
      IsLinkageBetween (L.stageWeb alpha) (L.frontier alpha) C W ∧
      IsTrimmedSeparator (L.stageWeb alpha) C ∧
      ((L.stageWeb alpha).quotient C).IsUnhindered ∧
      LinksToTarget (L.stageWeb alpha) W U ∧
      X ⊆ (L.frontier alpha)ᶜ ∧
      ((L.stageWeb alpha).quotient X).IsWave R ∧
      C ⊆ (L.stageWeb alpha).roof
        (((L.stageWeb alpha).quotient X).terminalFrontier R) ∧
      #X < kappa := by
  obtain ⟨U', hUU', hU'sub, hU'infinite, hU'card⟩ :=
    exists_infinite_enlargement hUsub hfrontierInfinite
  have hmax : max (#U) ℵ₀ < kappa :=
    (max_lt_iff.mpr ⟨hU, hkappaUncountable⟩)
  have hU'lt : #U' < kappa := hU'card.trans_lt hmax
  obtain ⟨W, C, X, R, hW, hCtrim, hCquotient, hlinks,
      hXsource, hR, hroof, _hXle, hXlt⟩ :=
    SliceHalfwayCore.exists_stageExplicitHalfwayData_of_lower
      hlower L alpha hstage hU'sub hU'infinite hU'lt
  exact ⟨W, C, X, R, hW, hCtrim, hCquotient,
    linksToTarget_mono (L.stageWeb alpha) W hUU' hlinks,
    hXsource, hR, hroof, hXlt⟩

/-! ## Pre-choosing the half-way height witnesses -/

/-- The source data chosen before the rows in (9.13a) are closed.  This is
not a candidate slice: it is exactly the output of the strictly lower
half-way induction clause, including its height witness `X`. -/
structure StageHalfwayPayload {kappa : Cardinal.{u}}
    (Q : DWeb V) (U : Set V) where
  W : Set Q.DPath
  C : Set V
  X : Set V
  R : Set (Q.quotient X).DPath
  linkage : IsLinkageBetween Q Q.source C W
  trimmed : IsTrimmedSeparator Q C
  quotientUnhindered : (Q.quotient C).IsUnhindered
  /-- The stop-over separates the whole stage frontier from the target.
  This field is retained by the strengthened simultaneous induction and is
  exactly what the auxiliary quotient completion in Assertion 9.15 uses. -/
  separator : IsSeparatorFrom Q Q.source C
  links : LinksToTarget Q W U
  /-- The chosen stop-over is the actual terminal frontier of the half-way
  linkage.  Besides being source-faithful, this makes first-hit tightening
  and quotient continuation insensitive to source/stop-over overlap. -/
  terminalFrontier_eq : Q.terminalFrontier W = C
  heightAwayFromSource : X ⊆ Q.sourceᶜ
  heightWave : (Q.quotient X).IsWave R
  stopoverRoof : C ⊆ Q.roof ((Q.quotient X).terminalFrontier R)
  heightSmall : #X < kappa

/-- Ladder-indexed public name for the stage-local pre-choice payload.

The underlying data is deliberately keyed only by the exact stage web and
its source frontier.  This makes the canonical choice invariant under the
prefix equalities used by the causal row recursion: changing bookkeeping or
future ladder stages does not create a distinct nominal choice type. -/
abbrev HalfwayPayload
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) :=
  StageHalfwayPayload (kappa := kappa)
    (L.stageWeb alpha) U

/-- The non-result conditions under which the pre-choice table has a
half-way entry. -/
structure StageHalfwayChoiceEligible {kappa : Cardinal.{u}}
    (Q : DWeb V) (U : Set V) : Prop where
  stageUnhindered : Q.IsUnhindered
  request_subset : U ⊆ Q.source
  request_small : #U < kappa
  frontier_infinite : ℵ₀ ≤ #Q.source

/-- Ladder-indexed public name for stage-local eligibility. -/
abbrev HalfwayChoiceEligible
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) : Prop :=
  StageHalfwayChoiceEligible (kappa := kappa)
    (L.stageWeb alpha) U

theorem exists_stageHalfwayPayload_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa)
    (Q : DWeb V) (U : Set V)
    (h : StageHalfwayChoiceEligible (kappa := kappa) Q U) :
    Nonempty (StageHalfwayPayload (kappa := kappa) Q U) := by
  obtain ⟨U', hUU', hU'sub, hU'infinite, hU'card⟩ :=
    exists_infinite_enlargement h.request_subset h.frontier_infinite
  have hmax : max (#U) ℵ₀ < kappa :=
    max_lt_iff.mpr ⟨h.request_small, huncountable⟩
  have hU'lt : #U' < kappa := hU'card.trans_lt hmax
  have hstep : CardinalInductionAt Q #U' :=
    hlower #U' hU'lt Q h.stageUnhindered
  obtain ⟨W, C, hstop, hlinks, hheight, hfrontier⟩ :=
    hstep.separatingHalfway hU'infinite U' hU'sub rfl
  obtain ⟨X, hX, hXcard⟩ := hheight
  obtain ⟨hXsource, R, hR, hroof⟩ := hX
  exact ⟨⟨W, C, X, R, hstop.linkage, hstop.stopover.minimal,
    hstop.stopover.quotient_unhindered, hstop.separator,
    linksToTarget_mono Q W hUU' hlinks,
    hfrontier, hXsource, hR, hroof, hXcard.trans_lt hU'lt⟩⟩

theorem exists_halfwayPayload_of_lower
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (U : Set V) (h : HalfwayChoiceEligible L alpha U) :
    Nonempty (HalfwayPayload L alpha U) :=
  exists_stageHalfwayPayload_of_lower hlower huncountable
    (L.stageWeb alpha) U h

/-- The actual choice is keyed by the visible stage web and source, rather
than by the nominal whole ladder carrying them. -/
noncomputable def chosenStageHalfwayPayloadOfUncountable
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa) (Q : DWeb V) (U : Set V) :
    Option (StageHalfwayPayload (kappa := kappa) Q U) := by
  classical
  exact if h : StageHalfwayChoiceEligible (kappa := kappa) Q U then
    some (Classical.choice
      (exists_stageHalfwayPayload_of_lower hlower huncountable Q U h))
  else none

/-- Stage-local projection of the chosen height set. -/
noncomputable def chosenStageHeightSetOfUncountable
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa) (Q : DWeb V) (U : Set V) : Set V :=
  match chosenStageHalfwayPayloadOfUncountable
      hlower huncountable Q U with
  | some D => D.X
  | none => ∅

/-- Optional half-way choice made uniformly for every table coordinate.
Only uncountability of the ambient induction cardinal is used.  In
particular this definition can be evaluated by a causal row rule before a
globally legal completed ladder has been assembled. -/
noncomputable def chosenHalfwayPayloadOfUncountable
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa) (L : Gamma.KappaLadder kappa)
    (alpha : Ladder.Stage kappa) (U : Set V) :
    Option (HalfwayPayload L alpha U) := by
  exact chosenStageHalfwayPayloadOfUncountable hlower huncountable
    (L.stageWeb alpha) U

/-- Legal-ladder wrapper retained for downstream table consumers. -/
noncomputable def chosenHalfwayPayload
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (L : Gamma.KappaLadder kappa) (hL : L.IsLegal)
    (alpha : Ladder.Stage kappa) (U : Set V) :
    Option (HalfwayPayload L alpha U) :=
  chosenHalfwayPayloadOfUncountable hlower hL.uncountable L alpha U

/-- The height set inserted into the closing-up rows.  Ineligible entries
contribute the empty set, just as nonexistent candidate entries do. -/
noncomputable def chosenHeightSet
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (L : Gamma.KappaLadder kappa) (hL : L.IsLegal)
    (alpha : Ladder.Stage kappa) (U : Set V) : Set V :=
  chosenStageHeightSetOfUncountable hlower hL.uncountable
    (L.stageWeb alpha) U

/-- Causal-row version of `chosenHeightSet`, requiring only
uncountability and the ladder prefix visible at the current row. -/
noncomputable def chosenHeightSetOfUncountable
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa) (L : Gamma.KappaLadder kappa)
    (alpha : Ladder.Stage kappa) (U : Set V) : Set V :=
  chosenStageHeightSetOfUncountable hlower huncountable
    (L.stageWeb alpha) U

/-- The causal height choice depends only on the accumulated warp at its
coordinate.  Hence two ladder prefixes with the same visible stage make
literally the same registered height choice, independently of their future
stages and bookkeeping fields. -/
theorem chosenHeightSetOfUncountable_congr_warpAt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa)
    (L L' : Gamma.KappaLadder kappa)
    (alpha : Ladder.Stage kappa) (U : Set V)
    (hwarp : L.warpAt alpha = L'.warpAt alpha) :
    chosenHeightSetOfUncountable hlower huncountable L alpha U =
      chosenHeightSetOfUncountable hlower huncountable L' alpha U := by
  have hstage : L.stageWeb alpha = L'.stageWeb alpha := by
    exact congrArg Gamma.stageWebOf hwarp
  unfold chosenHeightSetOfUncountable
  rw [hstage]

@[simp]
theorem chosenHeightSet_eq_ofUncountable
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (L : Gamma.KappaLadder kappa) (hL : L.IsLegal)
    (alpha : Ladder.Stage kappa) (U : Set V) :
    chosenHeightSet hlower L hL alpha U =
      chosenHeightSetOfUncountable hlower hL.uncountable L alpha U :=
  rfl

/-- At every eligible coordinate, the optional table exposes the exact
pre-chosen payload and its registered height set. -/
theorem chosenHalfwayPayload_spec
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (L : Gamma.KappaLadder kappa) (hL : L.IsLegal)
    (alpha : Ladder.Stage kappa) (U : Set V)
    (h : HalfwayChoiceEligible L alpha U) :
    ∃ D : HalfwayPayload L alpha U,
      chosenHalfwayPayload hlower L hL alpha U = some D ∧
        chosenHeightSet hlower L hL alpha U = D.X := by
  let D : HalfwayPayload L alpha U := Classical.choice
    (exists_stageHalfwayPayload_of_lower hlower hL.uncountable
      (L.stageWeb alpha) U h)
  refine ⟨D, ?_, ?_⟩
  · simp [chosenHalfwayPayload, chosenHalfwayPayloadOfUncountable,
      chosenStageHalfwayPayloadOfUncountable, h, D]
  · simp [chosenHeightSet, chosenStageHeightSetOfUncountable,
      chosenStageHalfwayPayloadOfUncountable, h, D]

/-- Eligibility specification for the causal-row half-way choice. -/
theorem chosenHalfwayPayloadOfUncountable_spec
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa) (L : Gamma.KappaLadder kappa)
    (alpha : Ladder.Stage kappa) (U : Set V)
    (h : HalfwayChoiceEligible L alpha U) :
    ∃ D : HalfwayPayload L alpha U,
      chosenHalfwayPayloadOfUncountable hlower huncountable L alpha U =
          some D ∧
        chosenHeightSetOfUncountable hlower huncountable L alpha U = D.X := by
  let D : HalfwayPayload L alpha U := Classical.choice
    (exists_stageHalfwayPayload_of_lower hlower huncountable
      (L.stageWeb alpha) U h)
  refine ⟨D, ?_, ?_⟩
  · simp [chosenHalfwayPayloadOfUncountable,
      chosenStageHalfwayPayloadOfUncountable, h, D]
  · simp [chosenHeightSetOfUncountable,
      chosenStageHeightSetOfUncountable,
      chosenStageHalfwayPayloadOfUncountable, h, D]

/-- One causal row coordinate, before any unbounded union is formed. -/
noncomputable def heightVerticesAt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa) (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa) : Set V :=
  chosenHeightSetOfUncountable hlower huncountable L delta
    (request delta gamma)

/-- Prefix invariance of one registered height-table coordinate. -/
theorem heightVerticesAt_congr_stageData
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa)
    (L L' : Gamma.KappaLadder kappa)
    (request request' : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa)
    (hwarp : L.warpAt delta = L'.warpAt delta)
    (hrequest : request delta gamma = request' delta gamma) :
    heightVerticesAt hlower huncountable L request delta gamma =
      heightVerticesAt hlower huncountable L' request' delta gamma := by
  unfold heightVerticesAt
  rw [hrequest]
  exact chosenHeightSetOfUncountable_congr_warpAt
    hlower huncountable L L' delta _ hwarp

theorem heightVerticesAt_eq_chosenHeightSet
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (L : Gamma.KappaLadder kappa) (hL : L.IsLegal)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa) :
    heightVerticesAt hlower hL.uncountable L request delta gamma =
      chosenHeightSet hlower L hL delta (request delta gamma) :=
  rfl

/-- Each pre-chosen height witness is a bounded single-coordinate row
contribution.  This estimate does not inspect any future ladder stage. -/
theorem mk_heightVerticesAt_le
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : ℵ₀ < kappa) (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa) :
    #(heightVerticesAt hlower huncountable L request delta gamma) ≤ kappa := by
  generalize hoption : chosenStageHalfwayPayloadOfUncountable
    hlower huncountable (L.stageWeb delta) (request delta gamma) = option
  cases option with
  | none =>
      simp only [heightVerticesAt, chosenHeightSetOfUncountable,
        chosenStageHeightSetOfUncountable, hoption,
        Cardinal.mk_emptyCollection]
      exact bot_le
  | some D =>
      simpa only [heightVerticesAt, chosenHeightSetOfUncountable,
        chosenStageHeightSetOfUncountable, hoption]
        using D.heightSmall.le

/-- Request-indexed notation for the family of all pre-chosen height sets
which the row constructor must register. -/
noncomputable def chosenHeightVertices
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (L : Gamma.KappaLadder kappa) (hL : L.IsLegal)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V) : Set V :=
  ⋃ alpha, ⋃ gamma,
    chosenHeightSet hlower L hL alpha (request alpha gamma)

theorem chosenHeightSet_subset_chosenHeightVertices
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (L : Gamma.KappaLadder kappa) (hL : L.IsLegal)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (alpha gamma : Ladder.Stage kappa) :
    chosenHeightSet hlower L hL alpha (request alpha gamma) ⊆
      chosenHeightVertices hlower L hL request := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨alpha, Set.mem_iUnion.2 ⟨gamma, hx⟩⟩

/-- The lower extension clause links an unhindered stage whenever its whole
frontier has cardinality `< kappa`.  This is the branch used when the
frontier itself is finite; it does not appeal to a nonexistent finite
half-way induction clause. -/
theorem exists_stageFullLinkage_of_lower
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (hstage : (L.stageWeb alpha).IsUnhindered)
    (hfrontier : #(L.frontier alpha) < kappa) :
    ∃ W : Set (L.stageWeb alpha).DPath,
      IsLinkageBetween (L.stageWeb alpha) (L.frontier alpha)
        (L.stageWeb alpha).target W := by
  exact linkable_of_cardinalInductionAt_source (L.stageWeb alpha)
    (hlower (#(L.frontier alpha)) hfrontier (L.stageWeb alpha) hstage)

/-- `LinksToTarget` contains a choice of one witnessing member for each
requested vertex.  Taking the range of those choices gives a subfamily of
cardinality at most that of the request.  This is the small exceptional
half-way subfamily retained during component replacement. -/
theorem exists_small_targetLinkingSubfamily
    (Q : DWeb V) {W : Set Q.DPath} {U : Set V}
    (hlinks : LinksToTarget Q W U) :
    ∃ K : Set Q.DPath,
      K ⊆ W ∧ LinksToTarget Q K U ∧ #K ≤ #U := by
  let witness : ∀ a : U, ∃ p ∈ W,
      ∃ q : DirectedPath.FinitePath Q.graph,
        p = .inl q ∧ q.support ∩ U = {a.1} ∧
          FinitePathSuffixMeets q a.1 Q.target :=
    fun a ↦ hlinks a.1 a.2
  let chosen : U → Q.DPath := fun a ↦ Classical.choose (witness a)
  let K : Set Q.DPath := Set.range chosen
  have hchosen_mem (a : U) : chosen a ∈ W :=
    (Classical.choose_spec (witness a)).1
  have hchosen_spec (a : U) :
      ∃ q : DirectedPath.FinitePath Q.graph,
        chosen a = .inl q ∧ q.support ∩ U = {a.1} ∧
          FinitePathSuffixMeets q a.1 Q.target :=
    (Classical.choose_spec (witness a)).2
  refine ⟨K, ?_, ?_, Cardinal.mk_range_le⟩
  · rintro p ⟨a, rfl⟩
    exact hchosen_mem a
  · intro a ha
    let a' : U := ⟨a, ha⟩
    obtain ⟨q, hq, hpure, hsuffix⟩ := hchosen_spec a'
    exact ⟨chosen a', ⟨a', rfl⟩, q, hq, hpure, hsuffix⟩

/-- In particular, the selected target-linking subfamily is `< kappa`
whenever the request is. -/
theorem exists_targetLinkingSubfamily_mk_lt
    (Q : DWeb V) {kappa : Cardinal.{u}} {W : Set Q.DPath} {U : Set V}
    (hlinks : LinksToTarget Q W U) (hU : #U < kappa) :
    ∃ K : Set Q.DPath,
      K ⊆ W ∧ LinksToTarget Q K U ∧ #K < kappa := by
  obtain ⟨K, hKW, hKlinks, hKcard⟩ :=
    exists_small_targetLinkingSubfamily Q hlinks
  exact ⟨K, hKW, hKlinks, hKcard.trans_lt hU⟩

/-- Any subfamily of a linkage is an exceptional remainder relative to the
same endpoint sets.  This lets the slice construction retain the genuinely
small family selected above without postulating an
`ExceptionalRealization` certificate. -/
theorem isExceptionalRemainder_of_linkage_subfamily
    (Q : DWeb V) {A C : Set V} {W K : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) (hK : K ⊆ W) :
    SliceSegmentCore.IsExceptionalRemainder Q A C K := by
  refine ⟨hW.isWarp.subset hK,
    (fun {_} hp ↦ hW.finiteCharacter (hK hp)), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hpK, rfl⟩ := hx
    rw [← hW.initialSet_eq]
    exact ⟨p, hK hpK, rfl⟩
  · rintro x ⟨p, hpK, hpx⟩
    exact hW.terminalFrontier_subset ⟨p, hK hpK, hpx⟩
  · intro p hpK
    exact hW.endpointPure p (hK hpK)

/-- The actual small exceptional remainder selected by a target-linking
linkage.  Its size estimate comes from the request, rather than from the
size of the whole stage frontier. -/
theorem exists_small_targetLinkingRemainder
    (Q : DWeb V) {A C U : Set V} {kappa : Cardinal.{u}}
    {W : Set Q.DPath} (hW : IsLinkageBetween Q A C W)
    (hlinks : LinksToTarget Q W U) (hU : #U < kappa) :
    ∃ K : Set Q.DPath,
      SliceSegmentCore.IsExceptionalRemainder Q A C K ∧
      LinksToTarget Q K U ∧ #K < kappa := by
  obtain ⟨K, hKW, hKlinks, hKcard⟩ :=
    exists_targetLinkingSubfamily_mk_lt Q hlinks hU
  exact ⟨K, isExceptionalRemainder_of_linkage_subfamily Q hW hKW,
    hKlinks, hKcard⟩

/-- A linkage has no more members than initial vertices.  The selector is
the initial vertex of each member; vertex-disjointness makes it injective. -/
theorem mk_linkage_le_initial
    (Q : DWeb V) {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) : #W ≤ #A := by
  apply FamilyTools.mk_le_of_pairwiseDisjoint_of_meets
  · exact hW.isWarp
  · intro p hp
    have hpA : p.initial ∈ A := by
      rw [← hW.initialSet_eq]
      exact ⟨p, hp, rfl⟩
    exact ⟨p.initial, hpA, p.initial_mem_support⟩

/-- Consequently every subfamily of a linkage, including the mavericks of
a slice, is bounded by the initial frontier. -/
theorem mk_subfamily_lt_of_linkage_initial_lt
    (Q : DWeb V) {A C : Set V} {W K : Set Q.DPath}
    {kappa : Cardinal.{u}} (hW : IsLinkageBetween Q A C W)
    (hK : K ⊆ W) (hA : #A < kappa) : #K < kappa :=
  (Cardinal.mk_subtype_mono hK).trans
    (mk_linkage_le_initial Q hW) |>.trans_lt hA

/-! ## Source-indexed first-hit linkage families -/

private theorem exists_linkageMemberAt
    {Q : DWeb V} {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) (x : A) :
    ∃ p ∈ W, p.initial = x.1 := by
  have hx : x.1 ∈ Q.initialSet W := hW.initialSet_eq.symm ▸ x.2
  exact hx

/-- The unique member of a linkage starting at a prescribed source. -/
noncomputable def linkageMemberAt
    {Q : DWeb V} {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) (x : A) : W :=
  ⟨Classical.choose (exists_linkageMemberAt hW x),
    (Classical.choose_spec (exists_linkageMemberAt hW x)).1⟩

@[simp] theorem linkageMemberAt_initial
    {Q : DWeb V} {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) (x : A) :
    (linkageMemberAt hW x).1.initial = x.1 :=
  (Classical.choose_spec (exists_linkageMemberAt hW x)).2

theorem linkageMemberAt_injective
    {Q : DWeb V} {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) :
    Function.Injective (linkageMemberAt hW) := by
  intro x y hxy
  apply Subtype.ext
  calc
    x.1 = (linkageMemberAt hW x).1.initial :=
      (linkageMemberAt_initial hW x).symm
    _ = (linkageMemberAt hW y).1.initial :=
      congrArg (fun z : W ↦ z.1.initial) hxy
    _ = y.1 := linkageMemberAt_initial hW y

/-- The finite representative of the linkage member at `x`. -/
noncomputable def linkageFiniteAt
    {Q : DWeb V} {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) (x : A) :
    DirectedPath.FinitePath Q.graph :=
  Classical.choose (hW.finiteCharacter (linkageMemberAt hW x).2)

theorem linkageMemberAt_eq_finite
    {Q : DWeb V} {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) (x : A) :
    (linkageMemberAt hW x).1 = .inl (linkageFiniteAt hW x) :=
  Classical.choose_spec (hW.finiteCharacter (linkageMemberAt hW x).2)

@[simp] theorem linkageFiniteAt_start
    {Q : DWeb V} {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) (x : A) :
    (linkageFiniteAt hW x).start = x.1 := by
  have h := linkageMemberAt_initial hW x
  rw [linkageMemberAt_eq_finite] at h
  change (linkageFiniteAt hW x).start = x.1 at h
  exact h

theorem linkageFiniteAt_finish_mem
    {Q : DWeb V} {A C : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W) (x : A) :
    (linkageFiniteAt hW x).finish ∈ C := by
  apply hW.terminalFrontier_subset
  refine ⟨(linkageMemberAt hW x).1, (linkageMemberAt hW x).2, ?_⟩
  rw [linkageMemberAt_eq_finite]
  rfl

theorem linkageFiniteAt_meets
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) (x : A) :
    (linkageFiniteAt hW x).walk.Meets D := by
  apply hsep (linkageFiniteAt hW x).walk
  · rw [linkageFiniteAt_start]
    exact x.2
  · exact linkageFiniteAt_finish_mem hW x

/-- First visit of the member at `x` to a separating boundary. -/
noncomputable def linkageFirstHitAt
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) (x : A) :
    DirectedPath.FinitePath Q.graph :=
  (linkageFiniteAt hW x).firstHit D (linkageFiniteAt_meets hW hsep x)

@[simp] theorem linkageFirstHitAt_start
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) (x : A) :
    (linkageFirstHitAt hW hsep x).start = x.1 := by
  exact linkageFiniteAt_start hW x

theorem linkageFirstHitAt_finish_mem
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) (x : A) :
    (linkageFirstHitAt hW hsep x).finish ∈ D :=
  DirectedPath.FinitePath.firstHit_finish_mem _ _ _

theorem linkageFirstHitAt_support_subset
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) (x : A) :
    (linkageFirstHitAt hW hsep x).support ⊆
      (linkageFiniteAt hW x).support :=
  DirectedPath.FinitePath.firstHit_support_subset _ _ _

theorem linkageFirstHitAt_edgeSet_subset
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) (x : A) :
    (linkageFirstHitAt hW hsep x).edgeSet ⊆
      (linkageFiniteAt hW x).edgeSet :=
  DirectedPath.FinitePath.firstHit_edgeSet_subset _ _ _

theorem linkageFirstHitAt_targetPure
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) (x : A) :
    (linkageFirstHitAt hW hsep x).support ∩ D =
      {(linkageFirstHitAt hW hsep x).finish} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hy, hyD⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hyFinish
    have hlast :
        (linkageFirstHitAt hW hsep x).walk.support.getLast
            (linkageFirstHitAt hW hsep x).walk.support_ne_nil =
          (linkageFirstHitAt hW hsep x).finish :=
      (linkageFirstHitAt hW hsep x).walk.getLast_support
    have hyLast : y ≠
        (linkageFirstHitAt hW hsep x).walk.support.getLast
          (linkageFirstHitAt hW hsep x).walk.support_ne_nil := by
      intro h
      exact hyFinish (h.trans hlast)
    exact DirectedPath.FinitePath.firstHit_no_mem_before
      (linkageFiniteAt hW x) D (linkageFiniteAt_meets hW hsep x)
      (List.mem_dropLast_of_mem_of_ne_getLast hy hyLast) hyD
  · intro y hy
    have hyFinish : y = (linkageFirstHitAt hW hsep x).finish :=
      Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨(linkageFirstHitAt hW hsep x).finish_mem_support,
      linkageFirstHitAt_finish_mem hW hsep x⟩

/-- Source-indexed family of first-boundary prefixes. -/
def firstHitPrefixFamily
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) : Set Q.DPath :=
  Set.range fun x : A ↦ (.inl (linkageFirstHitAt hW hsep x) : Q.DPath)

theorem firstHitPrefixFamily_isLinkageBetween
    {Q : DWeb V} {A C D : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hsep : RelationalRoof.Separates Q.graph.Adj A C D) :
    IsLinkageBetween Q A D (firstHitPrefixFamily hW hsep) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    apply (hW.isWarp (linkageMemberAt hW x).2
      (linkageMemberAt hW y).2 ?_).mono
      (by
        rw [linkageMemberAt_eq_finite]
        exact linkageFirstHitAt_support_subset hW hsep x)
      (by
        rw [linkageMemberAt_eq_finite]
        exact linkageFirstHitAt_support_subset hW hsep y)
    intro hmember
    apply hxy
    congr
    exact linkageMemberAt_injective hW (Subtype.ext hmember)
  · rintro _ ⟨x, rfl⟩
    exact ⟨linkageFirstHitAt hW hsep x, rfl⟩
  · ext v
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, hv⟩
      exact (linkageFirstHitAt_start hW hsep x).symm.trans hv ▸ x.2
    · intro hv
      let x : A := ⟨v, hv⟩
      exact ⟨.inl (linkageFirstHitAt hW hsep x), ⟨x, rfl⟩,
        linkageFirstHitAt_start hW hsep x⟩
  · rintro v ⟨_, ⟨x, rfl⟩, hv⟩
    change some (linkageFirstHitAt hW hsep x).finish = some v at hv
    exact Option.some.inj hv ▸ linkageFirstHitAt_finish_mem hW hsep x
  · rintro _ ⟨x, rfl⟩
    obtain ⟨q, hq, _hends, hsource⟩ :=
      hW.endpointPure (linkageMemberAt hW x).1
        (linkageMemberAt hW x).2
    have hqeq : q = linkageFiniteAt hW x := by
      apply Sum.inl.inj
      exact hq.symm.trans (linkageMemberAt_eq_finite hW x)
    subst q
    have hsource' : (linkageFirstHitAt hW hsep x).support ∩ A =
        {(linkageFirstHitAt hW hsep x).start} := by
      apply Set.Subset.antisymm
      · rintro y ⟨hy, hyA⟩
        have hyOld : y ∈ (linkageFiniteAt hW x).support ∩ A :=
          ⟨linkageFirstHitAt_support_subset hW hsep x hy, hyA⟩
        rw [hsource] at hyOld
        exact Set.mem_singleton_iff.mpr
          ((Set.mem_singleton_iff.mp hyOld).trans
            ((linkageFiniteAt_start hW x).trans
              (linkageFirstHitAt_start hW hsep x).symm))
      · intro y hy
        subst y
        exact ⟨(linkageFirstHitAt hW hsep x).start_mem_support,
          linkageFirstHitAt_start hW hsep x ▸ x.2⟩
    refine ⟨linkageFirstHitAt hW hsep x, rfl, ?_, hsource'⟩
    rw [Set.inter_union_distrib_left, hsource',
      linkageFirstHitAt_targetPure hW hsep x]
    rfl

/-! ## Whole alternating-component cuts

The regular and singular exchange arguments both use the same elementary
operation: retain the first family on every alternating component meeting a
seed set, and retain the second family on all remaining components.  These
definitions used to live only in compiled artifacts; keeping them here makes
the component-exchange layer reproducible from source. -/

/-- Members of `W` whose initial vertex lies in `D`. -/
def initialPart (Q : DWeb V) (W : Set Q.DPath) (D : Set V) : Set Q.DPath :=
  {p | p ∈ W ∧ p.initial ∈ D}

theorem initialSet_initialPart (Q : DWeb V) (W : Set Q.DPath) (D : Set V) :
    Q.initialSet (initialPart Q W D) = Q.initialSet W ∩ D := by
  ext x
  constructor
  · rintro ⟨p, ⟨hpW, hpD⟩, rfl⟩
    exact ⟨⟨p, hpW, rfl⟩, hpD⟩
  · rintro ⟨⟨p, hpW, hpx⟩, hxD⟩
    exact ⟨p, ⟨hpW, hpx.symm ▸ hxD⟩, hpx⟩

/-- Union of all alternating components meeting `E`. -/
def exceptionalComponentVertices (Q : DWeb V) (W Y : Set Q.DPath)
    (E : Set V) : Set V :=
  ⋃ x ∈ E, AlternatingComponents.component W Y x

theorem mem_exceptionalComponentVertices_of_mem
    (Q : DWeb V) (W Y : Set Q.DPath) {E : Set V} {x : V} (hx : x ∈ E) :
    x ∈ exceptionalComponentVertices Q W Y E := by
  simp only [exceptionalComponentVertices, Set.mem_iUnion]
  exact ⟨x, hx, AlternatingComponents.mem_component_self W Y x⟩

/-- A finite-character left path that meets the exceptional closure is
entirely contained in it. -/
theorem path_support_subset_exceptionalComponents_left
    {Q : DWeb V} {W Y : Set Q.DPath}
    (hfinite : Q.HasFiniteCharacter W) {p : Q.DPath} (hpW : p ∈ W)
    {x : V} (hxp : x ∈ p.support)
    {E : Set V} (hxD : x ∈ exceptionalComponentVertices Q W Y E) :
    p.support ⊆ exceptionalComponentVertices Q W Y E := by
  obtain ⟨q, rfl⟩ := hfinite hpW
  rw [exceptionalComponentVertices] at hxD ⊢
  obtain ⟨root, hxD⟩ := Set.mem_iUnion.mp hxD
  obtain ⟨hrootE, hxroot⟩ := Set.mem_iUnion.mp hxD
  intro y hyp
  apply Set.mem_iUnion.mpr
  refine ⟨root, Set.mem_iUnion.mpr ⟨hrootE, ?_⟩⟩
  exact AlternatingComponents.finitePath_support_subset_component_of_touches_left
    hxroot hpW hxp hyp

/-- Right-family version of
`path_support_subset_exceptionalComponents_left`. -/
theorem path_support_subset_exceptionalComponents_right
    {Q : DWeb V} {W Y : Set Q.DPath}
    (hfinite : Q.HasFiniteCharacter Y) {p : Q.DPath} (hpY : p ∈ Y)
    {x : V} (hxp : x ∈ p.support)
    {E : Set V} (hxD : x ∈ exceptionalComponentVertices Q W Y E) :
    p.support ⊆ exceptionalComponentVertices Q W Y E := by
  obtain ⟨q, rfl⟩ := hfinite hpY
  rw [exceptionalComponentVertices] at hxD ⊢
  obtain ⟨root, hxD⟩ := Set.mem_iUnion.mp hxD
  obtain ⟨hrootE, hxroot⟩ := Set.mem_iUnion.mp hxD
  intro y hyp
  apply Set.mem_iUnion.mpr
  refine ⟨root, Set.mem_iUnion.mpr ⟨hrootE, ?_⟩⟩
  exact AlternatingComponents.finitePath_support_subset_component_of_touches_right
    hxroot hpY hxp hyp

/-- Fewer than `kappa` countable alternating components have union smaller
than the uncountable regular cardinal `kappa`. -/
theorem mk_exceptionalComponentVertices_lt
    {Q : DWeb V} {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : Cardinal.aleph0 < kappa)
    {W Y : Set Q.DPath} (hW : Q.IsWarp W) (hY : Q.IsWarp Y)
    (hWfinite : Q.HasFiniteCharacter W)
    (hYfinite : Q.HasFiniteCharacter Y) {E : Set V} (hE : #E < kappa) :
    #(exceptionalComponentVertices Q W Y E) < kappa := by
  exact RegularSliceComponentClosure.mk_seededComponentClosure_lt
    hregular huncountable hW hY hWfinite hYfinite hE

/-- Retain `W` on the exceptional components and `Y` off them. -/
def componentMixedFamily (Q : DWeb V) (W Y : Set Q.DPath)
    (E : Set V) : Set Q.DPath :=
  initialPart Q W (exceptionalComponentVertices Q W Y E) ∪
    initialPart Q Y (exceptionalComponentVertices Q W Y E)ᶜ

/-- Complementary-source component switching preserves an exact linkage. -/
theorem componentMixedFamily_isLinkageBetween_of_complement
    (Q : DWeb V) {A B E : Set V} {W Y : Set Q.DPath}
    (hW : IsLinkageBetween Q A B W)
    (hY : IsLinkageBetween Q (A \ E) B Y) (hEsub : E ⊆ A) :
    IsLinkageBetween Q A B (componentMixedFamily Q W Y E) := by
  let D := exceptionalComponentVertices Q W Y E
  let WL := initialPart Q W D
  let YR := initialPart Q Y Dᶜ
  have hED : E ⊆ D := by
    intro x hx
    exact mem_exceptionalComponentVertices_of_mem Q W Y hx
  have hWLsupport : ∀ p ∈ WL, p.support ⊆ D := by
    intro p hp
    exact path_support_subset_exceptionalComponents_left hW.finiteCharacter
      hp.1 p.initial_mem_support hp.2
  have hYRsupport : ∀ p ∈ YR, Disjoint p.support D := by
    intro p hp
    rw [Set.disjoint_left]
    intro x hxp hxD
    exact hp.2 (path_support_subset_exceptionalComponents_right
      hY.finiteCharacter hp.1 hxp hxD p.initial_mem_support)
  change IsLinkageBetween Q A B (WL ∪ YR)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpWL | hpYR
    · rcases hq with hqWL | hqYR
      · exact hW.isWarp hpWL.1 hqWL.1 hpq
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 (hYRsupport q hqYR) hxq
          (hWLsupport p hpWL hxp)
    · rcases hq with hqWL | hqYR
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 (hYRsupport p hpYR) hxp
          (hWLsupport q hqWL hxq)
      · exact hY.isWarp hpYR.1 hqYR.1 hpq
  · intro p hp
    exact hp.elim
      (fun hpWL ↦ hW.finiteCharacter hpWL.1)
      (fun hpYR ↦ hY.finiteCharacter hpYR.1)
  · rw [Q.initialSet_union, initialSet_initialPart,
      initialSet_initialPart, hW.initialSet_eq, hY.initialSet_eq]
    ext x
    constructor
    · rintro (⟨hxA, _⟩ | ⟨⟨hxA, _hxE⟩, _⟩)
      · exact hxA
      · exact hxA
    · intro hxA
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨hxA, hxD⟩
      · refine Or.inr ⟨⟨hxA, ?_⟩, hxD⟩
        intro hxE
        exact hxD (hED hxE)
  · rw [Q.terminalFrontier_union]
    exact Set.union_subset
      (fun _ hx ↦ hW.terminalFrontier_subset
        ⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩)
      (fun _ hx ↦ hY.terminalFrontier_subset
        ⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩)
  · intro p hp
    rcases hp with hpWL | hpYR
    · exact hW.endpointPure p hpWL.1
    · obtain ⟨q, rfl, hends, hsource⟩ := hY.endpointPure p hpYR.1
      have havoidE : Disjoint q.support E :=
        (hYRsupport (.inl q) hpYR).mono_right hED
      have hsource' : q.support ∩ A = {q.start} := by
        apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA⟩
          have hxNotE : x ∉ E := by
            intro hxE
            exact Set.disjoint_left.1 havoidE hxq hxE
          have hx : x ∈ q.support ∩ (A \ E) := ⟨hxq, hxA, hxNotE⟩
          exact hsource ▸ hx
        · intro x hx
          have hx' : x ∈ q.support ∩ (A \ E) := hsource.symm ▸ hx
          exact ⟨hx'.1, hx'.2.1⟩
      have hends' : q.support ∩ (A ∪ B) = {q.start, q.finish} := by
        apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA | hxB⟩
          · have hxNotE : x ∉ E := by
              intro hxE
              exact Set.disjoint_left.1 havoidE hxq hxE
            exact hends ▸ (⟨hxq, Or.inl ⟨hxA, hxNotE⟩⟩ :
              x ∈ q.support ∩ ((A \ E) ∪ B))
          · exact hends ▸ (⟨hxq, Or.inr hxB⟩ :
              x ∈ q.support ∩ ((A \ E) ∪ B))
        · intro x hx
          have hx' : x ∈ q.support ∩ ((A \ E) ∪ B) :=
            hends.symm ▸ hx
          exact ⟨hx'.1, hx'.2.elim (fun h ↦ Or.inl h.1) Or.inr⟩
      exact ⟨q, rfl, hends', hsource'⟩

/-- The retained left subfamily is small when the seed is small. -/
theorem mk_componentMixedFamily_left_lt
    (Q : DWeb V) {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : Cardinal.aleph0 < kappa)
    {W Y : Set Q.DPath} (hW : Q.IsWarp W) (hY : Q.IsWarp Y)
    (hWfinite : Q.HasFiniteCharacter W)
    (hYfinite : Q.HasFiniteCharacter Y) {E : Set V} (hE : #E < kappa) :
    #(initialPart Q W (exceptionalComponentVertices Q W Y E)) < kappa := by
  change #(SliceSpliceSource.initialRestriction Q W
    (exceptionalComponentVertices Q W Y E)) < kappa
  apply RegularSliceComponentClosure.mk_initialRestriction_lt_of_isWarp hW
  exact mk_exceptionalComponentVertices_lt hregular huncountable
    hW hY hWfinite hYfinite hE

/-! ## Whole-component replacement at a separating cut -/

/-- Use old paths on the selected components, but only the first-hit
prefixes of the later paths on the complementary components.  Components
are deliberately computed with the *whole* later family `Y`. -/
def wholeComponentMixedFamily (Q : DWeb V) (W P Y : Set Q.DPath)
    (E : Set V) : Set Q.DPath :=
  initialPart Q W (exceptionalComponentVertices Q W Y E) ∪
    initialPart Q P (exceptionalComponentVertices Q W Y E)ᶜ

/-- Old terminals retained on the exceptional components. -/
def wholeExchangeExceptionalTerminals (Q : DWeb V)
    (W Y : Set Q.DPath) (E : Set V) : Set V :=
  Q.terminalFrontier
    (initialPart Q W (exceptionalComponentVertices Q W Y E))

private theorem firstHitPrefix_support_disjoint_exceptionalComponents
    {Q : DWeb V} {A C T E : Set V} {W Y : Set Q.DPath}
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C)
    {p : Q.DPath}
    (hp : p ∈ initialPart Q (firstHitPrefixFamily hY hsep)
      (exceptionalComponentVertices Q W Y E)ᶜ) :
    Disjoint p.support (exceptionalComponentVertices Q W Y E) := by
  obtain ⟨a, hpa⟩ := hp.1
  subst p
  rw [Set.disjoint_left]
  intro x hxp hxD
  apply hp.2
  have hwholeMem :
      (.inl (linkageFiniteAt hY a) : Q.DPath) ∈ Y := by
    rw [← linkageMemberAt_eq_finite]
    exact (linkageMemberAt hY a).2
  have hwholeD : (linkageFiniteAt hY a).support ⊆
      exceptionalComponentVertices Q W Y E :=
    path_support_subset_exceptionalComponents_right hY.finiteCharacter
      hwholeMem (linkageFirstHitAt_support_subset hY hsep a hxp) hxD
  change (linkageFirstHitAt hY hsep a).start ∈
    exceptionalComponentVertices Q W Y E
  rw [linkageFirstHitAt_start, ← linkageFiniteAt_start hY a]
  exact hwholeD (linkageFiniteAt hY a).start_mem_support

/-- Whole-component replacement by first-hit prefixes is again an exact
linkage from the original source set to the cut. -/
theorem wholeComponentMixedFamily_isLinkageBetween
    (Q : DWeb V) {A C T E : Set V} {W Y : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C)
    (hEsub : E ⊆ A) :
    IsLinkageBetween Q A C
      (wholeComponentMixedFamily Q W (firstHitPrefixFamily hY hsep) Y E) := by
  let D := exceptionalComponentVertices Q W Y E
  let P := firstHitPrefixFamily hY hsep
  let WL := initialPart Q W D
  let PR := initialPart Q P Dᶜ
  have hP : IsLinkageBetween Q (A \ E) C P :=
    firstHitPrefixFamily_isLinkageBetween hY hsep
  have hED : E ⊆ D := by
    intro x hx
    exact mem_exceptionalComponentVertices_of_mem Q W Y hx
  have hWLsupport : ∀ p ∈ WL, p.support ⊆ D := by
    intro p hp
    exact path_support_subset_exceptionalComponents_left hW.finiteCharacter
      hp.1 p.initial_mem_support hp.2
  have hPRsupport : ∀ p ∈ PR, Disjoint p.support D := by
    intro p hp
    exact firstHitPrefix_support_disjoint_exceptionalComponents hY hsep hp
  change IsLinkageBetween Q A C (WL ∪ PR)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpWL | hpPR
    · rcases hq with hqWL | hqPR
      · exact hW.isWarp hpWL.1 hqWL.1 hpq
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 (hPRsupport q hqPR) hxq
          (hWLsupport p hpWL hxp)
    · rcases hq with hqWL | hqPR
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 (hPRsupport p hpPR) hxp
          (hWLsupport q hqWL hxq)
      · exact hP.isWarp hpPR.1 hqPR.1 hpq
  · intro p hp
    exact hp.elim
      (fun hpWL ↦ hW.finiteCharacter hpWL.1)
      (fun hpPR ↦ hP.finiteCharacter hpPR.1)
  · rw [Q.initialSet_union, initialSet_initialPart,
      initialSet_initialPart, hW.initialSet_eq, hP.initialSet_eq]
    ext x
    constructor
    · rintro (⟨hxA, _⟩ | ⟨⟨hxA, _⟩, _⟩)
      · exact hxA
      · exact hxA
    · intro hxA
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨hxA, hxD⟩
      · refine Or.inr ⟨⟨hxA, ?_⟩, hxD⟩
        intro hxE
        exact hxD (hED hxE)
  · rw [Q.terminalFrontier_union]
    exact Set.union_subset
      (fun _ hx ↦ hW.terminalFrontier_subset
        ⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩)
      (fun _ hx ↦ hP.terminalFrontier_subset
        ⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩)
  · intro p hp
    rcases hp with hpWL | hpPR
    · exact hW.endpointPure p hpWL.1
    · obtain ⟨q, rfl, hends, hsource⟩ := hP.endpointPure p hpPR.1
      have havoidE : Disjoint q.support E :=
        (hPRsupport (.inl q) hpPR).mono_right hED
      have hsource' : q.support ∩ A = {q.start} := by
        apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA⟩
          have hxNotE : x ∉ E := by
            intro hxE
            exact Set.disjoint_left.1 havoidE hxq hxE
          exact hsource ▸ (⟨hxq, hxA, hxNotE⟩ :
            x ∈ q.support ∩ (A \ E))
        · intro x hx
          have hx' : x ∈ q.support ∩ (A \ E) := hsource.symm ▸ hx
          exact ⟨hx'.1, hx'.2.1⟩
      have hends' : q.support ∩ (A ∪ C) = {q.start, q.finish} := by
        apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA | hxC⟩
          · have hxNotE : x ∉ E := by
              intro hxE
              exact Set.disjoint_left.1 havoidE hxq hxE
            exact hends ▸ (⟨hxq, Or.inl ⟨hxA, hxNotE⟩⟩ :
              x ∈ q.support ∩ ((A \ E) ∪ C))
          · exact hends ▸ (⟨hxq, Or.inr hxC⟩ :
              x ∈ q.support ∩ ((A \ E) ∪ C))
        · intro x hx
          have hx' : x ∈ q.support ∩ ((A \ E) ∪ C) :=
            hends.symm ▸ hx
          exact ⟨hx'.1, hx'.2.elim (fun h ↦ Or.inl h.1) Or.inr⟩
      exact ⟨q, rfl, hends', hsource'⟩

/-- Requested sources seeded into the exceptional closure retain their old
target-linking witnesses. -/
theorem wholeComponentMixedFamily_linksToTarget
    (Q : DWeb V) {A C T E U : Set V} {W Y : Set Q.DPath}
    {hY : IsLinkageBetween Q (A \ E) T Y}
    {hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C}
    (hWfinite : Q.HasFiniteCharacter W) (hUE : U ⊆ E)
    (hlinks : LinksToTarget Q W U) :
    LinksToTarget Q
      (wholeComponentMixedFamily Q W
        (firstHitPrefixFamily hY hsep) Y E) U := by
  intro a ha
  obtain ⟨p, hpW, q, hpq, hqU, hsuffix⟩ := hlinks a ha
  have haq : a ∈ q.support := by
    have haInter : a ∈ q.support ∩ U := by
      rw [hqU]
      exact Set.mem_singleton a
    exact haInter.1
  have hap : a ∈ p.support := by
    rw [hpq]
    exact haq
  have haD : a ∈ exceptionalComponentVertices Q W Y E :=
    mem_exceptionalComponentVertices_of_mem Q W Y (hUE ha)
  have hpD : p.support ⊆ exceptionalComponentVertices Q W Y E :=
    path_support_subset_exceptionalComponents_left hWfinite hpW hap haD
  refine ⟨p, ?_, q, hpq, hqU, hsuffix⟩
  exact Or.inl ⟨hpW, hpD p.initial_mem_support⟩

/-- The old terminals retained on exceptional components form a small set. -/
theorem wholeExchangeExceptionalTerminals_small
    (Q : DWeb V) {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : Cardinal.aleph0 < kappa)
    {W Y : Set Q.DPath} (hW : Q.IsWarp W) (hY : Q.IsWarp Y)
    (hWfinite : Q.HasFiniteCharacter W)
    (hYfinite : Q.HasFiniteCharacter Y) {E : Set V} (hE : #E < kappa) :
    #(wholeExchangeExceptionalTerminals Q W Y E) < kappa := by
  let D := exceptionalComponentVertices Q W Y E
  let WL := initialPart Q W D
  let E' := Q.terminalFrontier WL
  let pick : E' → WL := fun x ↦
    ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  have hpick : Function.Injective pick := by
    intro x y hxy
    apply Subtype.ext
    have hxterm := (Classical.choose_spec x.2).2
    have hyterm := (Classical.choose_spec y.2).2
    have hpath : (pick x).1 = (pick y).1 := congrArg Subtype.val hxy
    change Classical.choose x.2 = Classical.choose y.2 at hpath
    rw [hpath] at hxterm
    exact Option.some.inj (hxterm.symm.trans hyterm)
  change #E' < kappa
  exact (Cardinal.mk_le_of_injective hpick).trans_lt
    (mk_componentMixedFamily_left_lt Q hregular huncountable
      hW hY hWfinite hYfinite hE)

/-! ## Complementary suffixes of the later linkage -/

/-- The suffix of a later linkage member beginning at its first visit to
the separating cut. -/
noncomputable def linkageSuffixAtFirstHit
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C) (a : A) :
    DirectedPath.FinitePath Q.graph :=
  (linkageFiniteAt hY a).suffixFrom
    (linkageFirstHitAt hY hsep a).finish
    (linkageFirstHitAt_support_subset hY hsep a
      (linkageFirstHitAt hY hsep a).finish_mem_support)

@[simp] theorem linkageSuffixAtFirstHit_start
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C) (a : A) :
    (linkageSuffixAtFirstHit hY hsep a).start =
      (linkageFirstHitAt hY hsep a).finish := by
  exact DirectedPath.FinitePath.suffixFrom_start _ _ _

@[simp] theorem linkageSuffixAtFirstHit_finish
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C) (a : A) :
    (linkageSuffixAtFirstHit hY hsep a).finish =
      (linkageFiniteAt hY a).finish := by
  exact DirectedPath.FinitePath.suffixFrom_finish _ _ _

theorem linkageSuffixAtFirstHit_support_subset
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C) (a : A) :
    (linkageSuffixAtFirstHit hY hsep a).support ⊆
      (linkageFiniteAt hY a).support :=
  DirectedPath.FinitePath.suffixFrom_support_subset _ _ _

theorem linkageSuffixAtFirstHit_edgeSet_subset
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C) (a : A) :
    (linkageSuffixAtFirstHit hY hsep a).edgeSet ⊆
      (linkageFiniteAt hY a).edgeSet :=
  DirectedPath.FinitePath.suffixFrom_edgeSet_subset _ _ _

/-- Later-linkage sources whose alternating component is not exceptional. -/
def wholeNonexceptionalPrefixSources
    {Q : DWeb V} {A C T E : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (_hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C)
    (W : Set Q.DPath) : Set (↑(A \ E) : Type u) :=
  {a | a.1 ∉ exceptionalComponentVertices Q W Y E}

/-- Starts of the selected complementary suffixes. -/
def selectedSuffixStartSet
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C)
    (S : Set A) : Set V :=
  Set.range fun a : S ↦ (linkageFirstHitAt hY hsep a.1).finish

/-- Family of complementary suffixes indexed by selected later sources. -/
def selectedSuffixFamily
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C)
    (S : Set A) : Set Q.DPath :=
  Set.range fun a : S ↦
    (.inl (linkageSuffixAtFirstHit hY hsep a.1) : Q.DPath)

private theorem support_inter_suffixFrom_eq_of_isPrefixOf
    {D : Digraph V} (p q : DirectedPath.FinitePath D)
    (hpq : p.IsPrefixOf q) :
    let hx : p.finish ∈ q.support :=
      hpq.support_subset p.finish_mem_support
    p.support ∩ (q.suffixFrom p.finish hx).support = {p.finish} := by
  let hx : p.finish ∈ q.support :=
    hpq.support_subset p.finish_mem_support
  change p.support ∩ (q.suffixFrom p.finish hx).support = {p.finish}
  obtain ⟨tail, htail⟩ := hpq
  have hsuffix : (q.suffixFrom p.finish hx).walk.support <:+
      q.walk.support := by
    unfold DirectedPath.FinitePath.suffixFrom
    exact (q.walk.lastHit {p.finish}
      ⟨p.finish, hx, Set.mem_singleton p.finish⟩).support_suffix
  have hdesired : p.finish :: tail <:+ q.walk.support := by
    refine ⟨p.walk.support.dropLast, ?_⟩
    calc
      p.walk.support.dropLast ++ p.finish :: tail =
          (p.walk.support.dropLast ++ [p.finish]) ++ tail := by simp
      _ = p.walk.support ++ tail := by
        have hlast := List.dropLast_append_getLast p.walk.support_ne_nil
        simpa only [p.walk.getLast_support] using
          congrArg (fun l : List V ↦ l ++ tail) hlast
      _ = q.walk.support := htail
  have hsuffixEq :
      (q.suffixFrom p.finish hx).walk.support = p.finish :: tail := by
    rcases List.suffix_total hsuffix hdesired with hsd | hds
    · apply List.Nodup.eq_of_head_mem_of_suffix
        (hne := by simp) hsd
      · change p.finish ∈ (q.suffixFrom p.finish hx).walk.support
        have hstart := (q.suffixFrom p.finish hx).start_mem_support
        change (q.suffixFrom p.finish hx).start ∈
          (q.suffixFrom p.finish hx).walk.support at hstart
        simpa only [DirectedPath.FinitePath.suffixFrom_start] using hstart
      · exact hdesired.nodup q.isPath
    · symm
      apply List.Nodup.eq_of_head_mem_of_suffix
        (hne := (q.suffixFrom p.finish hx).walk.support_ne_nil) hds
      · rw [(q.suffixFrom p.finish hx).walk.head_support,
          DirectedPath.FinitePath.suffixFrom_start]
        exact List.mem_cons_self
      · exact hsuffix.nodup q.isPath
  have hnodup : (p.walk.support ++ tail).Nodup := by
    rw [htail]
    exact q.isPath
  have hdis := (List.nodup_append.mp hnodup).2.2
  ext y
  constructor
  · rintro ⟨hyp, hyq⟩
    change y ∈ p.walk.support at hyp
    change y ∈ (q.suffixFrom p.finish hx).walk.support at hyq
    rw [hsuffixEq] at hyq
    rcases List.mem_cons.mp hyq with rfl | hytail
    · exact Set.mem_singleton p.finish
    · exact (hdis y hyp y hytail rfl).elim
  · intro hy
    have hyfinish : y = p.finish := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨p.finish_mem_support, ?_⟩
    have hstart := (q.suffixFrom p.finish hx).start_mem_support
    simpa only [DirectedPath.FinitePath.suffixFrom_start] using hstart

theorem linkageFirstHitAt_inter_suffix_eq
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C) (a : A) :
    (linkageFirstHitAt hY hsep a).support ∩
        (linkageSuffixAtFirstHit hY hsep a).support =
      {(linkageFirstHitAt hY hsep a).finish} := by
  apply support_inter_suffixFrom_eq_of_isPrefixOf
  exact ((linkageFiniteAt hY a).walk.firstHit C
    (linkageFiniteAt_meets hY hsep a)).support_prefix

/-- The selected complementary suffixes form a linkage from their first-hit
vertices to the later target. -/
theorem selectedSuffixFamily_isLinkageBetween
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C)
    (S : Set A) :
    IsLinkageBetween Q (selectedSuffixStartSet hY hsep S) T
      (selectedSuffixFamily hY hsep S) := by
  let F := selectedSuffixFamily hY hsep S
  let D := selectedSuffixStartSet hY hsep S
  have hindex_ne {a b : S} (hab : a ≠ b) : a.1 ≠ b.1 := by
    intro hab'
    exact hab (Subtype.ext hab')
  have hwhole_ne {a b : S} (hab : a ≠ b) :
      (linkageMemberAt hY a.1).1 ≠ (linkageMemberAt hY b.1).1 := by
    intro h
    exact hindex_ne hab (linkageMemberAt_injective hY (Subtype.ext h))
  have hstart_unique (a : S) {x : V}
      (hxsuffix : x ∈ (linkageSuffixAtFirstHit hY hsep a.1).support)
      (hxD : x ∈ D) :
      x = (linkageSuffixAtFirstHit hY hsep a.1).start := by
    obtain ⟨b, hxb⟩ := hxD
    by_cases hab : a = b
    · subst b
      exact hxb.symm.trans (linkageSuffixAtFirstHit_start hY hsep a.1).symm
    · have hxPrefix : x ∈ (linkageFirstHitAt hY hsep b.1).support := by
        rw [← hxb]
        exact (linkageFirstHitAt hY hsep b.1).finish_mem_support
      have hdis := hY.isWarp (linkageMemberAt hY a.1).2
        (linkageMemberAt hY b.1).2 (hwhole_ne hab)
      exact False.elim <| Set.disjoint_left.1 hdis
        (by
          rw [linkageMemberAt_eq_finite]
          exact linkageSuffixAtFirstHit_support_subset hY hsep a.1 hxsuffix)
        (by
          rw [linkageMemberAt_eq_finite]
          exact linkageFirstHitAt_support_subset hY hsep b.1 hxPrefix)
  change IsLinkageBetween Q D T F
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    have habIndex : a ≠ b := by
      intro h
      subst b
      exact hab rfl
    apply (hY.isWarp (linkageMemberAt hY a.1).2
      (linkageMemberAt hY b.1).2 (hwhole_ne habIndex)).mono
    · rw [linkageMemberAt_eq_finite]
      exact linkageSuffixAtFirstHit_support_subset hY hsep a.1
    · rw [linkageMemberAt_eq_finite]
      exact linkageSuffixAtFirstHit_support_subset hY hsep b.1
  · rintro _ ⟨a, rfl⟩
    exact ⟨linkageSuffixAtFirstHit hY hsep a.1, rfl⟩
  · ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, hx⟩
      exact ⟨a, (linkageSuffixAtFirstHit_start hY hsep a.1).symm.trans hx⟩
    · rintro ⟨a, rfl⟩
      exact ⟨.inl (linkageSuffixAtFirstHit hY hsep a.1), ⟨a, rfl⟩,
        linkageSuffixAtFirstHit_start hY hsep a.1⟩
  · rintro x ⟨_, ⟨a, rfl⟩, hx⟩
    change some (linkageSuffixAtFirstHit hY hsep a.1).finish = some x at hx
    rw [← Option.some.inj hx, linkageSuffixAtFirstHit_finish]
    exact linkageFiniteAt_finish_mem hY a.1
  · rintro _ ⟨a, rfl⟩
    let s := linkageSuffixAtFirstHit hY hsep a.1
    let f := linkageFirstHitAt hY hsep a.1
    let q := linkageFiniteAt hY a.1
    have hsSub : s.support ⊆ q.support :=
      linkageSuffixAtFirstHit_support_subset hY hsep a.1
    obtain ⟨q', hqeq, hqends, _hqsource⟩ :=
      hY.endpointPure (linkageMemberAt hY a.1).1
        (linkageMemberAt hY a.1).2
    have hq'q : q' = q := by
      apply Sum.inl.inj
      exact hqeq.symm.trans (linkageMemberAt_eq_finite hY a.1)
    subst q'
    have hTpoint {x : V} (hxs : x ∈ s.support) (hxT : x ∈ T) :
        x = s.start ∨ x = s.finish := by
      have hxEnds : x ∈ q.support ∩ (A ∪ T) :=
        ⟨hsSub hxs, Or.inr hxT⟩
      rw [hqends] at hxEnds
      rcases hxEnds with hxStart | hxFinish
      · left
        have hxf : x ∈ f.support := by
          rw [Set.mem_singleton_iff.mp hxStart]
          have hfstart : f.start = q.start :=
            (linkageFirstHitAt_start hY hsep a.1).trans
              (linkageFiniteAt_start hY a.1).symm
          rw [← hfstart]
          exact f.start_mem_support
        have hxInter : x ∈ f.support ∩ s.support := ⟨hxf, hxs⟩
        rw [linkageFirstHitAt_inter_suffix_eq hY hsep a.1] at hxInter
        exact (Set.mem_singleton_iff.mp hxInter).trans
          (linkageSuffixAtFirstHit_start hY hsep a.1).symm
      · right
        exact (Set.mem_singleton_iff.mp hxFinish).trans
          (linkageSuffixAtFirstHit_finish hY hsep a.1).symm
    have hsource : s.support ∩ D = {s.start} := by
      apply Set.Subset.antisymm
      · rintro x ⟨hxs, hxD⟩
        exact Set.mem_singleton_iff.mpr (hstart_unique a hxs hxD)
      · intro x hx
        have hxStart : x = s.start := Set.mem_singleton_iff.mp hx
        subst x
        refine ⟨s.start_mem_support, ?_⟩
        exact ⟨a, (linkageSuffixAtFirstHit_start hY hsep a.1).symm⟩
    have hends : s.support ∩ (D ∪ T) = {s.start, s.finish} := by
      apply Set.Subset.antisymm
      · rintro x ⟨hxs, hxD | hxT⟩
        · exact Or.inl (hstart_unique a hxs hxD)
        · exact hTpoint hxs hxT
      · intro x hx
        rcases hx with hxStart | hxFinish
        · subst x
          exact ⟨s.start_mem_support, Or.inl
            ⟨a, (linkageSuffixAtFirstHit_start hY hsep a.1).symm⟩⟩
        · subst x
          refine ⟨s.finish_mem_support, Or.inr ?_⟩
          rw [linkageSuffixAtFirstHit_finish]
          exact linkageFiniteAt_finish_mem hY a.1
    exact ⟨s, rfl, hends, hsource⟩

/-- Tightness of the whole later linkage passes to every selected suffix. -/
theorem selectedSuffixFamily_meetsOnlyAtTerminal
    {Q : DWeb V} {A C T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y)
    (hYtight : SliceSpliceSource.MeetsOnlyAtTerminal Q Y T)
    (hsep : RelationalRoof.Separates Q.graph.Adj A T C)
    (S : Set A) :
    SliceSpliceSource.MeetsOnlyAtTerminal Q
      (selectedSuffixFamily hY hsep S) T := by
  rintro _ ⟨a, rfl⟩ x hxs hxT
  have hwholeMem : (.inl (linkageFiniteAt hY a.1) : Q.DPath) ∈ Y := by
    rw [← linkageMemberAt_eq_finite]
    exact (linkageMemberAt hY a.1).2
  have hterm := hYtight (.inl (linkageFiniteAt hY a.1)) hwholeMem x
    (linkageSuffixAtFirstHit_support_subset hY hsep a.1 hxs) hxT
  change some (linkageFiniteAt hY a.1).finish = some x at hterm
  change some (linkageSuffixAtFirstHit hY hsep a.1).finish = some x
  simpa only [linkageSuffixAtFirstHit_finish] using hterm

/-- Removing the exceptional old terminals from the mixed terminal frontier
leaves exactly the terminal frontier of the complementary prefix part. -/
theorem terminalFrontier_wholeMixed_sdiff_exceptional_eq
    (Q : DWeb V) {A C T E : Set V} {W Y : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C) :
    Q.terminalFrontier
        (wholeComponentMixedFamily Q W (firstHitPrefixFamily hY hsep) Y E) \
      wholeExchangeExceptionalTerminals Q W Y E =
    Q.terminalFrontier
      (initialPart Q (firstHitPrefixFamily hY hsep)
        (exceptionalComponentVertices Q W Y E)ᶜ) := by
  let D := exceptionalComponentVertices Q W Y E
  let P := firstHitPrefixFamily hY hsep
  let WL := initialPart Q W D
  let PR := initialPart Q P Dᶜ
  have hWLsupport : ∀ p ∈ WL, p.support ⊆ D := by
    intro p hp
    exact path_support_subset_exceptionalComponents_left hW.finiteCharacter
      hp.1 p.initial_mem_support hp.2
  have hPRsupport : ∀ p ∈ PR, Disjoint p.support D := by
    intro p hp
    exact firstHitPrefix_support_disjoint_exceptionalComponents hY hsep hp
  change Q.terminalFrontier (WL ∪ PR) \ Q.terminalFrontier WL =
    Q.terminalFrontier PR
  rw [Q.terminalFrontier_union]
  ext x
  constructor
  · rintro ⟨hxWL | hxPR, hxNotWL⟩
    · exact False.elim (hxNotWL hxWL)
    · exact hxPR
  · intro hxPR
    refine ⟨Or.inr hxPR, ?_⟩
    intro hxWL
    obtain ⟨p, hpWL, hpx⟩ := hxWL
    obtain ⟨q, hqPR, hqx⟩ := hxPR
    have hxD : x ∈ D :=
      hWLsupport p hpWL (Q.terminal_mem_support hpx)
    exact Set.disjoint_left.1 (hPRsupport q hqPR)
      (Q.terminal_mem_support hqx) hxD

/-- The complementary prefix terminals are precisely the selected suffix
starts. -/
theorem terminalFrontier_wholeNonexceptionalPrefix_eq_suffixStartSet
    {Q : DWeb V} {A C T E : Set V} {W Y : Set Q.DPath}
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C) :
    Q.terminalFrontier
        (initialPart Q (firstHitPrefixFamily hY hsep)
          (exceptionalComponentVertices Q W Y E)ᶜ) =
      selectedSuffixStartSet hY hsep
        (wholeNonexceptionalPrefixSources hY hsep W) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    obtain ⟨a, hpa⟩ := hp.1
    subst p
    change some (linkageFirstHitAt hY hsep a).finish = some x at hpx
    have hax : (linkageFirstHitAt hY hsep a).finish = x :=
      Option.some.inj hpx
    let a' : wholeNonexceptionalPrefixSources hY hsep W :=
      ⟨a, by
        change a.1 ∉ exceptionalComponentVertices Q W Y E
        have hpNot := hp.2
        change (linkageFirstHitAt hY hsep a).start ∉
          exceptionalComponentVertices Q W Y E at hpNot
        simpa only [linkageFirstHitAt_start hY hsep a] using hpNot⟩
    exact ⟨a', by simpa only [a'] using hax⟩
  · rintro ⟨a, hax⟩
    let p : Q.DPath := .inl (linkageFirstHitAt hY hsep a.1)
    refine ⟨p, ?_, ?_⟩
    · refine ⟨⟨a.1, rfl⟩, ?_⟩
      change (linkageFirstHitAt hY hsep a.1).start ∉
        exceptionalComponentVertices Q W Y E
      have haNot : a.1.1 ∉ exceptionalComponentVertices Q W Y E := by
        have ha := a.2
        change a.1 ∈ wholeNonexceptionalPrefixSources hY hsep W at ha
        exact ha
      simpa only [linkageFirstHitAt_start hY hsep a.1] using haNot
    · change some (linkageFirstHitAt hY hsep a.1).finish = some x
      exact congrArg some hax

/-- The stopped mixed row and its selected suffix family can be spliced: an
intersection can occur only at the matching first-hit vertex. -/
theorem wholeComponentExchange_starCompatible
    (Q : DWeb V) {A C T E : Set V} {W Y : Set Q.DPath}
    (hW : IsLinkageBetween Q A C W)
    (hY : IsLinkageBetween Q (A \ E) T Y)
    (hsep : RelationalRoof.Separates Q.graph.Adj (A \ E) T C) :
    Q.StarCompatible
      (wholeComponentMixedFamily Q W (firstHitPrefixFamily hY hsep) Y E)
      (selectedSuffixFamily hY hsep
        (wholeNonexceptionalPrefixSources hY hsep W)) := by
  let D := exceptionalComponentVertices Q W Y E
  let P := firstHitPrefixFamily hY hsep
  let S := wholeNonexceptionalPrefixSources hY hsep W
  intro p hp q hq x hxp hxq
  obtain ⟨a, hqa⟩ := hq
  subst q
  rcases hp with hpOld | hpPrefix
  · have hxD : x ∈ D :=
      path_support_subset_exceptionalComponents_left hW.finiteCharacter
        hpOld.1 p.initial_mem_support hpOld.2 hxp
    have hwholeMem :
        (.inl (linkageFiniteAt hY a.1) : Q.DPath) ∈ Y := by
      rw [← linkageMemberAt_eq_finite]
      exact (linkageMemberAt hY a.1).2
    have hxWhole : x ∈ (linkageFiniteAt hY a.1).support :=
      linkageSuffixAtFirstHit_support_subset hY hsep a.1 hxq
    have hwholeD : (linkageFiniteAt hY a.1).support ⊆ D :=
      path_support_subset_exceptionalComponents_right hY.finiteCharacter
        hwholeMem hxWhole hxD
    have haD : a.1.1 ∈ D := by
      rw [← linkageFiniteAt_start hY a.1]
      exact hwholeD (linkageFiniteAt hY a.1).start_mem_support
    have haNot : a.1.1 ∉ D := by
      have ha := a.2
      change a.1 ∈ S at ha
      exact ha
    exact False.elim (haNot haD)
  · obtain ⟨b, rfl⟩ := hpPrefix.1
    have hxpPrefix : x ∈ (linkageFirstHitAt hY hsep b).support := hxp
    have hba : b = a.1 := by
      by_contra hne
      have hmemberNe : (linkageMemberAt hY b).1 ≠
          (linkageMemberAt hY a.1).1 := by
        intro heq
        apply hne
        exact linkageMemberAt_injective hY (Subtype.ext heq)
      exact False.elim <| Set.disjoint_left.1
        (hY.isWarp (linkageMemberAt hY b).2
          (linkageMemberAt hY a.1).2 hmemberNe)
        (by
          rw [linkageMemberAt_eq_finite]
          exact linkageFirstHitAt_support_subset hY hsep b hxpPrefix)
        (by
          rw [linkageMemberAt_eq_finite]
          exact linkageSuffixAtFirstHit_support_subset hY hsep a.1 hxq)
    subst b
    have hxInter : x ∈ (linkageFirstHitAt hY hsep a.1).support ∩
        (linkageSuffixAtFirstHit hY hsep a.1).support :=
      ⟨hxpPrefix, hxq⟩
    rw [linkageFirstHitAt_inter_suffix_eq hY hsep a.1] at hxInter
    have hxEq : x = (linkageFirstHitAt hY hsep a.1).finish :=
      Set.mem_singleton_iff.mp hxInter
    constructor
    · change some (linkageFirstHitAt hY hsep a.1).finish = some x
      exact congrArg some hxEq.symm
    · change (linkageSuffixAtFirstHit hY hsep a.1).start = x
      exact (linkageSuffixAtFirstHit_start hY hsep a.1).trans hxEq.symm

/-! ## First-hit tightening of ordinary limiting-warp segments -/

/-- A family is tight at its right boundary when every visit to that
boundary is already the terminal vertex.  This clause matters when two
ladder frontiers overlap: endpoint purity alone allows the initial vertex
to belong to both frontiers. -/
abbrev RightBoundaryTight (Gamma : DWeb V) (T : Set Gamma.DPath)
    (B : Set V) : Prop :=
  SliceSpliceSource.MeetsOnlyAtTerminal Gamma T B

/-- Every realized segment meets its declared right boundary at least at
its finish. -/
theorem segmentTargetMeet
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SliceSegmentCore.SegmentRealization Gamma Y A C S) (x : S) :
    (R.segment x).walk.Meets C :=
  ⟨(R.segment x).finish, (R.segment x).finish_mem_support,
    R.segment_finish_mem x⟩

/-- Cut an ordinary realized segment at its first visit to the right
boundary.  In particular, if its source already lies on that boundary,
the tightened segment is the trivial path there. -/
noncomputable def firstHitSegment
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SliceSegmentCore.SegmentRealization Gamma Y A C S) (x : S) :
    DirectedPath.FinitePath Gamma.graph :=
  (R.segment x).firstHit C (segmentTargetMeet R x)

@[simp]
theorem firstHitSegment_start
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SliceSegmentCore.SegmentRealization Gamma Y A C S) (x : S) :
    (firstHitSegment R x).start = x.1 := by
  exact R.segment_start x

@[simp]
theorem firstHitSegment_finish_mem
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SliceSegmentCore.SegmentRealization Gamma Y A C S) (x : S) :
    (firstHitSegment R x).finish ∈ C :=
  DirectedPath.FinitePath.firstHit_finish_mem _ _ _

theorem firstHitSegment_support_subset
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SliceSegmentCore.SegmentRealization Gamma Y A C S) (x : S) :
    (firstHitSegment R x).support ⊆ (R.segment x).support :=
  DirectedPath.FinitePath.firstHit_support_subset _ _ _

/-- First-hit truncation meets the right boundary only at its finish. -/
theorem firstHitSegment_target_pure
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SliceSegmentCore.SegmentRealization Gamma Y A C S) (x : S) :
    (firstHitSegment R x).support ∩ C =
      {(firstHitSegment R x).finish} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hy, hyC⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hyFinish
    have hlast :
        (firstHitSegment R x).walk.support.getLast
            (firstHitSegment R x).walk.support_ne_nil =
          (firstHitSegment R x).finish :=
      (firstHitSegment R x).walk.getLast_support
    have hyLast : y ≠ (firstHitSegment R x).walk.support.getLast
        (firstHitSegment R x).walk.support_ne_nil := by
      intro h
      exact hyFinish (h.trans hlast)
    exact DirectedPath.FinitePath.firstHit_no_mem_before
      (R.segment x) C (segmentTargetMeet R x)
      (List.mem_dropLast_of_mem_of_ne_getLast hy hyLast) hyC
  · intro y hy
    have hyFinish : y = (firstHitSegment R x).finish :=
      Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨( firstHitSegment R x).finish_mem_support,
      firstHitSegment_finish_mem R x⟩

/-- First-hit tightening preserves the realization axioms while adding the
missing right-boundary geometry. -/
noncomputable def tightenSegmentRealization
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SliceSegmentCore.SegmentRealization Gamma Y A C S) :
    SliceSegmentCore.SegmentRealization Gamma Y A C S where
  source_subset := R.source_subset
  carrier := R.carrier
  carrier_mem := R.carrier_mem
  carrier_injective := R.carrier_injective
  segment := firstHitSegment R
  segment_start := firstHitSegment_start R
  segment_finish_mem := firstHitSegment_finish_mem R
  segment_subpath x := by
    refine ⟨(firstHitSegment_support_subset R x).trans
        (R.segment_subpath x).1, ?_⟩
    exact (DirectedPath.FinitePath.firstHit_edgeSet_subset _ _ _).trans
      (R.segment_subpath x).2
  segment_endpoints x := by
    apply Set.Subset.antisymm
    · rintro y ⟨hy, hyA | hyC⟩
      · have hyOld : y ∈ (R.segment x).support ∩ A :=
          ⟨firstHitSegment_support_subset R x hy, hyA⟩
        rw [R.segment_source x] at hyOld
        have hyStart : y = (firstHitSegment R x).start := by
          calc
            y = (R.segment x).start := Set.mem_singleton_iff.mp hyOld
            _ = x.1 := R.segment_start x
            _ = (firstHitSegment R x).start :=
              (firstHitSegment_start R x).symm
        exact Set.mem_insert_iff.mpr (Or.inl hyStart)
      · have hyFinish : y = (firstHitSegment R x).finish := by
          have hy' : y ∈ (firstHitSegment R x).support ∩ C := ⟨hy, hyC⟩
          rw [firstHitSegment_target_pure R x] at hy'
          exact Set.mem_singleton_iff.mp hy'
        exact Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mpr hyFinish))
    · intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨(firstHitSegment R x).start_mem_support,
          Or.inl (firstHitSegment_start R x ▸ R.source_subset x.2)⟩
      · exact ⟨(firstHitSegment R x).finish_mem_support,
          Or.inr (firstHitSegment_finish_mem R x)⟩
  segment_source x := by
    apply Set.Subset.antisymm
    · rintro y ⟨hy, hyA⟩
      have hyOld : y ∈ (R.segment x).support ∩ A :=
        ⟨firstHitSegment_support_subset R x hy, hyA⟩
      rw [R.segment_source x] at hyOld
      exact Set.mem_singleton_iff.mpr
        (calc
          y = (R.segment x).start := Set.mem_singleton_iff.mp hyOld
          _ = x.1 := R.segment_start x
          _ = (firstHitSegment R x).start :=
            (firstHitSegment_start R x).symm)
    · intro y hy
      have hyStart : y = (firstHitSegment R x).start :=
        Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨(firstHitSegment R x).start_mem_support,
        firstHitSegment_start R x ▸ R.source_subset x.2⟩

/-- The ordinary family produced by the tightened realization satisfies
the right-boundary invariant needed by the splice recursion. -/
theorem segmentFamily_tighten_rightBoundaryTight
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {A C S : Set V}
    (R : SliceSegmentCore.SegmentRealization Gamma Y A C S) :
    RightBoundaryTight Gamma
      (SliceSegmentCore.segmentFamily (tightenSegmentRealization R)) C := by
  rintro q ⟨x, rfl⟩ y hy hyC
  have hy' : y ∈ (firstHitSegment R x).support ∩ C := ⟨hy, hyC⟩
  rw [firstHitSegment_target_pure R x] at hy'
  have hyFinish : y = (firstHitSegment R x).finish :=
    Set.mem_singleton_iff.mp hy'
  exact congrArg some hyFinish.symm

/-! ### Tightening the exceptional remainder -/

theorem exceptionalTargetMeet
    {Gamma : DWeb V} {A C S : Set V}
    (R : SliceSegmentCore.ExceptionalRealization Gamma A C S) (x : S) :
    (R.path x).walk.Meets C :=
  ⟨(R.path x).finish, (R.path x).finish_mem_support,
    R.path_finish_mem x⟩

/-- The first-right-boundary prefix of an exceptional path. -/
noncomputable def firstHitExceptionalPath
    {Gamma : DWeb V} {A C S : Set V}
    (R : SliceSegmentCore.ExceptionalRealization Gamma A C S) (x : S) :
    DirectedPath.FinitePath Gamma.graph :=
  (R.path x).firstHit C (exceptionalTargetMeet R x)

@[simp]
theorem firstHitExceptionalPath_start
    {Gamma : DWeb V} {A C S : Set V}
    (R : SliceSegmentCore.ExceptionalRealization Gamma A C S) (x : S) :
    (firstHitExceptionalPath R x).start = x.1 :=
  R.path_start x

@[simp]
theorem firstHitExceptionalPath_finish_mem
    {Gamma : DWeb V} {A C S : Set V}
    (R : SliceSegmentCore.ExceptionalRealization Gamma A C S) (x : S) :
    (firstHitExceptionalPath R x).finish ∈ C :=
  DirectedPath.FinitePath.firstHit_finish_mem _ _ _

theorem firstHitExceptionalPath_support_subset
    {Gamma : DWeb V} {A C S : Set V}
    (R : SliceSegmentCore.ExceptionalRealization Gamma A C S) (x : S) :
    (firstHitExceptionalPath R x).support ⊆ (R.path x).support :=
  DirectedPath.FinitePath.firstHit_support_subset _ _ _

theorem firstHitExceptionalPath_target_pure
    {Gamma : DWeb V} {A C S : Set V}
    (R : SliceSegmentCore.ExceptionalRealization Gamma A C S) (x : S) :
    (firstHitExceptionalPath R x).support ∩ C =
      {(firstHitExceptionalPath R x).finish} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hy, hyC⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hyFinish
    have hlast :
        (firstHitExceptionalPath R x).walk.support.getLast
            (firstHitExceptionalPath R x).walk.support_ne_nil =
          (firstHitExceptionalPath R x).finish :=
      (firstHitExceptionalPath R x).walk.getLast_support
    have hyLast : y ≠
        (firstHitExceptionalPath R x).walk.support.getLast
          (firstHitExceptionalPath R x).walk.support_ne_nil := by
      intro h
      exact hyFinish (h.trans hlast)
    exact DirectedPath.FinitePath.firstHit_no_mem_before
      (R.path x) C (exceptionalTargetMeet R x)
      (List.mem_dropLast_of_mem_of_ne_getLast hy hyLast) hyC
  · intro y hy
    have hyFinish : y = (firstHitExceptionalPath R x).finish :=
      Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨(firstHitExceptionalPath R x).finish_mem_support,
      firstHitExceptionalPath_finish_mem R x⟩

/-- First-hit tightening of every exceptional path.  This is a concrete
construction, not an exceptional-realization premise. -/
noncomputable def tightenExceptionalRealization
    {Gamma : DWeb V} {A C S : Set V}
    (R : SliceSegmentCore.ExceptionalRealization Gamma A C S) :
    SliceSegmentCore.ExceptionalRealization Gamma A C S where
  path := firstHitExceptionalPath R
  path_start := firstHitExceptionalPath_start R
  path_finish_mem := firstHitExceptionalPath_finish_mem R
  endpointPure x := by
    apply Set.Subset.antisymm
    · rintro y ⟨hy, hyA | hyC⟩
      · have hyOld : y ∈ (R.path x).support ∩ A :=
          ⟨firstHitExceptionalPath_support_subset R x hy, hyA⟩
        have hyStartOld : y = (R.path x).start := by
          have hyEnds : y ∈ (R.path x).support ∩ (A ∪ C) :=
            ⟨hyOld.1, Or.inl hyA⟩
          rw [R.endpointPure x] at hyEnds
          rcases Set.mem_insert_iff.mp hyEnds with h | h
          · exact h
          · have hyFinish : y = (R.path x).finish :=
              Set.mem_singleton_iff.mp h
            have hsource := R.sourcePure x
            rw [hsource] at hyOld
            exact Set.mem_singleton_iff.mp hyOld
        have hyStart : y = (firstHitExceptionalPath R x).start := by
          calc
            y = (R.path x).start := hyStartOld
            _ = x.1 := R.path_start x
            _ = (firstHitExceptionalPath R x).start :=
              (firstHitExceptionalPath_start R x).symm
        exact Set.mem_insert_iff.mpr (Or.inl hyStart)
      · have hy' : y ∈
            (firstHitExceptionalPath R x).support ∩ C := ⟨hy, hyC⟩
        rw [firstHitExceptionalPath_target_pure R x] at hy'
        exact Set.mem_insert_iff.mpr (Or.inr hy')
    · intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · have hstartInter :
            (R.path x).start ∈ (R.path x).support ∩ A := by
          rw [R.sourcePure x]
          exact Set.mem_singleton (R.path x).start
        have hxA : x.1 ∈ A := by
          rw [R.path_start x] at hstartInter
          exact hstartInter.2
        exact ⟨(firstHitExceptionalPath R x).start_mem_support,
          Or.inl (firstHitExceptionalPath_start R x ▸ hxA)⟩
      · exact ⟨(firstHitExceptionalPath R x).finish_mem_support,
          Or.inr (firstHitExceptionalPath_finish_mem R x)⟩
  sourcePure x := by
    apply Set.Subset.antisymm
    · rintro y ⟨hy, hyA⟩
      have hyOld : y ∈ (R.path x).support ∩ A :=
        ⟨firstHitExceptionalPath_support_subset R x hy, hyA⟩
      rw [R.sourcePure x] at hyOld
      have hyStartOld : y = (R.path x).start :=
        Set.mem_singleton_iff.mp hyOld
      exact Set.mem_singleton_iff.mpr (calc
        y = (R.path x).start := hyStartOld
        _ = x.1 := R.path_start x
        _ = (firstHitExceptionalPath R x).start :=
          (firstHitExceptionalPath_start R x).symm)
    · intro y hy
      have hyStart : y = (firstHitExceptionalPath R x).start :=
        Set.mem_singleton_iff.mp hy
      subst y
      have hxA : x.1 ∈ A := by
        have hstartInter :
            (R.path x).start ∈ (R.path x).support ∩ A := by
          rw [R.sourcePure x]
          exact Set.mem_singleton (R.path x).start
        rw [R.path_start x] at hstartInter
        exact hstartInter.2
      exact ⟨(firstHitExceptionalPath R x).start_mem_support,
        firstHitExceptionalPath_start R x ▸ hxA⟩
  pairwise_disjoint x y hxy :=
    (R.pairwise_disjoint x y hxy).mono
      (firstHitExceptionalPath_support_subset R x)
      (firstHitExceptionalPath_support_subset R y)

theorem exceptionalFamily_tighten_rightBoundaryTight
    {Gamma : DWeb V} {A C S : Set V}
    (R : SliceSegmentCore.ExceptionalRealization Gamma A C S) :
    RightBoundaryTight Gamma
      (SliceSegmentCore.exceptionalFamily
        (tightenExceptionalRealization R)) C := by
  rintro q ⟨x, rfl⟩ y hy hyC
  have hy' : y ∈ (firstHitExceptionalPath R x).support ∩ C := ⟨hy, hyC⟩
  rw [firstHitExceptionalPath_target_pure R x] at hy'
  exact congrArg some (Set.mem_singleton_iff.mp hy').symm

theorem RightBoundaryTight.union
    {Gamma : DWeb V} {T E : Set Gamma.DPath} {C : Set V}
    (hT : RightBoundaryTight Gamma T C)
    (hE : RightBoundaryTight Gamma E C) :
    RightBoundaryTight Gamma (T ∪ E) C := by
  intro q hq
  exact hq.elim (hT q) (hE q)

/-! ## Ordered owner provenance for ordinary members -/

/-- An ordinary slice member together with its unique limiting-warp owner.
`FinitePath.IsSubpathOf` records both vertices and directed edges; since
both paths are simple, this is precisely an ordered interval of the owner.
The two purity equalities say that the interval runs between the declared
frontier hits, rather than merely having its carrier inside the owner. -/
def IsOwnedFrontierSegment
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (A B : Set V)
    (p : Gamma.DPath) : Prop :=
  ∃ finite : DirectedPath.FinitePath Gamma.graph,
    p = .inl finite ∧
    ∃ owner : Gamma.DPath,
      owner ∈ Y ∧ finite.IsSubpathOf owner ∧
      finite.start ∈ A ∧ finite.finish ∈ B ∧
      finite.support ∩ A = {finite.start} ∧
      finite.support ∩ B = {finite.finish} ∧
      ∀ q ∈ Y, finite.IsSubpathOf q → q = owner

/-- Every member declared ordinary has explicit ordered owner provenance.
Mavericks are deliberately excluded by the `IsLadderFragment` premise. -/
def HasOwnedOrdinarySegments
    (Gamma : DWeb V) (Y T : Set Gamma.DPath) (A B : Set V) : Prop :=
  ∀ p ∈ T, IsLadderFragment Gamma Y p →
    IsOwnedFrontierSegment Gamma Y A B p

/-- A right-tight linkage whose ordinary members lie on a warp has the
unique-owner property.  Uniqueness uses a support vertex of the nonempty
finite interval and pairwise disjointness of the owner warp. -/
theorem hasOwnedOrdinarySegments_of_tightLinkage
    {Gamma : DWeb V} {Y T : Set Gamma.DPath} {A B : Set V}
    (hY : Gamma.IsWarp Y)
    (hT : IsLinkageBetween Gamma A B T)
    (htight : RightBoundaryTight Gamma T B) :
    HasOwnedOrdinarySegments Gamma Y T A B := by
  intro p hpT hpordinary
  obtain ⟨f, rfl⟩ := hT.2.1 hpT
  obtain ⟨owner, hownerY, hfowner⟩ := hpordinary
  have hstartA : f.start ∈ A := by
    rw [← hT.2.2.1]
    exact ⟨.inl f, hpT, rfl⟩
  have hfinishB : f.finish ∈ B := by
    apply hT.2.2.2.1
    exact ⟨.inl f, hpT, rfl⟩
  obtain ⟨g, hgf, _hendpoints, hgsource⟩ := hT.2.2.2.2 _ hpT
  have hfg : f = g := Sum.inl.inj hgf
  subst g
  refine ⟨f, rfl, owner, hownerY, hfowner, hstartA, hfinishB,
    hgsource, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxB⟩
      have hterminal : some f.finish = some x :=
        htight (.inl f) hpT x hxf hxB
      exact Set.mem_singleton_iff.mpr (Option.some.inj hterminal).symm
    · intro x hx
      have hxf : x = f.finish := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨f.finish_mem_support, hfinishB⟩
  · intro q hqY hfq
    by_contra hqowner
    have hdisjoint := hY hqY hownerY hqowner
    exact Set.disjoint_left.1 hdisjoint
      (hfq.1 f.start_mem_support) (hfowner.1 f.start_mem_support)

/-- Tight annularity supplies the linkage and right-boundary hypotheses of
the owner-provenance constructor. -/
theorem hasOwnedOrdinarySegments_of_tightAnnularSlice
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hY : Gamma.IsWarp L.limitWarp)
    (hT : SliceSpliceSource.IsTightAnnularSlice
      Gamma L T alpha beta U) :
    HasOwnedOrdinarySegments Gamma L.limitWarp T
      (L.frontier alpha) (L.frontier beta) :=
  hasOwnedOrdinarySegments_of_tightLinkage hY hT.1.1.1 hT.2

/-! ### Causal, stage-local interval provenance -/

/-- Exact source-faithful provenance of one ordinary slice member.  The
member is literally the interval which appends the canonical finite
component at `delta` to the canonical finite component at `beta`.

All objects mentioned here belong to `warpAt delta`, `warpAt beta`, or the
two frontiers.  In particular no final `limitWarp` occurs, so this predicate
can be evaluated by the causal row recursion. -/
def IsStageInterval
    {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa) (delta beta : Ladder.Stage kappa)
    (p : Gamma.DPath) : Prop :=
  ∃ (left right segment : DirectedPath.FinitePath Gamma.graph),
    p = .inl segment ∧
    (Sum.inl left : Gamma.DPath) ∈
      Gamma.essentialWarpPart (L.warpAt delta) ∧
    (Sum.inl right : Gamma.DPath) ∈
      Gamma.essentialWarpPart (L.warpAt beta) ∧
    left.finish ∈ L.frontier delta ∧
    right.finish ∈ L.frontier beta ∧
    ∃ hstart : DirectedPath.Path.initial
        (Sum.inl segment : Gamma.DPath) = left.finish,
      ∃ hinter : left.support ∩ segment.support ⊆ {left.finish},
        left.support ∩ segment.support = {left.finish} ∧
        DirectedPath.Path.appendFinite left (.inl segment) hstart hinter =
          (.inl right : Gamma.DPath)

/-- Every member ordinary relative to the available `beta`-stage warp has
an exact pair of stage prefixes.  This is the causal table invariant; the
later legal-ladder transfer supplies the unique final-warp owner. -/
def HasStageIntervalSegments
    {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa) (T : Set Gamma.DPath)
    (delta beta : Ladder.Stage kappa) : Prop :=
  ∀ p ∈ T, IsLadderFragment Gamma (L.warpAt beta) p →
    IsStageInterval Gamma L delta beta p

/-- Realization-level data which constructs, rather than postulates, the
exact stage-prefix invariant.  This is deliberately local: the final slice
existence theorem must build such a realization from the limiting-warp
component replacement. -/
structure StageIntervalRealization
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (delta beta : Ladder.Stage kappa)
    (S : Set V)
    extends SliceSegmentCore.SegmentRealization Gamma (L.warpAt beta)
      (L.frontier delta) (L.frontier beta) S where
  leftPrefix : S → DirectedPath.FinitePath Gamma.graph
  rightPrefix : S → DirectedPath.FinitePath Gamma.graph
  left_mem : ∀ x, (Sum.inl (leftPrefix x) : Gamma.DPath) ∈
    Gamma.essentialWarpPart (L.warpAt delta)
  right_mem : ∀ x, (Sum.inl (rightPrefix x) : Gamma.DPath) ∈
    Gamma.essentialWarpPart (L.warpAt beta)
  left_finish : ∀ x, (leftPrefix x).finish = x.1
  right_finish : ∀ x,
    (rightPrefix x).finish = (toSegmentRealization.segment x).finish
  prefix_inter : ∀ x,
    (leftPrefix x).support ∩ (toSegmentRealization.segment x).support =
      {(leftPrefix x).finish}
  append_eq : ∀ x,
    DirectedPath.Path.appendFinite (leftPrefix x)
      (.inl (toSegmentRealization.segment x))
      (toSegmentRealization.segment_start x |>.trans (left_finish x).symm)
      (prefix_inter x).subset =
        (.inl (rightPrefix x) : Gamma.DPath)

/-- The empty ordinary component family always has a stage-interval
realization.  This is the degenerate component-replacement branch: all
members of the eventual slice are exceptional, so there are no ladder
segments or prefix-append identities to construct.

Keeping this constructor explicit is useful in the small-frontier branch,
where a full frontier linkage may be treated as the exceptional remainder.
It also isolates the genuinely geometric obligation in the general slice
lemma: only the nonempty ordinary source set requires extracting compatible
prefix intervals from two ladder stages. -/
noncomputable def emptyStageIntervalRealization
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (delta beta : Ladder.Stage kappa) :
    StageIntervalRealization L delta beta (∅ : Set V) where
  source_subset := Set.empty_subset _
  carrier x := x.2.elim
  carrier_mem x := x.2.elim
  carrier_injective x := x.2.elim
  segment x := x.2.elim
  segment_start x := x.2.elim
  segment_finish_mem x := x.2.elim
  segment_subpath x := x.2.elim
  segment_endpoints x := x.2.elim
  segment_source x := x.2.elim
  leftPrefix x := x.2.elim
  rightPrefix x := x.2.elim
  left_mem x := x.2.elim
  right_mem x := x.2.elim
  left_finish x := x.2.elim
  right_finish x := x.2.elim
  prefix_inter x := x.2.elim
  append_eq x := x.2.elim

/-- The segment family of a stage-interval realization exposes the exact
prefix append equality coordinatewise. -/
theorem segmentFamily_hasStageIntervalSegments
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S) :
    HasStageIntervalSegments Gamma L
      (SliceSegmentCore.segmentFamily R.toSegmentRealization) delta beta := by
  intro p hp _hpordinary
  obtain ⟨x, rfl⟩ := hp
  refine ⟨R.leftPrefix x, R.rightPrefix x,
    R.toSegmentRealization.segment x, rfl, R.left_mem x, R.right_mem x,
    ?_, ?_, ?_⟩
  · rw [R.left_finish x]
    exact R.toSegmentRealization.source_subset x.2
  · rw [R.right_finish x]
    exact R.toSegmentRealization.segment_finish_mem x
  · refine ⟨?_, (R.prefix_inter x).subset,
      R.prefix_inter x, R.append_eq x⟩
    exact R.toSegmentRealization.segment_start x |>.trans
      (R.left_finish x).symm

/-- The full local geometry needed by iterative source-star splicing. -/
abbrev IsTightAnnularSlice {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa) (T : Set Gamma.DPath)
    (alpha beta : Ladder.Stage kappa) (U : Set V) : Prop :=
  SliceSpliceSource.IsTightAnnularSlice Gamma L T alpha beta U

/-- Controlled-slice interface which retains right-boundary tightness. -/
def HasTightAnnularControlledSlices
    {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa) (C : Set (Ladder.Stage kappa))
    (Z : Set V) : Prop :=
  RegularCardinal.HasControlledSlices C L.frontier Z
    (IsTightAnnularSlice Gamma L)
    (sliceMavericks Gamma L.limitWarp)
    (fun p : Gamma.DPath ↦ p.support)

/-- Controlled-slice payload retaining the causal candidate information.
Besides ordinary limit-warp control, it exposes the literal stage-prefix
intervals and the small, already registered stage-relative exceptional
family used by the source scheduler. -/
def IsTrackedTightAnnularControlledSlice
    {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa) (Z : Set V)
    (alpha beta : Ladder.Stage kappa) (U : Set V)
    (T : Set Gamma.DPath) : Prop :=
  RegularCardinal.IsControlledSlice
      (IsTightAnnularSlice Gamma L)
      (sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T ∧
    HasStageIntervalSegments Gamma L T alpha beta ∧
    #(sliceMavericks Gamma (L.warpAt beta) T) < kappa ∧
    Gamma.vertexSet (sliceMavericks Gamma (L.warpAt beta) T) ⊆ Z

def HasTrackedTightAnnularControlledSlices
    {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa) (C : Set (Ladder.Stage kappa))
    (Z : Set V) : Prop :=
  ∀ alpha ∈ C, ∀ U : Set V,
    U ⊆ L.frontier alpha ∩ Z → #U < kappa →
      ∃ beta ∈ C, alpha < beta ∧ ∃ T,
        IsTrackedTightAnnularControlledSlice Gamma L Z alpha beta U T

theorem IsTrackedTightAnnularControlledSlice.toControlled
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (h : IsTrackedTightAnnularControlledSlice
      Gamma L Z alpha beta U T) :
    RegularCardinal.IsControlledSlice
      (IsTightAnnularSlice Gamma L)
      (sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T :=
  h.1

theorem HasTrackedTightAnnularControlledSlices.toUntracked
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {C : Set (Ladder.Stage kappa)}
    {Z : Set V}
    (h : HasTrackedTightAnnularControlledSlices Gamma L C Z) :
    HasTightAnnularControlledSlices Gamma L C Z := by
  intro alpha halpha U hU hsmall
  obtain ⟨beta, hbeta, hab, T, hT⟩ := h alpha halpha U hU hsmall
  exact ⟨beta, hbeta, hab, T, hT.1⟩

/-- Annular, right-tight form of the candidate-table predicate.  Forgetting
the two geometric clauses recovers `ControlledSlices.IsSliceCandidate`. -/
def IsAnnularSliceCandidate {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa)
    (T : Set Gamma.DPath) : Prop :=
  IsTightAnnularSlice Gamma L T delta beta (request delta gamma) ∧
  HasStageIntervalSegments Gamma L T delta beta ∧
    #(sliceMavericks Gamma (L.warpAt beta) T) < kappa

/-- In a realized replacement, if the residual family is genuinely
exceptional relative to the current stage warp, it is exactly (not merely
an upper bound for) the stage-relative maverick family. -/
theorem sliceMavericks_segmentFamily_union_eq
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {S : Set V}
    (R : StageIntervalRealization L delta beta S)
    {E : Set Gamma.DPath}
    (hE : ∀ p ∈ E, ¬ IsLadderFragment Gamma (L.warpAt beta) p) :
    sliceMavericks Gamma (L.warpAt beta)
        (SliceSegmentCore.segmentFamily R.toSegmentRealization ∪ E) = E := by
  ext p
  constructor
  · rintro ⟨hpO | hpE, hpnot⟩
    · exact (hpnot
        (SliceSegmentCore.segmentFamily_isLadderFragment
          R.toSegmentRealization p hpO)).elim
    · exact hpE
  · intro hpE
    exact ⟨Or.inr hpE, hE p hpE⟩

/-- Assemble the causal annular candidate from the two concrete outputs of
the component-replacement argument: ordinary, stage-owned intervals and a
small exceptional remainder.  This is the path-level bridge which was
missing between `StageIntervalRealization`/`IsExceptionalRemainder` and the
pre-recorded candidate table.

The exceptional paths are allowed to be ordinary relative to the current
stage warp; in that case their interval provenance has to be supplied by
`hintervalE`.  In the source construction the stronger (and usual) fact is
that every member of `E` is a stage-relative maverick, making this premise
vacuous. -/
theorem isAnnularSliceCandidate_of_componentReplacement
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    {S : Set V}
    (hY : Gamma.IsWarp (L.warpAt beta))
    (R : StageIntervalRealization L delta beta S)
    {E : Set Gamma.DPath}
    (hE : SliceSegmentCore.IsExceptionalRemainder Gamma
      (L.frontier delta) (L.frontier beta) E)
    (hcover : L.frontier delta = S ∪ Gamma.initialSet E)
    (hdisjoint : Disjoint
      (Gamma.vertexSet
        (SliceSegmentCore.segmentFamily R.toSegmentRealization))
      (Gamma.vertexSet E))
    (hlinks : LinksToTarget Gamma E (request delta gamma))
    (hEsmall : #E < kappa)
    (hannular : Gamma.vertexSet
        (SliceSegmentCore.segmentFamily R.toSegmentRealization ∪ E) ⊆
      L.lowerRegion delta ∩ L.upperRegion beta)
    (htight : RightBoundaryTight Gamma
      (SliceSegmentCore.segmentFamily R.toSegmentRealization ∪ E)
      (L.frontier beta))
    (hintervalE : HasStageIntervalSegments Gamma L E delta beta) :
    IsAnnularSliceCandidate Gamma L request delta beta gamma
      (SliceSegmentCore.segmentFamily R.toSegmentRealization ∪ E) := by
  let O := SliceSegmentCore.segmentFamily R.toSegmentRealization
  have hlinkage : IsLinkageBetween Gamma (L.frontier delta)
      (L.frontier beta) (O ∪ E) :=
    SliceSegmentCore.linkageBetween_segmentFamily_union_exceptional
      hY R.toSegmentRealization hE hcover hdisjoint
  have htarget : LinksToTarget Gamma (O ∪ E) (request delta gamma) :=
    SliceSegmentCore.linksToTarget_mono_family Set.subset_union_right hlinks
  have hinterval : HasStageIntervalSegments Gamma L (O ∪ E)
      delta beta := by
    intro p hp hpordinary
    rcases hp with hpO | hpE
    · exact segmentFamily_hasStageIntervalSegments R p hpO hpordinary
    · exact hintervalE p hpE hpordinary
  have hmaverick : sliceMavericks Gamma (L.warpAt beta) (O ∪ E) ⊆ E := by
    intro p hp
    rcases hp.1 with hpO | hpE
    · exact (hp.2
        (SliceSegmentCore.segmentFamily_isLadderFragment
          R.toSegmentRealization p hpO)).elim
    · exact hpE
  have hmaverickSmall :
      #(sliceMavericks Gamma (L.warpAt beta) (O ∪ E)) < kappa :=
    (Cardinal.mk_subtype_mono hmaverick).trans_lt hEsmall
  exact ⟨⟨⟨⟨hlinkage, htarget⟩, hannular⟩, htight⟩,
    hinterval, hmaverickSmall⟩

/-- Source-form specialization of
`isAnnularSliceCandidate_of_componentReplacement`: every residual path is
a stage-relative maverick.  This both discharges interval provenance on
the residual family and identifies its vertex set with the registration
term used by the causal rows. -/
theorem isAnnularSliceCandidate_of_maverickComponentReplacement
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa} {S : Set V}
    (hY : Gamma.IsWarp (L.warpAt beta))
    (R : StageIntervalRealization L delta beta S)
    {E : Set Gamma.DPath}
    (hE : SliceSegmentCore.IsExceptionalRemainder Gamma
      (L.frontier delta) (L.frontier beta) E)
    (hcover : L.frontier delta = S ∪ Gamma.initialSet E)
    (hdisjoint : Disjoint
      (Gamma.vertexSet
        (SliceSegmentCore.segmentFamily R.toSegmentRealization))
      (Gamma.vertexSet E))
    (hlinks : LinksToTarget Gamma E (request delta gamma))
    (hEsmall : #E < kappa)
    (hEmaverick : ∀ p ∈ E,
      ¬ IsLadderFragment Gamma (L.warpAt beta) p)
    (hannular : Gamma.vertexSet
        (SliceSegmentCore.segmentFamily R.toSegmentRealization ∪ E) ⊆
      L.lowerRegion delta ∩ L.upperRegion beta)
    (htight : RightBoundaryTight Gamma
      (SliceSegmentCore.segmentFamily R.toSegmentRealization ∪ E)
      (L.frontier beta)) :
    IsAnnularSliceCandidate Gamma L request delta beta gamma
      (SliceSegmentCore.segmentFamily R.toSegmentRealization ∪ E) := by
  apply isAnnularSliceCandidate_of_componentReplacement
    hY R hE hcover hdisjoint hlinks hEsmall hannular htight
  intro p hpE hpordinary
  exact (hEmaverick p hpE hpordinary).elim

/-- Bounded all-exceptional branch of component replacement.  Here the
residual family already covers the entire old frontier, so the ordinary
stage-interval realization is empty.  This is the precise shape needed
when a `< kappa` frontier is linked wholesale by the lower extension
clause and subsequently tightened at a later frontier. -/
theorem isAnnularSliceCandidate_of_exceptionalRemainder
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa} {E : Set Gamma.DPath}
    (hE : SliceSegmentCore.IsExceptionalRemainder Gamma
      (L.frontier delta) (L.frontier beta) E)
    (hinitial : Gamma.initialSet E = L.frontier delta)
    (hlinks : LinksToTarget Gamma E (request delta gamma))
    (hEsmall : #E < kappa)
    (hEmaverick : ∀ p ∈ E,
      ¬ IsLadderFragment Gamma (L.warpAt beta) p)
    (hannular : Gamma.vertexSet E ⊆
      L.lowerRegion delta ∩ L.upperRegion beta)
    (htight : RightBoundaryTight Gamma E (L.frontier beta)) :
    IsAnnularSliceCandidate Gamma L request delta beta gamma E := by
  have hlinkage : IsLinkageBetween Gamma (L.frontier delta)
      (L.frontier beta) E :=
    ⟨hE.isWarp, hE.finiteCharacter, hinitial,
      hE.terminalFrontier_subset, hE.endpointPure⟩
  have hinterval : HasStageIntervalSegments Gamma L E delta beta := by
    intro p hpE hpordinary
    exact (hEmaverick p hpE hpordinary).elim
  have hmaverickSmall :
      #(sliceMavericks Gamma (L.warpAt beta) E) < kappa :=
    (Cardinal.mk_subtype_mono
      (sliceMavericks_subset Gamma (L.warpAt beta) E)).trans_lt hEsmall
  exact ⟨⟨⟨⟨hlinkage, hlinks⟩, hannular⟩, htight⟩,
    hinterval, hmaverickSmall⟩

/-- A stage-local annular candidate whose exceptional vertices have been
registered is already the full tracked controlled-slice payload needed by
the splice constructor.  The only passage from the current-stage warp to
the limiting warp is `StagesEmbedInLimit`; hence no global choice-table
assumption is hidden in this conversion. -/
theorem IsAnnularSliceCandidate.toTrackedControlled
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {Z U : Set V} {delta beta gamma : Ladder.Stage kappa}
    {T : Set Gamma.DPath}
    (hT : IsAnnularSliceCandidate Gamma L request delta beta gamma T)
    (hstageLimit : StagesEmbedInLimit Gamma L)
    (hU : U ⊆ request delta gamma)
    (hregistered : Gamma.vertexSet
      (sliceMavericks Gamma (L.warpAt beta) T) ⊆ Z) :
    IsTrackedTightAnnularControlledSlice Gamma L Z delta beta U T := by
  have hmaverickSub :
      sliceMavericks Gamma L.limitWarp T ⊆
        sliceMavericks Gamma (L.warpAt beta) T :=
    sliceMavericks_limit_subset_stage Gamma L hstageLimit beta T
  have hcontrolled : RegularCardinal.IsControlledSlice
      (IsTightAnnularSlice Gamma L)
      (sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z delta beta U T := by
    refine ⟨⟨⟨⟨hT.1.1.1.1,
      linksToTarget_mono Gamma T hU hT.1.1.1.2⟩,
      hT.1.1.2⟩, hT.1.2⟩,
      mk_sliceMavericks_lt_of_subset Gamma hmaverickSub hT.2.2, ?_⟩
    rw [maverickVertexSet_eq_vertexSet]
    rintro x ⟨p, hp, hxp⟩
    exact hregistered ⟨p, hmaverickSub hp, hxp⟩
  exact ⟨hcontrolled, hT.2.1, hT.2.2, hregistered⟩

/-- The causal candidate predicate depends only on the two visible ladder
stages and the request at the current coordinate. -/
theorem isAnnularSliceCandidate_congr_stageData
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L L' : Gamma.KappaLadder kappa}
    {request request' : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hwarpDelta : L.warpAt delta = L'.warpAt delta)
    (hwarpBeta : L.warpAt beta = L'.warpAt beta)
    (hfrontierDelta : L.frontier delta = L'.frontier delta)
    (hfrontierBeta : L.frontier beta = L'.frontier beta)
    (hrequest : request delta gamma = request' delta gamma) :
    IsAnnularSliceCandidate Gamma L request delta beta gamma T ↔
      IsAnnularSliceCandidate Gamma L' request' delta beta gamma T := by
  simp only [IsAnnularSliceCandidate, IsTightAnnularSlice,
    SliceSpliceSource.IsTightAnnularSlice, SliceSplice.IsAnnularSlice,
    SliceGood, RightBoundaryTight,
    SliceSpliceSource.MeetsOnlyAtTerminal,
    DWeb.KappaLadder.lowerRegion, DWeb.KappaLadder.upperRegion,
    HasStageIntervalSegments, IsStageInterval,
    hwarpDelta, hwarpBeta, hfrontierDelta, hfrontierBeta, hrequest]

theorem IsAnnularSliceCandidate.toSliceCandidate
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hT : IsAnnularSliceCandidate Gamma L request delta beta gamma T) :
    IsSliceCandidate Gamma L request delta beta gamma T :=
  ⟨hT.1.1.1, hT.2.2⟩

/-- If the whole old frontier is already `< kappa`, annularity alone makes
the slice a candidate: every possible maverick belongs to a family of size
at most that frontier.  This closes the finite-frontier branch after its
annular linkage has been constructed. -/
theorem isAnnularSliceCandidate_of_frontier_lt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {request : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hT : IsTightAnnularSlice Gamma L T delta beta
      (request delta gamma))
    (hinterval : HasStageIntervalSegments Gamma L T delta beta)
    (hfrontier : #(L.frontier delta) < kappa) :
    IsAnnularSliceCandidate Gamma L request delta beta gamma T := by
  refine ⟨hT, hinterval, ?_⟩
  exact mk_subfamily_lt_of_linkage_initial_lt Gamma hT.1.1.1
    (sliceMavericks_subset Gamma (L.warpAt beta) T) hfrontier

/-! ## The annular pre-recorded candidate table -/

/-- The set of all stage-local candidates at one causal coordinate. -/
def annularCandidateFamilies {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa -> Ladder.Stage kappa -> Set V)
    (delta beta gamma : Ladder.Stage kappa) : Set (Set Gamma.DPath) :=
  {T | IsAnnularSliceCandidate Gamma L request delta beta gamma T}

/-- Extensional choice from a set of path families.  Factoring the choice
through the candidate set makes prefix congruence an ordinary congruence of
function arguments, rather than a dependent rewrite through `Exists.choose`. -/
def choosePathFamily {Gamma : DWeb V}
    (families : Set (Set Gamma.DPath)) : Set Gamma.DPath := by
  classical
  exact if h : families.Nonempty then
    Classical.choose h
  else ∅

/-- Annular analogue of `ControlledSlices.chosenSlice`.  It is kept
separate from the older table so consumers which only need `SliceGood` do
not lose their existing definitional interface. -/
def chosenAnnularSlice {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa -> Ladder.Stage kappa -> Set V)
    (delta beta gamma : Ladder.Stage kappa) : Set Gamma.DPath :=
  choosePathFamily
    (annularCandidateFamilies Gamma L request delta beta gamma)

/-- Prefix congruence of the causal choice table.  Once the two visible
warps, frontiers, and current request agree, proof irrelevance makes the
classical table choice identical; no final-warp comparison is required. -/
theorem chosenAnnularSlice_congr_stageData
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L L' : Gamma.KappaLadder kappa}
    {request request' : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hwarpDelta : L.warpAt delta = L'.warpAt delta)
    (hwarpBeta : L.warpAt beta = L'.warpAt beta)
    (hfrontierDelta : L.frontier delta = L'.frontier delta)
    (hfrontierBeta : L.frontier beta = L'.frontier beta)
    (hrequest : request delta gamma = request' delta gamma) :
    chosenAnnularSlice Gamma L request delta beta gamma =
      chosenAnnularSlice Gamma L' request' delta beta gamma := by
  apply congrArg choosePathFamily
  ext T
  exact isAnnularSliceCandidate_congr_stageData hwarpDelta hwarpBeta
    hfrontierDelta hfrontierBeta hrequest

theorem chosenAnnularSlice_spec_of_exists
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa -> Ladder.Stage kappa -> Set V)
    {delta beta gamma : Ladder.Stage kappa}
    (h : exists T,
      IsAnnularSliceCandidate Gamma L request delta beta gamma T) :
    IsAnnularSliceCandidate Gamma L request delta beta gamma
      (chosenAnnularSlice Gamma L request delta beta gamma) := by
  classical
  change (annularCandidateFamilies Gamma L request
    delta beta gamma).Nonempty at h
  rw [chosenAnnularSlice, choosePathFamily, dif_pos h]
  exact Classical.choose_spec h

/-- Vertices of every stage-relative maverick in the annular table.  As in
the source's (9.13a), these vertices are registered before the later table
entry is invoked. -/
def chosenAnnularMaverickVertices
    {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa -> Ladder.Stage kappa -> Set V) : Set V :=
  ⋃ delta, ⋃ beta, ⋃ gamma, Gamma.vertexSet
    (sliceMavericks Gamma (L.warpAt beta)
      (chosenAnnularSlice Gamma L request delta beta gamma))

/-- The single candidate-table coordinate registered by one causal row.
Unlike `chosenAnnularMaverickVertices`, this definition contains no global
union over future stages. -/
def candidateVerticesAt
    {kappa : Cardinal.{u}} (Gamma : DWeb V)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa) : Set V :=
  Gamma.vertexSet
    (sliceMavericks Gamma (L.warpAt beta)
      (chosenAnnularSlice Gamma L request delta beta gamma))

/-- The single-coordinate registered vertex set has the same prefix
congruence as the chosen path family. -/
theorem candidateVerticesAt_congr_stageData
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L L' : Gamma.KappaLadder kappa}
    {request request' : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta beta gamma : Ladder.Stage kappa}
    (hwarpDelta : L.warpAt delta = L'.warpAt delta)
    (hwarpBeta : L.warpAt beta = L'.warpAt beta)
    (hfrontierDelta : L.frontier delta = L'.frontier delta)
    (hfrontierBeta : L.frontier beta = L'.frontier beta)
    (hrequest : request delta gamma = request' delta gamma) :
    candidateVerticesAt Gamma L request delta beta gamma =
      candidateVerticesAt Gamma L' request' delta beta gamma := by
  unfold candidateVerticesAt
  rw [hwarpBeta,
    chosenAnnularSlice_congr_stageData hwarpDelta hwarpBeta
      hfrontierDelta hfrontierBeta hrequest]

theorem candidateVerticesAt_subset_chosenAnnularMaverickVertices
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa) :
    candidateVerticesAt Gamma L request delta beta gamma ⊆
      chosenAnnularMaverickVertices Gamma L request := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨delta, Set.mem_iUnion.2 ⟨beta,
    Set.mem_iUnion.2 ⟨gamma, hx⟩⟩⟩

/-- A single candidate coordinate contributes at most `kappa` vertices to
a row.  If the coordinate is populated this is regularity plus finite
character of the chosen slice; if it is absent, the contribution is empty. -/
theorem mk_candidateVerticesAt_le
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta beta gamma : Ladder.Stage kappa) :
    #(candidateVerticesAt Gamma L request delta beta gamma) ≤ kappa := by
  classical
  by_cases hcandidate : ∃ T,
      IsAnnularSliceCandidate Gamma L request delta beta gamma T
  · have hchosen :=
      chosenAnnularSlice_spec_of_exists L request hcandidate
    exact (mk_vertexSet_exceptional_lt Gamma hregular
      (sliceMavericks_subset Gamma (L.warpAt beta) _)
      hchosen.2.2 hchosen.1.1.1.1.2.1).le
  · have hempty :
        chosenAnnularSlice Gamma L request delta beta gamma = ∅ := by
      rw [chosenAnnularSlice, choosePathFamily]
      split
      · rename_i hnonempty
        exact (hcandidate hnonempty).elim
      · rfl
    have hmaverick : sliceMavericks Gamma (L.warpAt beta)
        (chosenAnnularSlice Gamma L request delta beta gamma) = ∅ := by
      rw [hempty]
      ext p
      simp only [mem_sliceMavericks, Set.mem_empty_iff_false,
        false_and]
    have hvertices : Gamma.vertexSet
        (sliceMavericks Gamma (L.warpAt beta)
          (chosenAnnularSlice Gamma L request delta beta gamma)) = ∅ := by
      rw [hmaverick]
      ext x
      constructor
      · rintro ⟨p, hp, _hxp⟩
        exact hp
      · exact False.elim
    rw [candidateVerticesAt, hvertices]
    rw [Cardinal.mk_emptyCollection]
    exact bot_le

theorem vertexSet_chosenAnnularMavericks_subset
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa -> Ladder.Stage kappa -> Set V)
    (delta beta gamma : Ladder.Stage kappa) :
    Gamma.vertexSet
        (sliceMavericks Gamma (L.warpAt beta)
          (chosenAnnularSlice Gamma L request delta beta gamma)) ⊆
      chosenAnnularMaverickVertices Gamma L request := by
  exact candidateVerticesAt_subset_chosenAnnularMaverickVertices
    L request delta beta gamma

/-- Once an annular candidate is known to exist, the pre-recorded annular
entry is controlled relative to the limiting warp.  The request may be
shrunk; annularity is unaffected, while `LinksToTarget` is monotone. -/
theorem chosenAnnularSlice_isControlled_of_exists
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa -> Ladder.Stage kappa -> Set V)
    {Z U : Set V} {delta beta gamma : Ladder.Stage kappa}
    (hstageLimit : StagesEmbedInLimit Gamma L)
    (hcandidate : exists T,
      IsAnnularSliceCandidate Gamma L request delta beta gamma T)
    (hU : U ⊆ request delta gamma)
    (hregistered : chosenAnnularMaverickVertices Gamma L request ⊆ Z) :
    RegularCardinal.IsControlledSlice
      (IsTightAnnularSlice Gamma L)
      (sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath => p.support) Z delta beta U
      (chosenAnnularSlice Gamma L request delta beta gamma) := by
  have hchosen := chosenAnnularSlice_spec_of_exists L request hcandidate
  have hmaverickSub :
      sliceMavericks Gamma L.limitWarp
          (chosenAnnularSlice Gamma L request delta beta gamma) ⊆
    sliceMavericks Gamma (L.warpAt beta)
          (chosenAnnularSlice Gamma L request delta beta gamma) :=
    sliceMavericks_limit_subset_stage Gamma L hstageLimit beta _
  refine ⟨⟨⟨⟨hchosen.1.1.1.1,
    linksToTarget_mono Gamma _ hU hchosen.1.1.1.2⟩,
    hchosen.1.1.2⟩, hchosen.1.2⟩,
    mk_sliceMavericks_lt_of_subset Gamma hmaverickSub hchosen.2.2, ?_⟩
  rw [maverickVertexSet_eq_vertexSet]
  rintro x ⟨p, hp, hxp⟩
  apply hregistered
  apply vertexSet_chosenAnnularMavericks_subset L request delta beta gamma
  exact ⟨p, hmaverickSub hp, hxp⟩

end SliceCandidate
end CardinalInduction
end Erdos599
