/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.GroundingSelection
import ErdosProblems.Erdos599.LambdaDecoder

/-!
# Assembly of the Section 8 grounding construction

This file contains the recursive transversal used in Assertions 8.19--8.22.
Before doing the recursion, each local stationary in-fan is normalized
against the whole popular cut.  Requests are embedded in the ordinals below
`kappa`; at one stage, fewer than `kappa` paths have already been chosen.
The paths in the current fan which meet any earlier chosen finite path have
a nonstationary set of initial indices, so a fresh member remains.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingAssembly

open DirectedPath Stationary
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev LV (L : PopularAuxiliary.Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

abbrev Path (L : PopularAuxiliary.Input Gamma I) :=
  FinitePath L.lambda.graph

/-- Normalize the local fan at a request against the complete popular cut.
Consequently a member can meet the cut only at its own apex. -/
def normalizedRequestFan
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    Popular.JoinedFamily L.lambda {requestAuxVertex r} :=
  Popular.goodJoinedFamily
    (GroundingSelection.controlledRequestFan S K r) S.cut

theorem normalizedRequestFan_stationary
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf U (normalizedRequestFan S K r).paths
        (normalizedRequestFan S K r).starts_in_source) := by
  exact Popular.goodJoinedFamily_stationary U
    (GroundingSelection.controlledRequestFan S K r) S.cut
    (GroundingSelection.controlledRequestFan_stationary S K r)
    S.not_strongly_popular

theorem normalizedRequestFan_cut_normalized
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut)
    {p : Path L} (hp : p ∈ (normalizedRequestFan S K r).paths) :
    p.support ∩ S.cut ⊆ {requestAuxVertex r} :=
  Popular.goodJoinedFamily_normalized
    (GroundingSelection.controlledRequestFan S K r) S.cut hp

/-- The unique request at rank `a`, if there is one. -/
def requestAt
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa) :
    Option (Request L S.cut) := by
  classical
  exact if h : ∃ r, rank r = a then some (Classical.choose h) else none

theorem requestAt_eq_some_iff
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa)
    (r : Request L S.cut) :
    requestAt rank a = some r ↔ rank r = a := by
  classical
  simp only [requestAt]
  split
  next h =>
    constructor
    · intro hr
      have hchosen : Classical.choose h = r := Option.some.inj hr
      exact hchosen ▸ Classical.choose_spec h
    · intro hra
      have hchosen : Classical.choose h = r := by
        apply rank.injective
        exact (Classical.choose_spec h).trans hra.symm
      exact congrArg some hchosen
  next h =>
    constructor
    · intro hr
      cases hr
    · exact fun hra => False.elim (h ⟨r, hra⟩)

/-- Paths in a joined family which meet a prescribed finite path. -/
def collidingPaths
    {W : Type u} {web : DWeb W} {T : Set W}
    (F : Popular.JoinedFamily web T) (q : FinitePath web.graph) :
    Set (FinitePath web.graph) :=
  {p | p ∈ F.paths ∧ (p.support ∩ q.support).Nonempty}

/-- Paths in a joined family which meet an arbitrary prescribed vertex set. -/
def collidingSet
    {W : Type u} {web : DWeb W} {T : Set W}
    (F : Popular.JoinedFamily web T) (R : Set W) :
    Set (FinitePath web.graph) :=
  {p | p ∈ F.paths ∧ (p.support ∩ R).Nonempty}

theorem collidingSetIndices_nonstationary
    {W : Type u} {web : DWeb W} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed web kappa) {T R : Set W}
    (F : Popular.JoinedFamily web T) (hR : R.Countable)
    (hRT : Disjoint R T) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U F (collidingSet F R)) := by
  apply PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
    U (PopularSwitching.restrictPaths F (collidingSet F R)) hR hRT
  intro p hp
  obtain ⟨x, hxp, hxR⟩ := hp.2.2
  exact ⟨x, hxR, hxp⟩

theorem collidingIndices_nonstationary
    {W : Type u} {web : DWeb W} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed web kappa) {T : Set W}
    (F : Popular.JoinedFamily web T) (q : FinitePath web.graph)
    (hqT : Disjoint q.support T) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U F (collidingPaths F q)) := by
  apply PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
    U (PopularSwitching.restrictPaths F (collidingPaths F q))
    q.support_finite.countable hqT
  intro p hp
  obtain ⟨x, hxp, hxq⟩ := hp.2.2
  exact ⟨x, hxq, hxp⟩

/-- A normalized member at one request misses the apex of every different
request.  This is the small geometric fact which makes the recursion work. -/
theorem normalized_member_disjoint_other_apex
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    {r s : Request L S.cut}
    (hrs : r ≠ s) {p : Path L}
    (hp : p ∈ (normalizedRequestFan S K r).paths) :
    Disjoint p.support {requestAuxVertex s} := by
  rw [Set.disjoint_left]
  intro x hxp hxs
  have hx : x = requestAuxVertex s := Set.mem_singleton_iff.1 hxs
  have hcut : requestAuxVertex s ∈ S.cut := requestAuxVertex_mem_cut s
  have happ := normalizedRequestFan_cut_normalized S K r hp
    ⟨hxp, hx ▸ hcut⟩
  have heq : requestAuxVertex s = requestAuxVertex r := by
    exact hx.symm.trans (Set.mem_singleton_iff.1 happ)
  exact hrs (GroundingSelection.requestAuxVertex_injective heq.symm)

/-- The complete forbidden set contributed by an earlier selected route.
Besides the route's own auxiliary support, it contains the whole trace of
every reference-ladder component touched by that route.  The current apex is
removed because every member of the current in-fan must end there. -/
def priorForbidden
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    (r : Request L C) (q : Path L) : Set (LV L) :=
  (q.support ∪ PopularSwitching.metLadderTrace L q) \
    {requestAuxVertex r}

theorem priorForbidden_countable
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    (r : Request L C) (q : Path L) :
    (priorForbidden r q).Countable := by
  exact (q.support_finite.countable.union
    (PopularSwitching.metLadderTrace_countable L q)).mono Set.sdiff_subset

theorem priorForbidden_disjoint_apex
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    (r : Request L C) (q : Path L) :
    Disjoint (priorForbidden r q) {requestAuxVertex r} :=
  Set.disjoint_sdiff_left

/-- Avoiding the prior forbidden set implies ordinary route disjointness.
The only point removed from that forbidden set is the current apex, and
cut-normalization says an earlier route for a different request misses it. -/
theorem disjoint_support_of_disjoint_priorForbidden
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    {r s : Request L S.cut} (hrs : r ≠ s)
    {p q : Path L}
    (hq : q ∈ (normalizedRequestFan S K r).paths)
    (havoid : Disjoint p.support (priorForbidden s q)) :
    Disjoint p.support q.support := by
  have hqapex : Disjoint q.support {requestAuxVertex s} :=
    normalized_member_disjoint_other_apex S K hrs hq
  rw [Set.disjoint_left] at hqapex havoid ⊢
  intro x hxp hxq
  apply havoid hxp
  refine ⟨Or.inl hxq, ?_⟩
  intro hxs
  exact hqapex hxq (Set.mem_singleton_iff.2 hxs)

/-- Candidate paths at one stage of the well-founded request recursion.
This is condition (a) of Assertion 8.22: later paths avoid every ladder
component trace met by an earlier path, in addition to avoiding the earlier
path itself. -/
def freshCandidates
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (a : Below kappa)
    (r : Request L S.cut)
    (previous : ∀ b : Below kappa, b < a → Option (Path L)) :
    Set (Path L) :=
  {p | p ∈ (normalizedRequestFan S K r).paths ∧
    ∀ b (hba : b < a) q, previous b hba = some q →
      Disjoint p.support (priorForbidden r q)}

/-- Totalized selection from a set. -/
def chooseSome {X : Type*} (A : Set X) : Option X := by
  classical
  exact if h : A.Nonempty then some (Classical.choose h) else none

theorem chooseSome_spec {X : Type*} {A : Set X} (hA : A.Nonempty) :
    ∃ x, chooseSome A = some x ∧ x ∈ A := by
  classical
  refine ⟨Classical.choose hA, ?_, Classical.choose_spec hA⟩
  simp [chooseSome, hA]

/-- One stage of the request recursion. -/
def chooseAt
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa)
    (previous : ∀ b : Below kappa, b < a → Option (Path L)) :
    Option (Path L) :=
  match requestAt rank a with
  | none => none
  | some r => chooseSome (freshCandidates S K a r previous)

/-- The recursively selected path at an ordinal below `kappa`. -/
def recursiveChoice
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa) :
    Option (Path L) :=
  WellFounded.fix wellFounded_lt
    (fun a previous => chooseAt S K rank a previous) a

theorem recursiveChoice_eq
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa) :
    recursiveChoice S K rank a =
      chooseAt S K rank a (fun b _hba => recursiveChoice S K rank b) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun a previous => chooseAt S K rank a previous) a

/-- The induction invariant of the recursive transversal. -/
def ChoiceValidAt
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa)
    (previous : ∀ b : Below kappa, b < a → Option (Path L))
    (chosen : Option (Path L)) : Prop :=
  match requestAt rank a with
  | none => chosen = none
  | some r => ∃ p, chosen = some p ∧ p ∈ freshCandidates S K a r previous

/-- The predecessor order below one ordinal below `kappa` has cardinality
strictly below `kappa` (with the universe lift required by stationary sets). -/
theorem mk_Iio_below_lt_lift
    {kappa : Cardinal.{u}} (a : Below kappa) :
    #(Set.Iio a) < Cardinal.lift.{u + 1, u} kappa := by
  let f : Set.Iio a → Set.Iio a.1 := fun b => ⟨b.1.1, b.2⟩
  have hf : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Set.Iio a.1 => z.1) hbc
  calc
    #(Set.Iio a) ≤ #(Set.Iio a.1) := Cardinal.mk_le_of_injective hf
    _ = Cardinal.lift.{u + 1, u} a.1.card := by
      rw [Cardinal.mk_Iio_ordinal]
    _ < Cardinal.lift.{u + 1, u} kappa :=
      Cardinal.lift_lt.mpr (Cardinal.lt_ord.mp a.2)

/-- The fresh candidate set is nonempty when all earlier recursive choices
satisfy the induction invariant. -/
theorem freshCandidates_nonempty
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa)
    (r : Request L S.cut) (hra : requestAt rank a = some r)
    (previous : ∀ b : Below kappa, b < a → Option (Path L))
    (hprevious : ∀ b (hba : b < a),
      ChoiceValidAt S K rank b
        (fun c _hcb => previous c (lt_trans _hcb hba))
        (previous b hba)) :
    (freshCandidates S K a r previous).Nonempty := by
  let bad : Set.Iio a → Set (Below kappa) := fun b =>
    match hq : previous b.1 b.2 with
    | none => ∅
    | some q => GroundingSelection.restrictedIndices U
        (normalizedRequestFan S K r)
        (collidingSet (normalizedRequestFan S K r) (priorForbidden r q))
  have hbad : ∀ b, ¬ IsStationaryBelow kappa (bad b) := by
    intro b
    dsimp only [bad]
    cases hq : previous b.1 b.2 with
    | none =>
        simp [hq]
    | some q =>
        have hv := hprevious b.1 b.2
        cases hrb : requestAt rank b.1 with
        | none =>
            simp only [ChoiceValidAt, hrb] at hv
            exact False.elim (by simpa [hq] using hv)
        | some rb =>
            simp only [ChoiceValidAt, hrb] at hv
            obtain ⟨q', hq', hq'fresh⟩ := hv
            have hqq' : q = q' := Option.some.inj (hq.symm.trans hq')
            subst q'
            simpa only [hq] using
              (collidingSetIndices_nonstationary U
                (normalizedRequestFan S K r)
                (priorForbidden_countable r q)
                (priorForbidden_disjoint_apex r q))
  have hbadUnion : ¬ IsStationaryBelow kappa (⋃ b, bad b) :=
    not_isStationaryBelow_iUnion_of_lt U.regular U.uncountable
      (mk_Iio_below_lt_lift a) hbad
  have hfreshIndices : IsStationaryBelow kappa
      (Popular.initialIndicesOf U (normalizedRequestFan S K r).paths
        (normalizedRequestFan S K r).starts_in_source \ ⋃ b, bad b) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      U.regular U.uncountable
        (normalizedRequestFan_stationary S K r) hbadUnion
  obtain ⟨i, hiFan, hiBad⟩ := hfreshIndices.nonempty
  obtain ⟨p, hpFan, hip⟩ := hiFan
  refine ⟨p, hpFan, ?_⟩
  intro b hba q hbq
  by_contra hdisj
  have hmeet : (p.support ∩ priorForbidden r q).Nonempty :=
    Set.not_disjoint_iff.mp hdisj
  have hpcoll : p ∈ collidingSet (normalizedRequestFan S K r)
      (priorForbidden r q) :=
    ⟨hpFan, hmeet⟩
  let b' : Set.Iio a := ⟨b, hba⟩
  have hiOne : i ∈ bad b' := by
    have hindex := GroundingSelection.mem_restrictedIndices_of U
      (normalizedRequestFan S K r)
      (collidingSet (normalizedRequestFan S K r) (priorForbidden r q))
      hpFan hpcoll
    have heq :
        U.f ⟨p.start, (normalizedRequestFan S K r).starts_in_source hpFan⟩ = i :=
      hip
    have hbq' : previous b'.1 b'.2 = some q := by
      simpa only [b'] using hbq
    dsimp only [bad]
    rw [hbq']
    exact heq ▸ hindex
  exact hiBad (Set.mem_iUnion.2 ⟨b', hiOne⟩)

/-- Every stage of the well-founded recursion satisfies its invariant. -/
theorem recursiveChoice_valid
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa) :
    ChoiceValidAt S K rank a (fun b _hba => recursiveChoice S K rank b)
      (recursiveChoice S K rank a) := by
  rw [recursiveChoice_eq S K rank a]
  cases hra : requestAt rank a with
  | none =>
      simp [ChoiceValidAt, chooseAt, hra]
  | some r =>
      have hnonempty :
          (freshCandidates S K a r
            (fun b _hba => recursiveChoice S K rank b)).Nonempty := by
        apply freshCandidates_nonempty S K rank a r hra
        intro b hba
        simpa only using recursiveChoice_valid S K rank b
      obtain ⟨p, hpchoose, hp⟩ := chooseSome_spec hnonempty
      simp only [ChoiceValidAt, hra, chooseAt]
      exact ⟨p, by simpa [hra] using hpchoose, hp⟩
termination_by a.1

/-- A canonical embedding of the request set in the ordinal stages. -/
def requestRank
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) : Request L S.cut ↪ Below kappa :=
  Classical.choice
    (by
      apply Cardinal.lift_mk_le'.mp
      rw [Stationary.mk_below]
      simpa only [Cardinal.lift_lift] using
        Cardinal.lift_le.mpr (requests_card_le U S))

/-- The chosen auxiliary path assigned to a request. -/
def selectedPath
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) : Path L :=
  Classical.choose (show ∃ p,
      recursiveChoice S K (requestRank U S) (requestRank U S r) = some p ∧
        p ∈ freshCandidates S K (requestRank U S r) r
          (fun b _h => recursiveChoice S K (requestRank U S) b) by
    have hv := recursiveChoice_valid S K (requestRank U S)
      (requestRank U S r)
    have hra : requestAt (requestRank U S) (requestRank U S r) = some r :=
      (requestAt_eq_some_iff (requestRank U S) _ r).2 rfl
    simpa only [ChoiceValidAt, hra] using hv)

theorem selectedPath_spec
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    recursiveChoice S K (requestRank U S) (requestRank U S r) =
        some (selectedPath U S K r) ∧
      selectedPath U S K r ∈ freshCandidates S K (requestRank U S r) r
        (fun b _h => recursiveChoice S K (requestRank U S) b) := by
  unfold selectedPath
  exact Classical.choose_spec (show ∃ p,
      recursiveChoice S K (requestRank U S) (requestRank U S r) = some p ∧
        p ∈ freshCandidates S K (requestRank U S r) r
          (fun b _h => recursiveChoice S K (requestRank U S) b) by
    have hv := recursiveChoice_valid S K (requestRank U S)
      (requestRank U S r)
    have hra : requestAt (requestRank U S) (requestRank U S r) = some r :=
      (requestAt_eq_some_iff (requestRank U S) _ r).2 rfl
    simpa only [ChoiceValidAt, hra] using hv)

theorem selectedPath_mem_normalizedRequestFan
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    selectedPath U S K r ∈ (normalizedRequestFan S K r).paths :=
  (selectedPath_spec U S K r).2.1

/-- The recursive choice really respects the ladder-collision pruning
recorded in `Controls`; this is the projection used by the final switching
argument. -/
theorem selectedPath_not_mem_hangingLadder
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    selectedPath U S K r ∉ K.hangingLadder r :=
  (selectedPath_mem_normalizedRequestFan U S K r).1.2.1

/-- The recursive choice also respects the deleted-fragment pruning. -/
theorem selectedPath_not_mem_hangingFragment
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    selectedPath U S K r ∉ K.hangingFragment r :=
  (selectedPath_mem_normalizedRequestFan U S K r).1.2.2

theorem selectedPath_finish
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    (selectedPath U S K r).finish = requestAuxVertex r := by
  exact Set.mem_singleton_iff.1
    ((normalizedRequestFan S K r).ends_in_join
      (selectedPath_mem_normalizedRequestFan U S K r))

theorem selectedPath_pairwiseDisjoint
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S) :
    Set.PairwiseDisjoint Set.univ
      (fun r : Request L S.cut => (selectedPath U S K r).support) := by
  intro r _hr s _hs hrs
  let rank := requestRank U S
  rcases lt_trichotomy (rank r) (rank s) with hrslt | hrseq | hrslt
  · have hsFresh := (selectedPath_spec U S K s).2.2
    exact (disjoint_support_of_disjoint_priorForbidden S K hrs
      (selectedPath_mem_normalizedRequestFan U S K r)
      (hsFresh (rank r) hrslt (selectedPath U S K r)
        (selectedPath_spec U S K r).1)).symm
  · exact False.elim (hrs (rank.injective hrseq))
  · have hrFresh := (selectedPath_spec U S K r).2.2
    exact disjoint_support_of_disjoint_priorForbidden S K hrs.symm
      (selectedPath_mem_normalizedRequestFan U S K s)
      (hrFresh (rank s) hrslt (selectedPath U S K s)
        (selectedPath_spec U S K s).1)

/-- The recursively selected auxiliary paths form an honest finite warp,
with one path ending at the auxiliary representative of every request. -/
def selectedWarp
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S) :
    Popular.XSWarp L.lambda (GroundingSelection.requestCut L S.cut) where
  paths := Set.range (selectedPath U S K)
  disjoint := by
    rintro p ⟨r, rfl⟩ q ⟨s, rfl⟩ hpq
    apply selectedPath_pairwiseDisjoint U S K
      (Set.mem_univ r) (Set.mem_univ s)
    intro hrs
    subst s
    exact hpq rfl
  starts_in_source := by
    rintro p ⟨r, rfl⟩
    exact (normalizedRequestFan S K r).starts_in_source
      (selectedPath_mem_normalizedRequestFan U S K r)
  ends_in_target := by
    rintro p ⟨r, rfl⟩
    exact ⟨r, (selectedPath_finish U S K r).symm⟩

theorem selectedWarp_covers_requests
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    ∃ p ∈ (selectedWarp U S K).paths, p.finish = requestAuxVertex r :=
  ⟨selectedPath U S K r, ⟨r, rfl⟩, selectedPath_finish U S K r⟩

end GroundingAssembly
end Erdos599
