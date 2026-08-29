/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssembly

/-!
# Controlled assembly of the Section 8 grounding paths

This file strengthens `GroundingAssembly` by carrying the two exceptional
families of Assertions 8.19 and 8.20 through the recursive transversal.
Each normalized local fan is first restricted to paths which belong to
neither exceptional family.  The two nonstationarity theorems in
`GroundingSelection` show that the restricted fan is still stationary.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingControlledAssembly

open DirectedPath Stationary
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev LV (L : PopularAuxiliary.Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

abbrev Path (L : PopularAuxiliary.Input Gamma I) :=
  FinitePath L.lambda.graph

/-- The paths at `r` forbidden by Assertions 8.19 and 8.20. -/
def forbiddenPaths
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} (K : GroundingSelection.Controls S)
    (r : Request L S.cut) : Set (Path L) :=
  K.hangingLadder r ∪ K.hangingFragment r

/-- The normalized local fan after removing both source-theoretic bad
families. -/
def controlledRequestFan
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    Popular.JoinedFamily L.lambda {requestAuxVertex r} :=
  PopularSwitching.restrictPaths (GroundingAssembly.normalizedRequestFan S K r)
    (forbiddenPaths K r)ᶜ

@[simp]
theorem mem_controlledRequestFan
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) (p : Path L) :
    p ∈ (controlledRequestFan S K r).paths ↔
      p ∈ (GroundingAssembly.normalizedRequestFan S K r).paths ∧
        p ∉ forbiddenPaths K r := by
  rfl

/-- Restricting the path set of a joined family can only restrict its set of
initial indices. -/
theorem restrictedIndices_mono_family
    {W : Type u} {web : DWeb W} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed web kappa) {T : Set W}
    (F G : Popular.JoinedFamily web T)
    (hFG : F.paths ⊆ G.paths) (P : Set (FinitePath web.graph)) :
    GroundingSelection.restrictedIndices U F P ⊆
      GroundingSelection.restrictedIndices U G P := by
  rintro a ⟨p, hp, hpa⟩
  have hpG : p ∈ (PopularSwitching.restrictPaths G P).paths :=
    ⟨hFG hp.1, hp.2⟩
  refine ⟨p, hpG, ?_⟩
  have hs :
      (⟨p.start,
        (PopularSwitching.restrictPaths G P).starts_in_source hpG⟩ : web.source) =
      ⟨p.start,
        (PopularSwitching.restrictPaths F P).starts_in_source hp⟩ :=
    Subtype.ext rfl
  exact (congrArg U.f hs).trans hpa

theorem normalized_badLadder_indices_nonstationary
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U
        (GroundingAssembly.normalizedRequestFan S K r) (K.hangingLadder r)) := by
  intro h
  apply GroundingSelection.hangingLadder_indices_nonstationary S K r
  apply h.mono
  apply restrictedIndices_mono_family U
  intro p hp
  exact hp.1.1

theorem normalized_badFragment_indices_nonstationary
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U
        (GroundingAssembly.normalizedRequestFan S K r) (K.hangingFragment r)) := by
  intro h
  apply GroundingSelection.hangingFragment_indices_nonstationary S K r
  apply h.mono
  apply restrictedIndices_mono_family U
  intro p hp
  exact hp.1.1

theorem restrictedIndices_union_subset
    {W : Type u} {web : DWeb W} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed web kappa) {T : Set W}
    (F : Popular.JoinedFamily web T)
    (P Q : Set (FinitePath web.graph)) :
    GroundingSelection.restrictedIndices U F (P ∪ Q) ⊆
      GroundingSelection.restrictedIndices U F P ∪
        GroundingSelection.restrictedIndices U F Q := by
  rintro a ⟨p, hp, hpa⟩
  rcases hp.2 with hpP | hpQ
  · left
    let hp' : p ∈ (PopularSwitching.restrictPaths F P).paths := ⟨hp.1, hpP⟩
    refine ⟨p, hp', ?_⟩
    have hs :
        (⟨p.start,
          (PopularSwitching.restrictPaths F P).starts_in_source hp'⟩ : web.source) =
        ⟨p.start,
          (PopularSwitching.restrictPaths F (P ∪ Q)).starts_in_source hp⟩ :=
      Subtype.ext rfl
    exact (congrArg U.f hs).trans hpa
  · right
    let hp' : p ∈ (PopularSwitching.restrictPaths F Q).paths := ⟨hp.1, hpQ⟩
    refine ⟨p, hp', ?_⟩
    have hs :
        (⟨p.start,
          (PopularSwitching.restrictPaths F Q).starts_in_source hp'⟩ : web.source) =
        ⟨p.start,
          (PopularSwitching.restrictPaths F (P ∪ Q)).starts_in_source hp⟩ :=
      Subtype.ext rfl
    exact (congrArg U.f hs).trans hpa

theorem normalized_forbidden_indices_nonstationary
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U
        (GroundingAssembly.normalizedRequestFan S K r)
        (forbiddenPaths K r)) := by
  have hL := normalized_badLadder_indices_nonstationary S K r
  have hF := normalized_badFragment_indices_nonstationary S K r
  have hU := GroundingSelection.not_isStationaryBelow_union
    U.regular U.uncountable hL hF
  intro h
  apply hU
  exact h.mono (restrictedIndices_union_subset U
    (GroundingAssembly.normalizedRequestFan S K r)
    (K.hangingLadder r) (K.hangingFragment r))

/-- After both exceptional families are removed, the normalized local fan
still has stationary initial-index set. -/
theorem controlledRequestFan_stationary
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf U (controlledRequestFan S K r).paths
        (controlledRequestFan S K r).starts_in_source) := by
  let F := GroundingAssembly.normalizedRequestFan S K r
  let B := GroundingSelection.restrictedIndices U F (forbiddenPaths K r)
  have hdiff : IsStationaryBelow kappa
      (Popular.initialIndicesOf U F.paths F.starts_in_source \ B) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      U.regular U.uncountable
      (GroundingAssembly.normalizedRequestFan_stationary S K r)
      (normalized_forbidden_indices_nonstationary S K r)
  apply hdiff.mono
  rintro a ⟨⟨p, hpF, hpa⟩, haB⟩
  have hpGood : p ∉ forbiddenPaths K r := by
    intro hpBad
    apply haB
    have hm := GroundingSelection.mem_restrictedIndices_of U F
      (forbiddenPaths K r) hpF hpBad
    rw [hpa] at hm
    exact hm
  let hp : p ∈ (controlledRequestFan S K r).paths := ⟨hpF, hpGood⟩
  refine ⟨p, hp, ?_⟩
  have hs :
      (⟨p.start, (controlledRequestFan S K r).starts_in_source hp⟩ :
          L.lambda.source) =
      ⟨p.start, F.starts_in_source hpF⟩ := Subtype.ext rfl
  exact (congrArg U.f hs).trans hpa

/-- Candidate paths at one stage, now drawn from the controlled fan. -/
def freshCandidates
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (a : Below kappa) (r : Request L S.cut)
    (previous : ∀ b : Below kappa, b < a → Option (Path L)) :
    Set (Path L) :=
  {p | p ∈ (controlledRequestFan S K r).paths ∧
    ∀ b (hba : b < a) q, previous b hba = some q →
      Disjoint p.support q.support}

/-- One stage of the controlled request recursion. -/
def chooseAt
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa)
    (previous : ∀ b : Below kappa, b < a → Option (Path L)) :
    Option (Path L) :=
  match GroundingAssembly.requestAt rank a with
  | none => none
  | some r => GroundingAssembly.chooseSome (freshCandidates S K a r previous)

/-- The controlled recursively selected path at an ordinal below `kappa`. -/
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

/-- Induction invariant for the controlled recursion. -/
def ChoiceValidAt
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa)
    (previous : ∀ b : Below kappa, b < a → Option (Path L))
    (chosen : Option (Path L)) : Prop :=
  match GroundingAssembly.requestAt rank a with
  | none => chosen = none
  | some r => ∃ p, chosen = some p ∧ p ∈ freshCandidates S K a r previous

/-- The controlled fresh set is nonempty when the earlier choices satisfy
the recursion invariant. -/
theorem freshCandidates_nonempty
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa)
    (r : Request L S.cut)
    (hra : GroundingAssembly.requestAt rank a = some r)
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
        (controlledRequestFan S K r)
        (GroundingAssembly.collidingPaths (controlledRequestFan S K r) q)
  have hbad : ∀ b, ¬ IsStationaryBelow kappa (bad b) := by
    intro b
    dsimp only [bad]
    cases hq : previous b.1 b.2 with
    | none =>
        simp [hq]
    | some q =>
        have hv := hprevious b.1 b.2
        cases hrb : GroundingAssembly.requestAt rank b.1 with
        | none =>
            simp only [ChoiceValidAt, hrb] at hv
            exact False.elim (by simpa [hq] using hv)
        | some rb =>
            simp only [ChoiceValidAt, hrb] at hv
            obtain ⟨q', hq', hq'fresh⟩ := hv
            have hqq' : q = q' := Option.some.inj (hq.symm.trans hq')
            subst q'
            have hrankb : rank rb = b.1 :=
              (GroundingAssembly.requestAt_eq_some_iff rank b.1 rb).1 hrb
            have hranka : rank r = a :=
              (GroundingAssembly.requestAt_eq_some_iff rank a r).1 hra
            have hrbr : rb ≠ r := by
              intro h
              subst rb
              have : b.1 = a := hrankb.symm.trans hranka
              exact (ne_of_lt b.2) this
            have hqapex : Disjoint q.support {requestAuxVertex r} :=
              GroundingAssembly.normalized_member_disjoint_other_apex S K hrbr
                hq'fresh.1.1
            simpa only [hq] using
              (GroundingAssembly.collidingIndices_nonstationary U
                (controlledRequestFan S K r) q hqapex)
  have hbadUnion : ¬ IsStationaryBelow kappa (⋃ b, bad b) :=
    not_isStationaryBelow_iUnion_of_lt U.regular U.uncountable
      (GroundingAssembly.mk_Iio_below_lt_lift a) hbad
  have hfreshIndices : IsStationaryBelow kappa
      (Popular.initialIndicesOf U (controlledRequestFan S K r).paths
        (controlledRequestFan S K r).starts_in_source \ ⋃ b, bad b) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      U.regular U.uncountable (controlledRequestFan_stationary S K r)
      hbadUnion
  obtain ⟨i, hiFan, hiBad⟩ := hfreshIndices.nonempty
  obtain ⟨p, hpFan, hip⟩ := hiFan
  refine ⟨p, hpFan, ?_⟩
  intro b hba q hbq
  by_contra hdisj
  have hmeet : (p.support ∩ q.support).Nonempty :=
    Set.not_disjoint_iff.mp hdisj
  have hpcoll : p ∈ GroundingAssembly.collidingPaths
      (controlledRequestFan S K r) q := ⟨hpFan, hmeet⟩
  let b' : Set.Iio a := ⟨b, hba⟩
  have hiOne : i ∈ bad b' := by
    have hindex := GroundingSelection.mem_restrictedIndices_of U
      (controlledRequestFan S K r)
      (GroundingAssembly.collidingPaths (controlledRequestFan S K r) q)
      hpFan hpcoll
    have heq :
        U.f ⟨p.start, (controlledRequestFan S K r).starts_in_source hpFan⟩ = i :=
      hip
    have hbq' : previous b'.1 b'.2 = some q := by
      simpa only [b'] using hbq
    dsimp only [bad]
    rw [hbq']
    exact heq ▸ hindex
  exact hiBad (Set.mem_iUnion.2 ⟨b', hiOne⟩)

/-- Every stage of the controlled well-founded recursion satisfies its
invariant. -/
theorem recursiveChoice_valid
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Below kappa) (a : Below kappa) :
    ChoiceValidAt S K rank a (fun b _hba => recursiveChoice S K rank b)
      (recursiveChoice S K rank a) := by
  rw [recursiveChoice_eq S K rank a]
  cases hra : GroundingAssembly.requestAt rank a with
  | none =>
      simp [ChoiceValidAt, chooseAt, hra]
  | some r =>
      have hnonempty :
          (freshCandidates S K a r
            (fun b _hba => recursiveChoice S K rank b)).Nonempty := by
        apply freshCandidates_nonempty S K rank a r hra
        intro b hba
        simpa only using recursiveChoice_valid S K rank b
      obtain ⟨p, hpchoose, hp⟩ :=
        GroundingAssembly.chooseSome_spec hnonempty
      simp only [ChoiceValidAt, hra, chooseAt]
      exact ⟨p, by simpa [hra] using hpchoose, hp⟩
termination_by a.1

/-- The controlled auxiliary path assigned to a request. -/
def selectedPath
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) : Path L :=
  Classical.choose (show ∃ p,
      recursiveChoice S K (GroundingAssembly.requestRank U S)
          (GroundingAssembly.requestRank U S r) = some p ∧
        p ∈ freshCandidates S K (GroundingAssembly.requestRank U S r) r
          (fun b _h => recursiveChoice S K
            (GroundingAssembly.requestRank U S) b) by
    have hv := recursiveChoice_valid S K (GroundingAssembly.requestRank U S)
      (GroundingAssembly.requestRank U S r)
    have hra : GroundingAssembly.requestAt (GroundingAssembly.requestRank U S)
        (GroundingAssembly.requestRank U S r) = some r :=
      (GroundingAssembly.requestAt_eq_some_iff
        (GroundingAssembly.requestRank U S) _ r).2 rfl
    simpa only [ChoiceValidAt, hra] using hv)

theorem selectedPath_spec
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    recursiveChoice S K (GroundingAssembly.requestRank U S)
        (GroundingAssembly.requestRank U S r) = some (selectedPath U S K r) ∧
      selectedPath U S K r ∈
        freshCandidates S K (GroundingAssembly.requestRank U S r) r
          (fun b _h => recursiveChoice S K
            (GroundingAssembly.requestRank U S) b) := by
  unfold selectedPath
  exact Classical.choose_spec (show ∃ p,
      recursiveChoice S K (GroundingAssembly.requestRank U S)
          (GroundingAssembly.requestRank U S r) = some p ∧
        p ∈ freshCandidates S K (GroundingAssembly.requestRank U S r) r
          (fun b _h => recursiveChoice S K
            (GroundingAssembly.requestRank U S) b) by
    have hv := recursiveChoice_valid S K (GroundingAssembly.requestRank U S)
      (GroundingAssembly.requestRank U S r)
    have hra : GroundingAssembly.requestAt (GroundingAssembly.requestRank U S)
        (GroundingAssembly.requestRank U S r) = some r :=
      (GroundingAssembly.requestAt_eq_some_iff
        (GroundingAssembly.requestRank U S) _ r).2 rfl
    simpa only [ChoiceValidAt, hra] using hv)

theorem selectedPath_mem_controlledRequestFan
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    selectedPath U S K r ∈ (controlledRequestFan S K r).paths :=
  (selectedPath_spec U S K r).2.1

theorem selectedPath_mem_normalizedRequestFan
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    selectedPath U S K r ∈
      (GroundingAssembly.normalizedRequestFan S K r).paths :=
  (selectedPath_mem_controlledRequestFan U S K r).1

theorem selectedPath_not_mem_forbidden
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    selectedPath U S K r ∉ forbiddenPaths K r :=
  (selectedPath_mem_controlledRequestFan U S K r).2

theorem selectedPath_not_mem_hangingLadder
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    selectedPath U S K r ∉ K.hangingLadder r := by
  intro h
  exact selectedPath_not_mem_forbidden U S K r (Or.inl h)

theorem selectedPath_not_mem_hangingFragment
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    selectedPath U S K r ∉ K.hangingFragment r := by
  intro h
  exact selectedPath_not_mem_forbidden U S K r (Or.inr h)

theorem selectedPath_finish
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    (selectedPath U S K r).finish = requestAuxVertex r := by
  exact Set.mem_singleton_iff.1
    ((GroundingAssembly.normalizedRequestFan S K r).ends_in_join
      (selectedPath_mem_normalizedRequestFan U S K r))

theorem selectedPath_pairwiseDisjoint
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S) :
    Set.PairwiseDisjoint Set.univ
      (fun r : Request L S.cut => (selectedPath U S K r).support) := by
  intro r _hr s _hs hrs
  let rank := GroundingAssembly.requestRank U S
  rcases lt_trichotomy (rank r) (rank s) with hrslt | hrseq | hrslt
  · have hsFresh := (selectedPath_spec U S K s).2.2
    exact (hsFresh (rank r) hrslt (selectedPath U S K r)
      (selectedPath_spec U S K r).1).symm
  · exact False.elim (hrs (rank.injective hrseq))
  · have hrFresh := (selectedPath_spec U S K r).2.2
    exact hrFresh (rank s) hrslt (selectedPath U S K s)
      (selectedPath_spec U S K s).1

/-- The controlled selected paths form an `X`--request-cut warp. -/
def selectedWarp
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S) :
    Popular.XSWarp L.lambda (GroundingSelection.requestCut L S.cut) where
  paths := Set.range (selectedPath U S K)
  disjoint := by
    rintro p ⟨r, rfl⟩ q ⟨s, rfl⟩ hpq
    apply selectedPath_pairwiseDisjoint U S K (Set.mem_univ r) (Set.mem_univ s)
    intro hrs
    subst s
    exact hpq rfl
  starts_in_source := by
    rintro p ⟨r, rfl⟩
    exact (controlledRequestFan S K r).starts_in_source
      (selectedPath_mem_controlledRequestFan U S K r)
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

/-- Every member of the selected warp comes with a request and the
two avoidance conclusions needed by the grounding decoder. -/
theorem selectedWarp_member_avoids_controls
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    {p : Path L} (hp : p ∈ (selectedWarp U S K).paths) :
    ∃ r : Request L S.cut,
      p = selectedPath U S K r ∧
      p ∉ K.hangingLadder r ∧ p ∉ K.hangingFragment r := by
  obtain ⟨r, rfl⟩ := hp
  exact ⟨r, rfl, selectedPath_not_mem_hangingLadder U S K r,
    selectedPath_not_mem_hangingFragment U S K r⟩

end GroundingControlledAssembly
end Erdos599
