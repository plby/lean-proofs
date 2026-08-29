/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSelection
import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# Source-faithful exceptional families in Assertions 8.19--8.20

`GroundingSelection.Controls` records exactly the pressing-down and cut
contact data used by the recursive selection, but by itself does not say
that its two exceptional path families are the geometric exceptional
families from the paper.  In particular, both families could otherwise be
chosen empty.

This file defines the actual collision predicates and a non-vacuous wrapper
whose bad families are equal to those predicates.  It also separates the two
genuinely missing geometric propositions: common earlier-stage trace data
for hanging ladder collisions, and common cut-contact data for hanging
fragment collisions.  No instance of either proposition is postulated.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingConcreteControls

open DirectedPath Stationary
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev LV (L : PopularAuxiliary.Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

abbrev Path (L : PopularAuxiliary.Input Gamma I) :=
  FinitePath L.lambda.graph

/-- A local fan member collides away from its own apex with a hanging path
of the limiting ladder.  The hanging component itself may contain the apex;
source condition (b) permits only that one point, not arbitrary further
contacts with the same component. -/
def hangingLadderCollision
    (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L))
    (r : Request L C) (p : Path L) : Prop :=
  ∃ Y : Gamma.DPath,
    Y ∈ PopularAuxiliary.hangingPaths Gamma L.ladder.paths ∧
      ∃ a ∈ PopularSwitching.ladderTrace L Y \ {requestAuxVertex r},
        a ∈ p.support

/-- A surviving fragment is preceded on its parent ladder path by an edge
represented in the auxiliary cut.  This is the literal geometric content of
being a fragment "hanging in air" in Assertion 8.20. -/
def hasCutPredecessor
    (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) : Prop :=
  ∃ s : V × V, s ∈ GroundingCut.CE L C ∧
    s ∈ P.parent.edgeSet ∧ s.2 = P.path.initial

/-- A local fan member meets a cut-preceded hanging fragment away from the
request apex.  The predecessor requirement excludes a first fragment with
no deleted edge before it; the apex clause is the source's phrase "not
containing p". -/
def hangingFragmentCollision
    (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L))
    (r : Request L C) (p : Path L) : Prop :=
  ∃ P : L.Fragment,
    P ∈ GroundingCut.fragments L C ∧ P.IsHanging ∧
      hasCutPredecessor L C P ∧ requestVertex r ∉ P.path.support ∧
      ∃ v ∈ P.path.support,
        (PopularAuxiliary.Input.LambdaVertex.old v : LV L) ∈ p.support

/-- The old-vertex trace of a fragment which omits a request vertex is
disjoint from the corresponding auxiliary request apex.  For an edge
request this is disjointness of constructors; for an old request it is
exactly the displayed omission. -/
theorem oldImage_fragment_disjoint_requestAuxVertex
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    {r : Request L C} {P : L.Fragment}
    (hapex : requestVertex r ∉ P.path.support) :
    Disjoint
      (PopularAuxiliary.Input.LambdaVertex.old '' P.path.support)
      {requestAuxVertex r} := by
  rw [Set.disjoint_left]
  rintro z ⟨v, hvP, rfl⟩ hz
  have hz' :
      (PopularAuxiliary.Input.LambdaVertex.old v : LV L) =
        requestAuxVertex r := Set.mem_singleton_iff.mp hz
  cases r with
  | inl x =>
      apply hapex
      change x.1 ∈ P.path.support
      exact PopularAuxiliary.Input.LambdaVertex.old.inj hz' ▸ hvP
  | inr e => cases hz'

/-- Unpack a hanging-ladder collision with all source-level witnesses. -/
theorem hangingLadderCollision_iff
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    {r : Request L C} {p : Path L} :
    hangingLadderCollision L C r p ↔
      ∃ Y : Gamma.DPath, Y ∈ L.ladder.paths ∧
        PopularAuxiliary.IsHangingPath Gamma Y ∧
          ∃ a ∈ PopularSwitching.ladderTrace L Y \ {requestAuxVertex r},
            a ∈ p.support := by
  constructor
  · rintro ⟨Y, ⟨hY, hhang⟩, a, ha, hap⟩
    exact ⟨Y, hY, hhang, a, ha, hap⟩
  · rintro ⟨Y, hY, hhang, a, ha, hap⟩
    exact ⟨Y, ⟨hY, hhang⟩, a, ha, hap⟩

/-- Unpack a hanging-fragment collision, including its deleted predecessor
and avoidance of the request apex. -/
theorem hangingFragmentCollision_iff
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    {r : Request L C} {p : Path L} :
    hangingFragmentCollision L C r p ↔
      ∃ P : L.Fragment,
        P ∈ GroundingCut.fragments L C ∧
          P.parent ∈ L.ladder.paths ∧
          PopularAuxiliary.IsHangingPath Gamma P.parent ∧
          hasCutPredecessor L C P ∧ requestVertex r ∉ P.path.support ∧
          P.path.support ⊆ P.parent.support ∧
          ∃ v ∈ P.path.support,
            (PopularAuxiliary.Input.LambdaVertex.old v : LV L) ∈ p.support := by
  constructor
  · rintro ⟨P, hP, hhang, hpred, hapex, v, hvP, hvp⟩
    exact ⟨P, hP, P.parent_mem, hhang, hpred, hapex,
      P.support_subset, v, hvP, hvp⟩
  · rintro ⟨P, hP, _hparent, hhang, hpred, hapex,
      _hsubset, v, hvP, hvp⟩
    exact ⟨P, hP, hhang, hpred, hapex, v, hvP, hvp⟩

/-- A colliding fan member has a nonterminal contact with a hanging ladder
path, even when the same component also contains the request apex. -/
theorem hangingLadderCollision_has_nonterminal_contact
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    {r : Request L C} {p : Path L}
    (hpfinish : p.finish = requestAuxVertex r)
    (hp : hangingLadderCollision L C r p) :
    ∃ Y : Gamma.DPath, Y ∈ L.ladder.paths ∧
      PopularAuxiliary.IsHangingPath Gamma Y ∧
      ∃ a ∈ PopularSwitching.ladderTrace L Y,
        a ∈ p.support ∧ a ≠ p.finish := by
  rw [hangingLadderCollision_iff] at hp
  obtain ⟨Y, hY, hhang, a, haTrace, haPath⟩ := hp
  refine ⟨Y, hY, hhang, a, haTrace.1, haPath, ?_⟩
  intro hafinish
  exact haTrace.2 (by
    rw [Set.mem_singleton_iff, ← hpfinish, ← hafinish])

/-! ## The two exact missing geometric propositions -/

/-- Assertion 8.19 data for the *actual* hanging-ladder collision family.
The substantive missing theorem is existence of this structure from the
ladder laws. -/
structure HangingLadderRankData
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) where
  rank : Request L S.cut → Below kappa → Below kappa
  trace : Request L S.cut → Below kappa → Set (LV L)
  rank_regressive : ∀ r,
    IsRegressiveOn
      (Popular.initialIndicesOf U
        (PopularSwitching.restrictPaths (requestFan S r)
          {p | hangingLadderCollision L S.cut r p}).paths
        (PopularSwitching.restrictPaths (requestFan S r)
          {p | hangingLadderCollision L S.cut r p}).starts_in_source)
      (rank r)
  trace_countable : ∀ r i, (trace r i).Countable
  trace_disjoint_apex : ∀ r i,
    Disjoint (trace r i) {requestAuxVertex r}
  collision_meets_trace : ∀ r p
      (hp : p ∈ (PopularSwitching.restrictPaths (requestFan S r)
        {q | hangingLadderCollision L S.cut r q}).paths),
    ∃ x ∈ trace r
        (rank r
          (U.f ⟨p.start,
            (PopularSwitching.restrictPaths (requestFan S r)
              {q | hangingLadderCollision L S.cut r q}).starts_in_source hp⟩)),
      x ∈ p.support

/-- Assertion 8.20 for the actual cut-preceded hanging-fragment collision
family.  Its proof is conditional on stationarity and first thins to
compatible last contacts; it does not produce a warp covering the entire
unthinned exceptional family. -/
structure HangingFragmentWarpData
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) where
  initialIndices_nonstationary : ∀ r,
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U
        (PopularSwitching.restrictPaths (requestFan S r)
          {q | hangingFragmentCollision L S.cut r q}).paths
        (PopularSwitching.restrictPaths (requestFan S r)
          {q | hangingFragmentCollision L S.cut r q}).starts_in_source)

/-- A source-faithful control package.  The equality fields prevent the two
exceptional families from being silently replaced by arbitrary (in
particular empty) subfamilies. -/
structure ConcreteControls
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    extends GroundingSelection.Controls S where
  hangingLadder_exact : ∀ r,
    hangingLadder r = {p | hangingLadderCollision L S.cut r p}
  hangingFragment_exact : ∀ r,
    hangingFragment r = {p | hangingFragmentCollision L S.cut r p}

/-- The two missing geometric data packages assemble into genuine concrete
controls, with definitional coverage of both bad families. -/
def ConcreteControls.ofData
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (HL : HangingLadderRankData S) (HF : HangingFragmentWarpData S) :
    ConcreteControls S where
  hangingLadder r := {p | hangingLadderCollision L S.cut r p}
  hangingFragment r := {p | hangingFragmentCollision L S.cut r p}
  ladderRank := HL.rank
  ladderTrace := HL.trace
  ladderRank_regressive := HL.rank_regressive
  ladderTrace_countable := HL.trace_countable
  ladderTrace_disjoint_apex := HL.trace_disjoint_apex
  hangingLadder_meets := HL.collision_meets_trace
  fragmentIndices_nonstationary := HF.initialIndices_nonstationary
  hangingLadder_exact _ := rfl
  hangingFragment_exact _ := rfl

/-- Concrete controls recover the exact Assertion 8.19 data package. -/
def ConcreteControls.toHangingLadderRankData
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} (K : ConcreteControls S) :
    HangingLadderRankData S where
  rank := K.ladderRank
  trace := K.ladderTrace
  rank_regressive := by
    intro r a ha
    apply K.ladderRank_regressive r a
    rcases ha with ⟨p, hp, hpa⟩
    refine ⟨p, ⟨hp.1, ?_⟩, hpa⟩
    rw [K.hangingLadder_exact r]
    exact hp.2
  trace_countable := K.ladderTrace_countable
  trace_disjoint_apex := K.ladderTrace_disjoint_apex
  collision_meets_trace := by
    intro r p hp
    have hp' : p ∈ (PopularSwitching.restrictPaths (requestFan S r)
        (K.hangingLadder r)).paths := by
      exact ⟨hp.1, (K.hangingLadder_exact r).symm.subset hp.2⟩
    obtain ⟨x, hx, hxp⟩ := K.hangingLadder_meets r p hp'
    exact ⟨x, hx, hxp⟩

/-- Concrete controls recover the exact Assertion 8.20 data package. -/
def ConcreteControls.toHangingFragmentWarpData
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} (K : ConcreteControls S) :
    HangingFragmentWarpData S where
  initialIndices_nonstationary := by
    intro r hstationary
    apply K.fragmentIndices_nonstationary r
    apply hstationary.mono
    rintro a ⟨p, hp, hpa⟩
    have hp' : p ∈ (PopularSwitching.restrictPaths (requestFan S r)
        (K.hangingFragment r)).paths := by
      exact ⟨hp.1, (K.hangingFragment_exact r).symm.subset hp.2⟩
    exact ⟨p, hp', hpa⟩

end GroundingConcreteControls
end Erdos599
