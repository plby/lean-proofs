/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularGroundingBridge
import ErdosProblems.Erdos599.PopularSwitching
import ErdosProblems.Erdos599.RegularCardinal

/-!
# The recursive selection in Assertions 8.19--8.20

This file performs the choice made after the popular separator has been
constructed in Section 8 of Aharoni--Berger.  A request is either an old
vertex of the auxiliary cut or a represented edge of the ladder.  Theorem
8.4 supplies a stationary singleton in-fan at every request.

The two kinds of forbidden members are recorded structurally below.
Hanging-ladder collisions carry the regressive rank and countable trace of
Assertion 8.19.  Hanging-fragment collisions carry the represented part of
the popular cut met by the path, and Assertion 8.20 turns a stationary such
subfamily into a strongly popular subset of the cut.  Thus neither
nonstationarity conclusion is an input.

After deleting those two nonstationary subfamilies, we recursively choose
one member of every request fan.  Before the recursion we also discard paths
which meet the auxiliary representative of another request.  At a stage
`r`, collision with any one earlier chosen finite path is nonstationary,
because that path has finite (hence countable) support disjoint from the
apex of the `r`-fan.  There are fewer than `kappa` earlier requests, so
regularity leaves a stationary remainder.  The chosen paths are therefore
pairwise vertex-disjoint and form an honest finite warp in `Lambda`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingSelection

open DirectedPath Stationary
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev LV (L : PopularAuxiliary.Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

abbrev Path (L : PopularAuxiliary.Input Gamma I) :=
  FinitePath L.lambda.graph

/-- The auxiliary vertices at which the Section 8 switching requests end.
This is the tagged version of the transformed cut; applying
`requestVertex` gives the untagged set `controlVertices`. -/
def requestCut (L : PopularAuxiliary.Input Gamma I) (C : Set (LV L)) :
    Set (LV L) :=
  Set.range (@requestAuxVertex V I Gamma L C)

theorem requestAuxVertex_injective
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)} :
    Function.Injective
      (@requestAuxVertex V I Gamma L C) := by
  intro r s hrs
  cases r with
  | inl x =>
      cases s with
      | inl y =>
          exact congrArg Sum.inl <| Subtype.ext <|
            PopularAuxiliary.Input.LambdaVertex.old.inj hrs
      | inr y => cases hrs
  | inr x =>
      cases s with
      | inl y => cases hrs
      | inr y =>
          exact congrArg Sum.inr <| Subtype.ext <| Prod.ext
            (PopularAuxiliary.Input.LambdaVertex.edge.inj hrs).1
            (PopularAuxiliary.Input.LambdaVertex.edge.inj hrs).2

theorem requestCut_subset_cut
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)} :
    requestCut L C ⊆ C := by
  rintro _ ⟨r, rfl⟩
  exact requestAuxVertex_mem_cut r

@[simp]
theorem requestAuxVertex_ne_iff
    {L : PopularAuxiliary.Input Gamma I} {C : Set (LV L)}
    (r s : Request L C) :
    requestAuxVertex r ≠ requestAuxVertex s ↔ r ≠ s := by
  exact (requestAuxVertex_injective.eq_iff).not

/-! ## The two exact exceptional subfamilies -/

/-- Structural input for Assertions 8.19 and 8.20 at every request.

`hangingLadder r` consists of members of the local fan which meet a hanging
path of the limiting ladder away from their own apex.  The fields prefixed
by `ladder` are precisely the pressing-down data of Assertion 8.19.

`hangingFragment r` consists of members meeting a hanging fragment after
the represented cut edges have been deleted.  Assertion 8.20 supplies the
nonstationarity of their initial indices.  Keeping that derived conclusion
in the package also permits the canonical grounded selector to adjoin the
independently nonstationary paths starting at hanging finite records.
-/
structure Controls
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) where
  hangingLadder : Request L S.cut → Set (Path L)
  hangingFragment : Request L S.cut → Set (Path L)
  ladderRank : (r : Request L S.cut) → Below kappa → Below kappa
  ladderTrace : (r : Request L S.cut) → Below kappa → Set (LV L)
  ladderRank_regressive : ∀ r,
    IsRegressiveOn
      (Popular.initialIndicesOf U
        (PopularSwitching.restrictPaths (requestFan S r)
          (hangingLadder r)).paths
        (PopularSwitching.restrictPaths (requestFan S r)
          (hangingLadder r)).starts_in_source)
      (ladderRank r)
  ladderTrace_countable : ∀ r i, (ladderTrace r i).Countable
  ladderTrace_disjoint_apex : ∀ r i,
    Disjoint (ladderTrace r i) {requestAuxVertex r}
  hangingLadder_meets : ∀ r p
      (hp : p ∈ (PopularSwitching.restrictPaths (requestFan S r)
        (hangingLadder r)).paths),
    ∃ x ∈ ladderTrace r
        (ladderRank r
          (U.f ⟨p.start,
            (PopularSwitching.restrictPaths (requestFan S r)
              (hangingLadder r)).starts_in_source hp⟩)),
      x ∈ p.support
  fragmentIndices_nonstationary : ∀ r,
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U
        (PopularSwitching.restrictPaths (requestFan S r)
          (hangingFragment r)).paths
        (PopularSwitching.restrictPaths (requestFan S r)
          (hangingFragment r)).starts_in_source)

/-- Assertion 8.19: the members of a local fan which collide with hanging
ladder paths have nonstationary initial-index set. -/
theorem hangingLadder_indices_nonstationary
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : Controls S)
    (r : Request L S.cut) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U
        (PopularSwitching.restrictPaths (requestFan S r)
          (K.hangingLadder r)).paths
        (PopularSwitching.restrictPaths (requestFan S r)
          (K.hangingLadder r)).starts_in_source) := by
  apply PopularSwitching.initialIndices_nonstationary_of_regressive_countable_collisions
    U
    (PopularSwitching.restrictPaths (requestFan S r)
      (K.hangingLadder r))
    (K.ladderRank r) (K.ladderTrace r)
  · exact K.ladderRank_regressive r
  · exact K.ladderTrace_countable r
  · exact K.ladderTrace_disjoint_apex r
  · exact K.hangingLadder_meets r

/-- A subset of the popular cut is not strongly popular. -/
theorem not_stronglyPopular_of_subset_cut
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) {C : Set (LV L)}
    (hC : C ⊆ S.cut) :
    ¬ Popular.IsStronglyPopular U C := by
  intro h
  exact S.not_strongly_popular (h.mono hC)

/-- Assertion 8.20: the members which meet a hanging fragment have
nonstationary initial-index set. -/
theorem hangingFragment_indices_nonstationary
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : Controls S)
    (r : Request L S.cut) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U
        (PopularSwitching.restrictPaths (requestFan S r)
          (K.hangingFragment r)).paths
        (PopularSwitching.restrictPaths (requestFan S r)
          (K.hangingFragment r)).starts_in_source) := by
  exact K.fragmentIndices_nonstationary r

/-! ## Predicate-index bookkeeping -/

/-- Initial indices of the members of `F` satisfying `P`. -/
def restrictedIndices
    {W : Type u} {web : DWeb W} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed web kappa) {T : Set W}
    (F : Popular.JoinedFamily web T)
    (P : Set (FinitePath web.graph)) : Set (Below kappa) :=
  Popular.initialIndicesOf U (PopularSwitching.restrictPaths F P).paths
    (PopularSwitching.restrictPaths F P).starts_in_source

theorem mem_restrictedIndices_of
    {W : Type u} {web : DWeb W} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed web kappa) {T : Set W}
    (F : Popular.JoinedFamily web T)
    (P : Set (FinitePath web.graph)) {p : FinitePath web.graph}
    (hp : p ∈ F.paths) (hpP : p ∈ P) :
    U.f ⟨p.start, F.starts_in_source hp⟩ ∈
      restrictedIndices U F P := by
  let hp' : p ∈ (PopularSwitching.restrictPaths F P).paths := ⟨hp, hpP⟩
  refine ⟨p, hp', ?_⟩
  congr 1

theorem not_isStationaryBelow_union
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) {A B : Set (Below kappa)}
    (hA : ¬ IsStationaryBelow kappa A)
    (hB : ¬ IsStationaryBelow kappa B) :
    ¬ IsStationaryBelow kappa (A ∪ B) := by
  let F : Bool → Set (Below kappa)
    | false => A
    | true => B
  have hF : ∀ b, ¬ IsStationaryBelow kappa (F b) := by
    intro b
    cases b <;> assumption
  have hU := not_isStationaryBelow_iUnion_of_countable
    hregular huncountable hF
  have heq : (⋃ b : Bool, F b) = A ∪ B := by
    ext x
    simp [F]
  rw [← heq]
  exact hU

/-! ## Simultaneous control-aware pruning -/

/-- The members of a request fan which avoid both exceptional collision
classes.  This is the actual family from which Assertion 8.20 chooses: it
is not enough to prove the two bad classes nonstationary and then continue
selecting from the unpruned fan. -/
def controlledRequestFan
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : Controls S)
    (r : Request L S.cut) :
    Popular.JoinedFamily L.lambda {requestAuxVertex r} :=
  PopularSwitching.restrictPaths (requestFan S r)
    {p | p ∉ K.hangingLadder r ∧ p ∉ K.hangingFragment r}

@[simp]
theorem mem_controlledRequestFan
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : Controls S)
    (r : Request L S.cut) (p : Path L) :
    p ∈ (controlledRequestFan S K r).paths ↔
      p ∈ (requestFan S r).paths ∧
        p ∉ K.hangingLadder r ∧ p ∉ K.hangingFragment r :=
  Iff.rfl

/-- Removing both structurally defined exceptional classes leaves a
stationary request fan.  This is the κ-complete-ideal calculation needed
before the transfinite choice recursion. -/
theorem controlledRequestFan_stationary
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : Controls S)
    (r : Request L S.cut) :
    IsStationaryBelow kappa
      (Popular.initialIndicesOf U (controlledRequestFan S K r).paths
        (controlledRequestFan S K r).starts_in_source) := by
  let B : Set (Below kappa) :=
    restrictedIndices U (requestFan S r) (K.hangingLadder r)
  let F : Set (Below kappa) :=
    restrictedIndices U (requestFan S r) (K.hangingFragment r)
  have hB : ¬ IsStationaryBelow kappa B :=
    hangingLadder_indices_nonstationary S K r
  have hF : ¬ IsStationaryBelow kappa F :=
    hangingFragment_indices_nonstationary S K r
  have hbad : ¬ IsStationaryBelow kappa (B ∪ F) :=
    not_isStationaryBelow_union U.regular U.uncountable hB hF
  have hremain : IsStationaryBelow kappa
      (Popular.initialIndicesOf U (requestFan S r).paths
        (requestFan S r).starts_in_source \ (B ∪ F)) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      U.regular U.uncountable (requestFan_stationary S r) hbad
  apply hremain.mono
  rintro a ⟨⟨p, hp, hpa⟩, haBad⟩
  have hpLadder : p ∉ K.hangingLadder r := by
    intro hpLadder
    apply haBad
    apply Or.inl
    have hindex := mem_restrictedIndices_of U (requestFan S r)
      (K.hangingLadder r) hp hpLadder
    exact hpa ▸ hindex
  have hpFragment : p ∉ K.hangingFragment r := by
    intro hpFragment
    apply haBad
    apply Or.inr
    have hindex := mem_restrictedIndices_of U (requestFan S r)
      (K.hangingFragment r) hp hpFragment
    exact hpa ▸ hindex
  let hpControlled : p ∈ (controlledRequestFan S K r).paths :=
    ⟨hp, hpLadder, hpFragment⟩
  refine ⟨p, hpControlled, ?_⟩
  simpa only [controlledRequestFan, PopularSwitching.restrictPaths] using hpa

end GroundingSelection
end Erdos599
