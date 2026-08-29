/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFragmentPartition
import ErdosProblems.Erdos599.GroundingSelectedContactOrder

/-!
# Old cut vertices versus deleted-edge fragments

There are two different deletions in the source proof of Assertion 8.22.
The auxiliary web `Theta - S` deletes the old vertices `S_V` and the
represented ladder edges `S_E`.  The fragment family, however, is defined
immediately afterwards as

`G = Y - S_E`,

the maximal ladder fragments obtained by deleting only represented edges.
Thus a member of `G`, and even a retained member of `G0`, need not avoid
`S_V`.  The relevant avoidance statement is instead local: an original
path avoiding `BB = S_V union BL` cannot contact a fragment at a point of
`S_V`, and an off-apex old contact of one of the normalized auxiliary
routes cannot lie in `S_V`.

This file records both sides of that distinction.  The first two theorems
are a formal counterexample schema to the tempting but false assertion that
all deleted-edge fragments avoid `CV`.  The remaining theorems are the
contact-avoidance interfaces needed by the grounding switch.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingCVFragmentAudit

open DirectedPath
open PopularGroundingBridge

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-! ## Deleted-edge fragments can contain old cut vertices -/

/-- If an old cut vertex lies on a ladder member, the deleted-edge
partition still has a fragment containing it.  In particular, membership
in `fragments L C` does not imply avoidance of `CV L C`. -/
theorem exists_fragment_meeting_CV
    (L : Input Gamma I) (C : Set (LV L))
    {p : Gamma.DPath} (hp : p ∈ L.ladder.paths)
    {x : V} (hxP : x ∈ p.support) (hxC : x ∈ GroundingCut.CV L C) :
    ∃ P : L.Fragment,
      P.parent = p ∧ P ∈ GroundingCut.fragments L C ∧
        x ∈ P.path.support ∩ GroundingCut.CV L C := by
  obtain ⟨P, hparent, hP, hx⟩ :=
    GroundingFragmentPartition.exists_fragment_containing L C hp hxP
  exact ⟨P, hparent, hP, hx, hxC⟩

/-- The same phenomenon occurs in `G0` whenever the parent is not one of
the specially discarded grounded records.  The popular-separator
hypothesis is included literally to emphasize that none of its fields
changes the edge-only definition of the fragment partition. -/
theorem exists_G0_fragment_meeting_CV_of_parent_not_groundedRecord
    {kappa : Cardinal.{max u v}}
    (L : Input Gamma I) (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    {p : Gamma.DPath} (hp : p ∈ L.ladder.paths)
    (hpNotRecord : p ∉ L.groundedRecords)
    {x : V} (hxP : x ∈ p.support)
    (hxC : x ∈ GroundingCut.CV L S.cut) :
    ∃ P : L.Fragment,
      P.parent = p ∧ P ∈ GroundingCut.G0 L S.cut ∧
        x ∈ P.path.support ∩ GroundingCut.CV L S.cut := by
  obtain ⟨P, hparent, hP, hx⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      L S.cut hp hxP
  have hparentNot : P.parent ∉ L.groundedRecords := by
    simpa only [hparent] using hpNotRecord
  have hPG0 : P ∈ GroundingCut.G0 L S.cut :=
    GroundingCut.fragment_mem_G0_of_parent_not_groundedRecord
      L S.cut P hP hparentNot
  exact ⟨P, hparent, hPG0, hx, hxC⟩

/-- A proposition-level refutation of the false universal statement that
all retained fragments avoid the old part of a popular separator. -/
theorem not_all_G0_fragments_avoid_CV_of_parent_not_groundedRecord
    {kappa : Cardinal.{max u v}}
    (L : Input Gamma I) (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    {p : Gamma.DPath} (hp : p ∈ L.ladder.paths)
    (hpNotRecord : p ∉ L.groundedRecords)
    {x : V} (hxP : x ∈ p.support)
    (hxC : x ∈ GroundingCut.CV L S.cut) :
    ¬ ∀ P : L.Fragment, P ∈ GroundingCut.G0 L S.cut →
      Disjoint P.path.support (GroundingCut.CV L S.cut) := by
  rintro hall
  obtain ⟨P, _hparent, hPG0, hx, hxCV⟩ :=
    exists_G0_fragment_meeting_CV_of_parent_not_groundedRecord
      L U S hp hpNotRecord hxP hxC
  exact Set.disjoint_left.1 (hall P hPG0) hx hxCV

/-! ### A concrete two-vertex fragment model -/

namespace Concrete

inductive Vertex
  | a | b
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj x y := x = a ∧ y = b

def ab : FinitePath graph where
  start := a
  finish := b
  walk := .cons ⟨rfl, rfl⟩ .nil
  isPath := by
    change [a, b].Nodup
    simp

@[simp] theorem ab_support : ab.support = ({a, b} : Set Vertex) := by
  ext x
  change x ∈ [a, b] ↔ _
  simp

def web : DWeb Vertex where
  graph := graph
  source := ∅
  target := ∅

def ladderPaths : Set web.DPath := {Sum.inl ab}

theorem ladderPaths_isWarp : web.IsWarp ladderPaths := by
  intro p hp q hq hpq
  simp only [ladderPaths, Set.mem_singleton_iff] at hp hq
  exact False.elim (hpq (hp.trans hq.symm))

def ladder : web.Warp := ⟨ladderPaths, ladderPaths_isWarp⟩

def input : PopularAuxiliary.Input web Empty where
  ladder := ladder
  groundedRecords := ∅
  finiteSource := ∅
  markerSet := ∅
  proxyPath i := nomatch i
  proxy_isRay i := nomatch i

abbrev ConcreteLV :=
  PopularAuxiliary.Input.LambdaVertex Vertex Empty

/-- Select the old copy of the initial vertex of the concrete ladder path,
and no represented edge. -/
def oldInitialCut : Set ConcreteLV :=
  {PopularAuxiliary.Input.LambdaVertex.old a}

@[simp] theorem a_mem_oldInitialCut_CV :
    a ∈ GroundingCut.CV input oldInitialCut := by
  simp [oldInitialCut, GroundingCut.CV,
    PopularAuxiliary.Input.oldPart]

@[simp] theorem oldInitialCut_CE_empty :
    GroundingCut.CE input oldInitialCut = ∅ := by
  ext e
  simp [oldInitialCut, GroundingCut.CE,
    PopularAuxiliary.Input.edgePart]

/-- In the explicit one-edge ladder, deleting the old initial vertex from
the auxiliary web does not delete it from `G`: a retained `G0` fragment
still contains that vertex. -/
theorem concrete_G0_fragment_meets_CV :
    ∃ P : input.Fragment,
      P ∈ GroundingCut.G0 input oldInitialCut ∧
        a ∈ P.path.support ∩
          GroundingCut.CV input oldInitialCut := by
  have hp : (Sum.inl ab : web.DPath) ∈ input.ladder.paths := by
    exact Set.mem_singleton _
  have ha : a ∈
      (DirectedPath.Path.support (Sum.inl ab : web.DPath)) := by
    change a ∈ ab.support
    simp
  obtain ⟨P, _hparent, hP, haP⟩ :=
    GroundingFragmentPartition.exists_fragment_containing
      input oldInitialCut hp ha
  have hparentNot : P.parent ∉ input.groundedRecords := by
    simp [input]
  have hPG0 := GroundingCut.fragment_mem_G0_of_parent_not_groundedRecord
    input oldInitialCut P hP hparentNot
  exact ⟨P, hPG0, haP, a_mem_oldInitialCut_CV⟩

end Concrete

/-! ## The contact-level statements actually used by the proof -/

/-- Every contact of an original path avoiding `BB` is outside `CV`.
This is the precise replacement for global `CV`-avoidance of fragments. -/
theorem ambient_avoiding_BB_contact_not_mem_CV
    (L : Input Gamma I) (C : Set (LV L))
    (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R (GroundingCut.BB L C))
    {x : V} (hxR : x ∈ R.support) :
    x ∉ GroundingCut.CV L C := by
  intro hxCV
  exact Set.disjoint_left.1 havoid hxR
    (GroundingCut.CV_subset_BB L C hxCV)

/-- Therefore a contact of a `BB`-avoiding original path with a surviving
fragment lies in the vertex-residual part of that fragment, even though the
fragment as a whole may contain old cut vertices. -/
theorem ambient_fragment_contact_not_mem_CV
    (L : Input Gamma I) (C : Set (LV L))
    (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R (GroundingCut.BB L C))
    (P : L.Fragment) (_hP : P ∈ GroundingCut.fragments L C)
    {x : V} (hxR : x ∈ R.support) (_hxP : x ∈ P.path.support) :
    x ∉ GroundingCut.CV L C :=
  ambient_avoiding_BB_contact_not_mem_CV L C R havoid hxR

/-- An old contact of a normalized request route, away from its cut apex,
is not an old cut vertex.  This is an immediate consequence of the route
normalization theorem: the apex is its only possible cut vertex. -/
theorem normalizedRoute_offApex_oldContact_not_mem_CV
    {J : Type u} {L : PopularAuxiliary.Input Gamma J}
    {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    {p : FinitePath L.lambda.graph}
    (hp : p ∈ (GroundingAssembly.normalizedRequestFan S r).paths)
    {x : V}
    (hx : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈ p.support)
    (hoff : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ≠
      requestAuxVertex r) :
    x ∉ GroundingCut.CV L S.cut := by
  intro hxCV
  have hapex := GroundingAssembly.normalizedRequestFan_cut_normalized
    S r hp ⟨hx, hxCV⟩
  exact hoff (Set.mem_singleton_iff.mp hapex)

/-- The component-compatible selected request route has the same
off-apex old-contact avoidance property. -/
theorem strongSelectedPath_offApex_oldContact_not_mem_CV
    {J : Type u} {L : PopularAuxiliary.Input Gamma J}
    {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    {x : V}
    (hx : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈
      (GroundingSimultaneousDecode.strongSelectedPath U S K r).support)
    (hoff : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ≠
      requestAuxVertex r) :
    x ∉ GroundingCut.CV L S.cut := by
  apply normalizedRoute_offApex_oldContact_not_mem_CV S r
    (GroundingSimultaneousDecode.strongSelectedPath_mem_controlledRequestFan
      U S K r).1 hx hoff

end GroundingCVFragmentAudit
end Erdos599
