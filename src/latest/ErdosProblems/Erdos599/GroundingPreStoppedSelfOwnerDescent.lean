/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedUniformRecursiveRootOutcome
import ErdosProblems.Erdos599.GroundingFragmentResidualOrder

/-!
# Position descent for self-owned pre-stopped deletions

The control-rank classification of a deleted parent edge has an equality
case.  Equality is not a terminal case: the same selected route may use a
backward link on, or a forward departure from, the component which it
exposes.  Nevertheless both equality cases make strict progress in the
intrinsic order of that component.  The ambient start of a backward link is
strictly before every edge of the link, and the tail of a same-tail forward
conflict is strictly before the deleted head.

These facts are valid for both finite ladder paths and rays.  Thus they are
the position component of the lexicographic `(control rank, path position)`
measure needed by the remaining root recursion; no unjustified finiteness of
the owner is used.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath Alternating
open GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- The unique natural-number position of a vertex on a directed finite
path or ray.  The default value off the support is irrelevant; all exported
order lemmas carry the corresponding support hypotheses. -/
noncomputable def pathPosition (P : Gamma.DPath) (x : V) : ℕ :=
  by
    classical
    exact if hx : x ∈ P.support then
      Nat.find ((GroundingCut.mem_support_iff_exists_occursAt P x).1 hx)
    else 0

theorem occursAt_pathPosition (P : Gamma.DPath) {x : V}
    (hx : x ∈ P.support) :
    GroundingCut.OccursAt P (pathPosition P x) x := by
  classical
  rw [pathPosition, dif_pos hx]
  exact Nat.find_spec
    ((GroundingCut.mem_support_iff_exists_occursAt P x).1 hx)

/-- Strict intrinsic path order is strict order of the canonical natural
positions.  In particular the order on a ray is well-founded to the left. -/
theorem pathPosition_lt_of_before
    (P : Gamma.DPath) {x y : V}
    (hxy : GroundingCut.Before P x y) :
    pathPosition P x < pathPosition P y := by
  rcases hxy.1 with ⟨m, n, hmx, hny, hmn⟩
  have hx : x ∈ P.support := GroundingCut.occursAt_mem_support hmx
  have hy : y ∈ P.support := GroundingCut.occursAt_mem_support hny
  have hxm : pathPosition P x = m :=
    GroundingCutDecoder.occursAt_index_injective
      (occursAt_pathPosition P hx) hmx
  have hyn : pathPosition P y = n :=
    GroundingCutDecoder.occursAt_index_injective
      (occursAt_pathPosition P hy) hny
  rw [hxm, hyn]
  apply lt_of_le_of_ne hmn
  intro hnm
  apply hxy.2
  have hsame : GroundingCut.OccursAt P m y := by
    simpa only [hnm] using hny
  cases P with
  | inl p =>
      exact hmx.2.symm.trans hsame.2
  | inr r =>
      exact hmx.symm.trans hsame

/-- A finite directed walk whose edges lie on a directed path moves
monotonically in the intrinsic order of that path. -/
theorem walk_beforeEq_of_edgeSet_subset
    (P : Gamma.DPath) {a b : V}
    (q : Walk Gamma.graph a b)
    (ha : a ∈ P.support) (hq : q.edgeSet ⊆ P.edgeSet) :
    GroundingCut.BeforeEq P a b := by
  induction q with
  | nil => exact GroundingCut.beforeEq_refl ha
  | @cons a c b hac q ih =>
      have hacP : (a, c) ∈ P.edgeSet := by
        apply hq
        simp
      have hcP : c ∈ P.support :=
        (P.edgeSet_subset_support_prod hacP).2
      have hqP : q.edgeSet ⊆ P.edgeSet := by
        intro e he
        apply hq
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff]
        exact Or.inr he
      exact GroundingFragmentResidualOrder.beforeEq_trans
        (GroundingCut.beforeEq_of_mem_edgeSet hacP) (ih hcP hqP)

/-- The initial vertex of a finite subpath occurs before every vertex of
that subpath on its ambient directed path. -/
theorem finiteSubpath_start_beforeEq_of_mem
    (P : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hsub : q.IsSubpathOf P) {x : V} (hx : x ∈ q.support) :
    GroundingCut.BeforeEq P q.start x := by
  let m : q.walk.Meets ({x} : Set V) :=
    ⟨x, hx, Set.mem_singleton x⟩
  let r := q.firstHit ({x} : Set V) m
  have hrStart : r.start = q.start := rfl
  have hrFinish : r.finish = x := by
    exact Set.mem_singleton_iff.mp (q.firstHit_finish_mem ({x} : Set V) m)
  have hrEdges : r.edgeSet ⊆ P.edgeSet :=
    (q.firstHit_edgeSet_subset ({x} : Set V) m).trans hsub.2
  have hstart : q.start ∈ P.support :=
    hsub.1 q.start_mem_support
  simpa only [hrStart, hrFinish] using
    walk_beforeEq_of_edgeSet_subset P r.walk hstart hrEdges

/-- The ambient start of a backward link is strictly before the head of
each edge of that link on its owner.  This is the exact path-position
descent in the self-owned backward constructor. -/
theorem backwardLink_start_before_deletedHead
    (Y : Gamma.DPath) (l : Link Gamma.graph)
    (hsub : l.path.IsSubpathOf Y) {u z : V}
    (huz : (u, z) ∈ l.path.edgeSet) :
    GroundingCut.Before Y l.path.start z := by
  refine ⟨finiteSubpath_start_beforeEq_of_mem Y l.path hsub
    ((l.path.edgeSet_subset_support_prod huz).2), ?_⟩
  exact Ne.symm (FinitePath.target_ne_start_of_mem_edgeSet l.path huz)

/-- Numerical form of `backwardLink_start_before_deletedHead`, ready for a
well-founded induction on the position inside a fixed owner path. -/
theorem backwardLink_start_pathPosition_lt_deletedHead
    (Y : Gamma.DPath) (l : Link Gamma.graph)
    (hsub : l.path.IsSubpathOf Y) {u z : V}
    (huz : (u, z) ∈ l.path.edgeSet) :
    pathPosition Y l.path.start < pathPosition Y z :=
  pathPosition_lt_of_before Y
    (backwardLink_start_before_deletedHead Y l hsub huz)

/-- The tail of a deleted parent edge is strictly before its head on the
exposed parent.  In a same-tail forward conflict this tail is exactly the
source-side anchor from which the retained selected forward edge departs. -/
theorem forwardTail_before_deletedHead
    (Y : Gamma.DPath) {u z : V} (huz : (u, z) ∈ Y.edgeSet) :
    GroundingCut.Before Y u z := by
  refine ⟨GroundingCut.beforeEq_of_mem_edgeSet huz, ?_⟩
  exact GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet huz

/-- Numerical same-tail position descent. -/
theorem forwardTail_pathPosition_lt_deletedHead
    (Y : Gamma.DPath) {u z : V} (huz : (u, z) ∈ Y.edgeSet) :
    pathPosition Y u < pathPosition Y z :=
  pathPosition_lt_of_before Y (forwardTail_before_deletedHead Y huz)

/-! ## The combined control-rank/path-position recursion order -/

/-- One exposed-parent point whose source reachability may be requested by
the recursive root classifier. -/
structure ActiveExposedPoint
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S) where
  control : ActiveControlRequestAt U S K ∅
  parent : Gamma.DPath
  point : V
  point_mem : point ∈ parent.support

/-- Lexicographic key: request chronology first, then the natural position
on the currently exposed parent. -/
def ActiveExposedPoint.recursionKey
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    (s : ActiveExposedPoint K) : Stationary.Below kappa × ℕ :=
  (controlRank U S s.control.1, pathPosition s.parent s.point)

/-- The well-founded relation used by root recursion.  A recursive call may
move to any owner of strictly smaller control rank; at equal rank it must
move strictly left on the same exposed parent. -/
def ActiveExposedPoint.Precedes
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S} :
    ActiveExposedPoint K → ActiveExposedPoint K → Prop :=
  (Prod.Lex (fun a b : Stationary.Below kappa ↦ a < b)
    (fun m n : ℕ ↦ m < n)).onFun ActiveExposedPoint.recursionKey

theorem ActiveExposedPoint.precedes_wellFounded
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S} :
    WellFounded (@ActiveExposedPoint.Precedes V Gamma kappa I J U S K) := by
  exact InvImage.wf ActiveExposedPoint.recursionKey
    (wellFounded_lt.prod_lex wellFounded_lt)

/-- Strictly earlier control owners decrease the primary coordinate,
independently of their exposed parent and point. -/
theorem ActiveExposedPoint.precedes_of_controlRank_lt
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    {s t : ActiveExposedPoint K}
    (h : controlRank U S s.control.1 < controlRank U S t.control.1) :
    s.Precedes t := by
  exact Prod.Lex.left _ _ h

/-- A self-owned backward link decreases the secondary path-position
coordinate of the combined recursion key. -/
theorem ActiveExposedPoint.backwardSelf_precedes
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    (c : ActiveControlRequestAt U S K ∅)
    (Y : Gamma.DPath) (l : Link Gamma.graph)
    (hsub : l.path.IsSubpathOf Y) {u z : V}
    (huz : (u, z) ∈ l.path.edgeSet) :
    ({ control := c
       parent := Y
       point := l.path.start
       point_mem := hsub.1 l.path.start_mem_support } :
        ActiveExposedPoint K).Precedes
      ({ control := c
         parent := Y
         point := z
         point_mem := hsub.1
           ((l.path.edgeSet_subset_support_prod huz).2) } :
        ActiveExposedPoint K) := by
  exact Prod.Lex.right _
    (backwardLink_start_pathPosition_lt_deletedHead Y l hsub huz)

/-- A self-owned same-tail conflict likewise decreases the secondary
path-position coordinate. -/
theorem ActiveExposedPoint.forwardTailSelf_precedes
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    (c : ActiveControlRequestAt U S K ∅)
    (Y : Gamma.DPath) {u z : V} (huz : (u, z) ∈ Y.edgeSet) :
    ({ control := c
       parent := Y
       point := u
       point_mem := (Y.edgeSet_subset_support_prod huz).1 } :
        ActiveExposedPoint K).Precedes
      ({ control := c
         parent := Y
         point := z
         point_mem := (Y.edgeSet_subset_support_prod huz).2 } :
        ActiveExposedPoint K) := by
  exact Prod.Lex.right _
    (forwardTail_pathPosition_lt_deletedHead Y huz)

end Assertion822PreStoppedRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.pathPosition_lt_of_before
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.walk_beforeEq_of_edgeSet_subset
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.finiteSubpath_start_beforeEq_of_mem
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.backwardLink_start_before_deletedHead
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.backwardLink_start_pathPosition_lt_deletedHead
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.forwardTail_before_deletedHead
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.forwardTail_pathPosition_lt_deletedHead
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ActiveExposedPoint.precedes_wellFounded
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ActiveExposedPoint.backwardSelf_precedes
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ActiveExposedPoint.forwardTailSelf_precedes
