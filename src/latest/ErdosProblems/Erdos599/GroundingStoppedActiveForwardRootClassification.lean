/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingActiveRequestRootTransfer

/-!
# Unrooted retained-forward points at a stopping frontier

The forward-prefix transfer theorem is valid at the actual stopping frontier
`T`: once the selected route's initial and every backward-link entry are
rooted, every retained forward vertex is rooted.  This file records its exact
contrapositive.  It avoids the invalid empty-frontier-to-`T` transport and is
the native input for the selected-owner rank recursion.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedDecode

open _root_.Erdos599.DirectedPath Alternating

universe u

variable {V I : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Exact source-side alternatives exposed by an unrooted retained forward
vertex of an active selected request. -/
inductive ActiveRetainedForwardVertexUnrootedOutcome
    {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T A : Set V)
    (c : ActiveControlRequestAt U S K T) : Prop
  | initial
      (not_rooted : ¬ ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T) a
          (selectedRequestTrace U S K (chosenRequest c.1)).initial)
  | backwardOwner
      (link : Link Gamma.graph)
      (parent : Gamma.DPath)
      (link_mem : link ∈ (selectedErasedCompression U S K
        (chosenRequest c.1)).path.links)
      (direction : link.direction = .backward)
      (parent_mem : parent ∈ J.ladder.paths)
      (subpath : link.path.IsSubpathOf parent)
      (not_rooted : ¬ ∃ a ∈ A,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T)
          a link.path.start)

/-- Contrapositive of boundary-parametric retained-forward root transfer.
No activity or edge relation is transported from a different frontier. -/
theorem activeRequestAt_retainedForwardVertex_unrooted_outcome
    {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T A : Set V)
    (c : ActiveControlRequestAt U S K T)
    {x : V}
    (hx : x ∈ retainedForwardVerticesAt T
      (selectedErasedCompression U S K (chosenRequest c.1)).path)
    (hnot : ¬ ∃ a ∈ A,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K T) a x) :
    ActiveRetainedForwardVertexUnrootedOutcome U S K T A c := by
  classical
  by_cases hinitial : ∃ a ∈ A,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K T) a
        (selectedRequestTrace U S K (chosenRequest c.1)).initial
  · by_cases hbackward : ∀ (l : Link Gamma.graph),
        l ∈ (selectedErasedCompression U S K
            (chosenRequest c.1)).path.links →
        l.direction = .backward →
        ∀ parent ∈ J.ladder.paths, l.path.IsSubpathOf parent →
          ∃ a ∈ A,
            Relation.ReflTransGen
              (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K T)
              a l.path.start
    · exact False.elim <| hnot <|
        activeRequestAt_retainedForwardVertex_rooted_of_anchor_reachability
          U S K T c hinitial hbackward hx
    · push_neg at hbackward
      obtain ⟨l, hlmem, hldir, parent, hparent, hsub,
        hnotRooted⟩ := hbackward
      refine .backwardOwner l parent hlmem hldir hparent hsub ?_
      rintro ⟨a, ha, hareach⟩
      exact hnotRooted a ha hareach
  · exact .initial hinitial

end GroundingErasedDecode
end Erdos599

#print axioms
  Erdos599.GroundingErasedDecode.activeRequestAt_retainedForwardVertex_unrooted_outcome
