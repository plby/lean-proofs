/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingBBGeometry
import ErdosProblems.Erdos599.GroundingWellFoundedRoots

/-!
# Root and antichain reductions for the repaired grounding relation

This file turns the `Compatible` certificate for the literal switched
relation into its well-founded predecessor relation.  It isolates the two
remaining geometric statements needed by the finite rooted-warp constructor:

* classification of no-incoming roots of components reaching `BB`;
* incomparability of distinct points of `BB`.

No realization warp is introduced in these reductions.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingBBRootReduction

open Alternating GroundingErasedDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Compatibility makes the predecessor relation of the literal corrected
switch well founded. -/
theorem predecessor_wellFounded
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    (h : Compatible U S K) :
    WellFounded (fun x y : V ↦
      (x, y) ∈ erasedSelectedSwitchedEdges U S K) :=
  Alternating.RelationDecomposition.ForwardOrientation.predecessor_wellFounded
    (erasedSelectedSwitchedEdges U S K)
    h.noDirectedCycle h.noReverseDirectedRay

/-- Exact rooted-reachability reduction for `BB`.  It is enough to classify
the no-incoming root of any switched component which reaches `BB` as an
original source. -/
theorem rooted_reachability_of_root_classification
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    (h : Compatible U S K)
    (hclassify : ∀ a b : V,
      ¬ HasIncoming (erasedSelectedSwitchedEdges U S K) a →
      b ∈ GroundingCut.BB L S.cut →
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K) a b →
      a ∈ Gamma.source) :
    ∀ b ∈ GroundingCut.BB L S.cut,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K) a b ∧
        ¬ HasIncoming (erasedSelectedSwitchedEdges U S K) a := by
  apply GroundingWellFoundedRoots.rooted_reachability_of_noIncoming_classification
    (erasedSelectedSwitchedEdges U S K)
    (predecessor_wellFounded h) Gamma.source
      (GroundingCut.BB L S.cut)
  exact hclassify

/-- A set of vertices with no outgoing relation edge is automatically a
directed-reachability antichain. -/
theorem reachabilityAntichain_of_noOutgoing
    {E : Set (V × V)} {B : Set V}
    (h : ∀ b ∈ B, ¬ HasOutgoing E b) :
    GroundingRootedReachabilityWarp.IsReachabilityAntichain E B := by
  intro b hb c hc hbc
  rcases hbc.cases_head with hcb | ⟨x, hbx, _hxc⟩
  · exact hcb
  · exact False.elim (h b hb ⟨x, hbx⟩)

end GroundingBBRootReduction
end Erdos599
