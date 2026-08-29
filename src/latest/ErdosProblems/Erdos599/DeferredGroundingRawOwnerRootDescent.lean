/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawContactOrder
import ErdosProblems.Erdos599.GroundingPathPrefix

/-!
# Finite root-defect reduction on a grounded backward owner

A finite prefix of a grounded owner starts rooted. Its first rootedness
crossing is a stopped edge, a cut edge, or a backward deletion belonging
to the unique request changing that owner. No other request can interfere.
The alternatives and the owner's groundedness hypothesis remain explicit.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath Alternating
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

private theorem exists_predicate_exit_of_reflTransGen
    {V : Type u} {R : V → V → Prop} {a b : V}
    (h : Relation.ReflTransGen R a b) {P : V → Prop} (ha : P a) (hb : ¬ P b) :
    ∃ x y, R x y ∧ P x ∧ ¬ P y := by
  classical
  induction h with
  | refl => exact (hb ha).elim
  | @tail x y hax hxy ih =>
      by_cases hx : P x
      · exact ⟨x, y, hxy, hx, hb⟩
      · exact ih hx

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "T" => reservedStrongSelectedSourceFirstBB (L := L) (hL := hL) (S := S)
local notation "Root" => reservedRawSourceRooted (L := L) (hL := hL) (S := S)

/-- Every failed root on a grounded backward-changed owner has a finite
prefix crossing caused only by a stop, the cut, or that same request. -/
theorem reservedRawBackwardOwner_unrooted_prefix_crossing
    (r : Request J S.cut) {Y : Gamma.DPath} (hY : Y ∈ (J).ladder.paths)
    (hground : Y.initial ∈ Gamma.source)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet)
    {x : V} (hxY : x ∈ Y.support) (hx : ¬ Root x) :
    ∃ q : FinitePath Gamma.graph,
      q.start = Y.initial ∧ q.finish = x ∧ q.support ⊆ Y.support ∧
      q.edgeSet ⊆ Y.edgeSet ∧
      ∃ a b, (a, b) ∈ q.edgeSet ∧ Root a ∧ ¬ Root b ∧
        (a ∈ T ∨ (a, b) ∈ GroundingCut.CE J S.cut ∨
          (a, b) ∈ reservedRawRequestBackwardEdges r) := by
  classical
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix Y hxY
  have hstart : Root q.start := by
    rw [hqStart]
    exact reservedRawSourceRooted_of_source hground
  have hfinish : ¬ Root q.finish := by simpa only [hqFinish] using hx
  obtain ⟨a, b, hab, haRoot, hbNot⟩ := exists_predicate_exit_of_reflTransGen
    (Walk.reflTransGen_edgeSet q.walk) hstart hfinish
  refine ⟨q, hqStart, hqFinish, hqSupport, hqEdges, a, b, hab, haRoot, hbNot, ?_⟩
  by_cases haT : a ∈ T
  · exact Or.inl haT
  by_cases habCut : (a, b) ∈ GroundingCut.CE J S.cut
  · exact Or.inr (Or.inl habCut)
  by_cases habBack : (a, b) ∈ reservedRawRequestBackwardEdges r
  · exact Or.inr (Or.inr habBack)
  have habRetained := (reservedRawRetained_on_backwardOwner_iff
    r hY he heY (hqEdges hab)).2 ⟨habCut, habBack⟩
  exact (hbNot (reservedRawSourceRooted_step haRoot ⟨Or.inl habRetained, haT⟩)).elim

#print axioms reservedRawBackwardOwner_unrooted_prefix_crossing

end Erdos599.DWeb.KappaLadder.Deferred
