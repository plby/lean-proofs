/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingTraversal

/-!
# Finite continuation in the coloured residual port relation

For reverse reducing switches the forward family is not used as a second
exclusive matching.  Instead the reference matching is completed by
identity edges, and a sending-to-receiving step may use either a forward
family edge or the complementary identity.  This retains same-colour
backward continuation along the reference warp.
-/

namespace Erdos599
namespace ColouredResidualPortContinuation

open Set DirectedPath Alternating
open TwoWarpMatchingTraversal

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The neutral web has the same ambient graph and empty boundary sets. -/
def neutralWeb (Gamma : DWeb V) : DWeb V where
  graph := Gamma.graph
  source := ∅
  target := ∅

/-- The completed reference matching: reference edges together with
diagonals outside the reference edge carrier. -/
def completedReferenceMatching (Z : Set Gamma.DPath) (x y : V) : Prop :=
  matchingEdge (Gamma := neutralWeb Gamma) Z x y

/-- The coloured residual port relation. -/
def ResidualStep (Z Y : Set Gamma.DPath) : Port V → Port V → Prop
  | .inl x, .inr y =>
      ((x, y) ∈ familyEdges Y ∨ x = y) ∧
        ¬ completedReferenceMatching Z x y
  | .inr y, .inl x => completedReferenceMatching Z x y
  | _, _ => False

private theorem Walk.not_self_mem_edgeSet_of_isPath
    {D : Digraph V} {a b x : V} (p : Walk D a b) (hp : p.IsPath) :
    (x, x) ∉ p.edgeSet := by
  induction p with
  | nil => simp [Walk.edgeSet]
  | @cons a c b hac p ih =>
      intro hxx
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at hxx
      rcases hxx with hhead | htail
      · have hax : x = a := congrArg Prod.fst hhead
        have hcx : x = c := congrArg Prod.snd hhead
        have hacEq : a = c := hax.symm.trans hcx
        subst c
        subst x
        exact (List.nodup_cons.mp hp).1 p.start_mem_support
      · exact ih hp.tail htail

theorem not_self_mem_familyEdges (W : Set Gamma.DPath) (x : V) :
    (x, x) ∉ familyEdges W := by
  intro hxx
  simp only [familyEdges, Set.mem_iUnion] at hxx
  rcases hxx with ⟨p, _hpW, hxp⟩
  rcases p with p | r
  · exact Walk.not_self_mem_edgeSet_of_isPath p.walk p.isPath hxp
  · rcases hxp with ⟨n, heq⟩
    have hsame : r n = r (n + 1) := by
      exact (congrArg Prod.fst heq).symm.trans (congrArg Prod.snd heq)
    exact (Nat.ne_of_lt (Nat.lt_succ_self n)) (r.injective hsame)

theorem not_completedReferenceMatching_self_of_mem_edgeCarrier
    {Z : Set Gamma.DPath} {x : V} (hx : x ∈ edgeCarrier Z) :
    ¬ completedReferenceMatching Z x x := by
  intro h
  rcases h with h | h
  · exact not_self_mem_familyEdges Z x h
  · exact h.2.1 hx

theorem residualStep_diagonal
    {Z Y : Set Gamma.DPath} {x : V} (hx : x ∈ edgeCarrier Z) :
    ResidualStep Z Y (.inl x) (.inr x) :=
  ⟨Or.inr rfl, not_completedReferenceMatching_self_of_mem_edgeCarrier hx⟩

theorem residualStep_reference_backward
    {Z Y : Set Gamma.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges Z) :
    ResidualStep Z Y (.inr y) (.inl x) :=
  matchingEdge_actual hxy

theorem residualStep_forward_of_not_reference
    {Z Y : Set Gamma.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges Y)
    (hnot : ¬ completedReferenceMatching Z x y) :
    ResidualStep Z Y (.inl x) (.inr y) :=
  ⟨Or.inl hxy, hnot⟩

private theorem Walk.sender_finish_reaches_start
    {Z Y : Set Gamma.DPath} {a b : V} (w : Walk Gamma.graph a b)
    (hE : w.edgeSet ⊆ familyEdges Z) :
    Relation.ReflTransGen (ResidualStep Z Y) (.inl b) (.inl a) := by
  induction w with
  | nil => exact .refl
  | @cons a c b hac w ih =>
      have hhead : (a, c) ∈ familyEdges Z := by
        apply hE
        simp [Walk.edgeSet]
      have htail : w.edgeSet ⊆ familyEdges Z := by
        intro e he
        apply hE
        exact Set.mem_union_right _ he
      have hc : c ∈ edgeCarrier Z := Or.inr ⟨a, hhead⟩
      exact (ih htail).trans
        ((Relation.ReflTransGen.single (residualStep_diagonal hc)).trans
          (Relation.ReflTransGen.single
            (residualStep_reference_backward hhead)))

private theorem Walk.receiver_finish_reaches_start
    {Z Y : Set Gamma.DPath} {a b : V} (w : Walk Gamma.graph a b)
    (hE : w.edgeSet ⊆ familyEdges Z) (hpos : 0 < w.length) :
    Relation.ReflTransGen (ResidualStep Z Y) (.inr b) (.inl a) := by
  induction w with
  | nil => simp at hpos
  | @cons a c b hac w ih =>
      have hhead : (a, c) ∈ familyEdges Z := by
        apply hE
        simp [Walk.edgeSet]
      cases w with
      | nil =>
          exact Relation.ReflTransGen.single
            (residualStep_reference_backward hhead)
      | @cons c d b hcd w =>
          have htail : (Walk.cons hcd w).edgeSet ⊆ familyEdges Z := by
            intro e he
            apply hE
            exact Set.mem_union_right _ he
          have htailPos : 0 < (Walk.cons hcd w).length := by simp
          have hc : c ∈ edgeCarrier Z := Or.inr ⟨a, hhead⟩
          exact (ih htail htailPos).trans
            ((Relation.ReflTransGen.single (residualStep_diagonal hc)).trans
              (Relation.ReflTransGen.single
                (residualStep_reference_backward hhead)))

private theorem Walk.endpoints_eq_of_zero_length
    {D : Digraph V} {a b : V} (w : Walk D a b)
    (hzero : w.length = 0) : a = b := by
  cases w with
  | nil => rfl
  | cons h w => simp at hzero

/-- Every finite reference path can be traversed backwards from its terminal
sending port to its initial sending port. -/
theorem finiteReferencePath_sender_finish_reaches_start_of_edges
    {Z Y : Set Gamma.DPath} (p : FinitePath Gamma.graph)
    (hpZ : p.edgeSet ⊆ familyEdges Z) :
    Relation.ReflTransGen (ResidualStep Z Y)
      (.inl p.finish) (.inl p.start) :=
  Walk.sender_finish_reaches_start p.walk hpZ

/-- A nontrivial reference fragment can start at its terminal receiving
port. Whole-owner membership is not needed. -/
theorem finiteReferencePath_receiver_finish_reaches_start_of_edges
    {Z Y : Set Gamma.DPath} (p : FinitePath Gamma.graph)
    (hpZ : p.edgeSet ⊆ familyEdges Z) (hne : p.start ≠ p.finish) :
    Relation.ReflTransGen (ResidualStep Z Y)
      (.inr p.finish) (.inl p.start) := by
  apply Walk.receiver_finish_reaches_start p.walk hpZ
  by_contra hnot
  have hzero : p.walk.length = 0 := Nat.eq_zero_of_not_pos hnot
  exact hne (Walk.endpoints_eq_of_zero_length p.walk hzero)

/-- Whole-member specialization of backward continuation. -/
theorem finiteReferencePath_sender_finish_reaches_start
    {Z Y : Set Gamma.DPath} (p : FinitePath Gamma.graph)
    (hpZ : (Sum.inl p : Gamma.DPath) ∈ Z) :
    Relation.ReflTransGen (ResidualStep Z Y)
      (.inl p.finish) (.inl p.start) := by
  apply Walk.sender_finish_reaches_start p.walk
  intro e he
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨.inl p, hpZ, he⟩

/-- A nontrivial finite reference path can be traversed backwards directly
from its terminal receiving port. -/
theorem finiteReferencePath_receiver_finish_reaches_start
    {Z Y : Set Gamma.DPath} (p : FinitePath Gamma.graph)
    (hpZ : (Sum.inl p : Gamma.DPath) ∈ Z)
    (hne : p.start ≠ p.finish) :
    Relation.ReflTransGen (ResidualStep Z Y)
      (.inr p.finish) (.inl p.start) := by
  apply Walk.receiver_finish_reaches_start p.walk
  · intro e he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨.inl p, hpZ, he⟩
  · by_contra hnot
    have hzero : p.walk.length = 0 := Nat.eq_zero_of_not_pos hnot
    exact hne (Walk.endpoints_eq_of_zero_length p.walk hzero)

/-- A forward-family edge entering the terminal of a nontrivial finite
reference path reaches the reference initial.  If the forward edge is also
a reference edge, its last reference occurrence is cancelled and the
remaining reference prefix is traversed instead. -/
theorem forwardEdge_to_finiteReferenceFinish_reaches_start_of_edges
    {Z Y : Set Gamma.DPath} (hZ : Gamma.IsWarp Z)
    (p : FinitePath Gamma.graph)
    (hpZ : p.edgeSet ⊆ familyEdges Z)
    (hne : p.start ≠ p.finish) {y : V}
    (hy : (y, p.finish) ∈ familyEdges Y) :
    Relation.ReflTransGen (ResidualStep Z Y) (.inl y) (.inl p.start) := by
  by_cases hmatch : completedReferenceMatching Z y p.finish
  · rcases hmatch with hreference | hidentity
    · obtain ⟨z, hz⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start p
        p.finish_mem_support hne.symm
      have hyz : y = z := (IsWarp.familyEdges_biUnique hZ).1 hreference (hpZ hz)
      have hyp : (y, p.finish) ∈ p.edgeSet := hyz ▸ hz
      have hypSupport : y ∈ p.support :=
        (p.edgeSet_subset_support_prod hyp).1
      let hmeet : p.walk.Meets {y} :=
        ⟨y, hypSupport, Set.mem_singleton y⟩
      let qprefix : FinitePath Gamma.graph := p.firstHit {y} hmeet
      have hprefixEdges : qprefix.edgeSet ⊆ familyEdges Z := by
        intro e he
        exact hpZ (p.firstHit_edgeSet_subset {y} hmeet he)
      have hreach :=
        Walk.sender_finish_reaches_start (Y := Y) qprefix.walk hprefixEdges
      have hprefixStart : qprefix.start = p.start := rfl
      have hprefixFinish : qprefix.finish = y := by
        have hm := p.firstHit_finish_mem {y} hmeet
        simpa only [Set.mem_singleton_iff] using hm
      rw [hprefixStart, hprefixFinish] at hreach
      exact hreach
    · have hyEq : y = p.finish := hidentity.1
      exact False.elim
        (not_self_mem_familyEdges Y p.finish (hyEq ▸ hy))
  · exact (Relation.ReflTransGen.single
        (residualStep_forward_of_not_reference hy hmatch)).trans
      (finiteReferencePath_receiver_finish_reaches_start_of_edges p hpZ hne)

/-- Whole-member specialization of the shared-edge-aware continuation. -/
theorem forwardEdge_to_finiteReferenceFinish_reaches_start
    {Z Y : Set Gamma.DPath} (hZ : Gamma.IsWarp Z)
    (p : FinitePath Gamma.graph)
    (hpZ : (Sum.inl p : Gamma.DPath) ∈ Z)
    (hne : p.start ≠ p.finish) {y : V}
    (hy : (y, p.finish) ∈ familyEdges Y) :
    Relation.ReflTransGen (ResidualStep Z Y) (.inl y) (.inl p.start) := by
  apply forwardEdge_to_finiteReferenceFinish_reaches_start_of_edges hZ p
    (fun e he ↦ ?_) hne hy
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨.inl p, hpZ, he⟩

#print axioms finiteReferencePath_sender_finish_reaches_start
#print axioms finiteReferencePath_receiver_finish_reaches_start
#print axioms forwardEdge_to_finiteReferenceFinish_reaches_start
#print axioms forwardEdge_to_finiteReferenceFinish_reaches_start_of_edges

end ColouredResidualPortContinuation
end Erdos599
