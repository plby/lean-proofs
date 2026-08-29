/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualActiveSelection

/-! # Owner provenance inside one equal-stage collision carrier -/

noncomputable section

open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingEqualActiveSelection GroundingSimultaneousDecode
open PopularAuxiliary.Input

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- The union of the complete collision carriers of a family of auxiliary
routes.  This lightweight definition is shared by both candidate boundary
constructions. -/
def collisionHull
    (J : PopularAuxiliary.Input Gamma I)
    (P : Set (FinitePath J.lambda.graph)) : Set J.LV :=
  ⋃ p ∈ P, collisionCarrier J p

@[simp] theorem mem_collisionHull
    {J : PopularAuxiliary.Input Gamma I}
    {P : Set (FinitePath J.lambda.graph)} {x : J.LV} :
    x ∈ collisionHull J P ↔
      ∃ p ∈ P, x ∈ collisionCarrier J p := by
  simp only [collisionHull, Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨p, hp, hx⟩

def OldCollisionProvenance
    (J : PopularAuxiliary.Input Gamma I)
    (r : FinitePath J.lambda.graph) (b : V) : Prop :=
  (((LambdaVertex.old b : J.LV) ∈ r.support) ∧
      b ∈ J.decodedVertexCarrier r) ∨
    ∃ Y ∈ exposedLadderPaths J r, b ∈ Y.support

def EdgeCollisionProvenance
    (J : PopularAuxiliary.Input Gamma I)
    (r : FinitePath J.lambda.graph) (u v : V) : Prop :=
  (((LambdaVertex.edge u v : J.LV) ∈ r.support) ∧
      u ∈ J.decodedVertexCarrier r ∧
      v ∈ J.decodedVertexCarrier r) ∨
    ∃ Y ∈ exposedLadderPaths J r, (u, v) ∈ Y.edgeSet

theorem old_mem_ladderTrace_iff
    (J : PopularAuxiliary.Input Gamma I) (Y : Gamma.DPath) (b : V) :
    (LambdaVertex.old b : J.LV) ∈ PopularSwitching.ladderTrace J Y ↔
      b ∈ Y.support := by
  constructor
  · rintro (⟨x, hxY, hxb⟩ | ⟨e, _heY, heq⟩)
    · exact (LambdaVertex.old.inj hxb).symm ▸ hxY
    · cases heq
  · intro hbY
    exact Or.inl ⟨b, hbY, rfl⟩

theorem edge_mem_ladderTrace_iff
    (J : PopularAuxiliary.Input Gamma I) (Y : Gamma.DPath) (u v : V) :
    (LambdaVertex.edge u v : J.LV) ∈ PopularSwitching.ladderTrace J Y ↔
      (u, v) ∈ Y.edgeSet := by
  constructor
  · rintro (⟨x, _hxY, heq⟩ | ⟨e, heY, heq⟩)
    · cases heq
    · have hu : e.1 = u := (LambdaVertex.edge.inj heq).1
      have hv : e.2 = v := (LambdaVertex.edge.inj heq).2
      have he : e = (u, v) := Prod.ext hu hv
      simpa only [he] using heY
  · intro huvY
    exact Or.inr ⟨(u, v), huvY, rfl⟩

theorem old_mem_collisionCarrier_iff
    (J : PopularAuxiliary.Input Gamma I)
    (r : FinitePath J.lambda.graph) (b : V) :
    (LambdaVertex.old b : J.LV) ∈ collisionCarrier J r ↔
      OldCollisionProvenance J r b := by
  constructor
  · intro hb
    rcases hb with (hbSupport | hbTrace) | hbProxy
    · left
      refine ⟨hbSupport, ?_⟩
      apply J.gadgetCarrier_subset_decodedVertexCarrier r hbSupport
      simp
    · right
      obtain ⟨Y, hYr, hbY⟩ :=
        (mem_metLadderTrace_iff J r (.old b)).1 hbTrace
      exact ⟨Y, hYr, (old_mem_ladderTrace_iff J Y b).1 hbY⟩
    · obtain ⟨i, heq, _hi⟩ := hbProxy
      cases heq
  · rintro (⟨hbSupport, _hbDecoded⟩ | ⟨Y, hYr, hbY⟩)
    · exact Or.inl (Or.inl hbSupport)
    · exact Or.inl (Or.inr ((mem_metLadderTrace_iff J r (.old b)).2
        ⟨Y, hYr, (old_mem_ladderTrace_iff J Y b).2 hbY⟩))

theorem edge_mem_collisionCarrier_iff
    (J : PopularAuxiliary.Input Gamma I)
    (r : FinitePath J.lambda.graph) (u v : V) :
    (LambdaVertex.edge u v : J.LV) ∈ collisionCarrier J r ↔
      EdgeCollisionProvenance J r u v := by
  constructor
  · intro he
    rcases he with (heSupport | heTrace) | heProxy
    · left
      refine ⟨heSupport, ?_, ?_⟩
      · apply J.gadgetCarrier_subset_decodedVertexCarrier r heSupport
        simp
      · apply J.gadgetCarrier_subset_decodedVertexCarrier r heSupport
        simp
    · right
      obtain ⟨Y, hYr, heY⟩ :=
        (mem_metLadderTrace_iff J r (.edge u v)).1 heTrace
      exact ⟨Y, hYr, (edge_mem_ladderTrace_iff J Y u v).1 heY⟩
    · obtain ⟨i, heq, _hi⟩ := heProxy
      cases heq
  · rintro (⟨heSupport, _hu, _hv⟩ | ⟨Y, hYr, heY⟩)
    · exact Or.inl (Or.inl heSupport)
    · exact Or.inl (Or.inr ((mem_metLadderTrace_iff J r (.edge u v)).2
        ⟨Y, hYr, (edge_mem_ladderTrace_iff J Y u v).2 heY⟩))

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.old_mem_collisionCarrier_iff
#print axioms Erdos599.DWeb.KappaLadder.edge_mem_collisionCarrier_iff
