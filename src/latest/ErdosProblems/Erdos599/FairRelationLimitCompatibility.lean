/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySchedulerConstruction
import ErdosProblems.Erdos599.IntermediateRelationLimitCompatibility

/-!
# Fair relation limits from the honest well-foundedness boundary

The source's imaginary-edge replacement may insert a new real predecessor
at an old non-root vertex.  Consequently the final fair scheduler must not
hide absence of reverse rays behind `NoNewRealPredecessors`.

This module gives the final all-real analogue of
`IntermediateRelationLimitCompatibility`.  A successful enumeration is
compiled from the genuinely necessary relation data: a `RelationLimitCore`
and the raw boundary of its real-edge union.  Source coverage is automatic
from the stage blueprint conditions; it does not require predecessor
preservation.  If an incoming real edge entered a source vertex, the stage
containing that edge would contradict its own source-cover clause.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {T Z persistent B : Set V}

namespace RealExtensionChain

variable {I : Type u} [LinearOrder I] [Nonempty I]

/-- A source vertex in the union carrier is a root of the all-real union.
The proof uses the stage which contains a hypothetical incoming real edge,
not a no-new-predecessor invariant. -/
theorem source_mem_realRelationRoots
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    {a : V} (ha : a ∈ Gamma.source) (haLimit : a ∈ C.realVertexLimit) :
    a ∈ C.realVertexLimit ∧
      ¬ ∃ y, (y, a) ∈ C.realEdgeLimit := by
  refine ⟨haLimit, ?_⟩
  rintro ⟨y, hya⟩
  obtain ⟨i, hyai⟩ := Set.mem_iUnion.1 hya
  have haStage : a ∈ (C.stage i).vertexSet := by
    exact (Alternating.familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hyai.1).2
  rcases (C.isBlueprint i).covers_source ha with hainitial | hretained
  · exact no_incoming_edge_of_mem_initialSet (C.stage i) hainitial
      ⟨y, hyai.1⟩
  · rcases hretained with ⟨p, ⟨hpT, hpnoti⟩, hpinitial⟩
    exact hpnoti
      ⟨hpT.1, ⟨a, hpinitial ▸ p.initial_mem_support,
        by simpa only [realPart_vertices] using haStage⟩⟩

/-- Source coverage of the all-real relation limit is a consequence of the
stage source-cover clauses alone. -/
theorem compatibleRelationLimit_covers_source
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (hYwarp : Gamma.IsWarp Y) :
    Gamma.source ⊆
      {x | x ∈ C.realVertexLimit ∧
        ¬ ∃ y, (y, x) ∈ C.realEdgeLimit} ∪
        Gamma.initialSet
          (referencePathsMeeting Y T \
            referencePathsMeeting Y C.realVertexLimit) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  intro a ha
  rcases (C.isBlueprint i₀).covers_source ha with hainitial | hretained
  · apply Or.inl
    apply C.source_mem_realRelationRoots ha
    exact C.stage_vertices_subset_realVertexLimit i₀
      (by
        rcases hainitial with ⟨p, hp, rfl⟩
        exact ⟨p, hp, p.initial_mem_support⟩)
  · rcases hretained with ⟨p, ⟨hpT, hpnoti₀⟩, hpinitial⟩
    by_cases hpmeet : (p.support ∩ C.realVertexLimit).Nonempty
    · obtain ⟨x, hxp, hxlimit⟩ := hpmeet
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 hxlimit
      rcases (C.isBlueprint j).covers_source ha with hjinitial | hjretained
      · apply Or.inl
        apply C.source_mem_realRelationRoots ha
        exact C.stage_vertices_subset_realVertexLimit j
          (by
            rcases hjinitial with ⟨q, hq, rfl⟩
            exact ⟨q, hq, q.initial_mem_support⟩)
      · rcases hjretained with ⟨q, ⟨hqT, hqnotj⟩, hqinitial⟩
        have hqp : q = p := by
          by_contra hne
          have hd := hYwarp hqT.1 hpT.1 hne
          exact Set.disjoint_left.1 hd
            (hqinitial ▸ q.initial_mem_support)
            (hpinitial ▸ p.initial_mem_support)
        subst q
        exact False.elim <| hqnotj
          ⟨hpT.1, ⟨x, hxp,
            by simpa only [realPart_vertices] using hxj⟩⟩
    · exact Or.inr ⟨p, ⟨hpT, fun hp ↦ hpmeet hp.2⟩, hpinitial⟩

end RealExtensionChain

namespace TerminalResolutionState
namespace ResolutionChain

variable {I : Type u} [LinearOrder I] [Nonempty I]
variable {compiler : Stable934Compiler
  (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B}
variable {hpersistent : persistent ⊆ T}

/-- The final relation-limit scheduler state for an arbitrary honest
`RelationLimitCore`. -/
noncomputable def compatibleLimitState
    (C : ResolutionChain I compiler hpersistent)
    (H : C.toRealExtensionChain.RelationLimitCore)
    (D : C.toRealExtensionChain.StableRelationLimitData H) :
    TerminalResolutionState Gamma Y kappa T Z persistent B where
  blueprint := C.toRealExtensionChain.relationLimit H
  isBlueprint := D.isBlueprint
  stable := D.stable
  linked := ⋃ i, (C.stage i).linked
  links := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact realLinksTo_mono
      (C.toRealExtensionChain.realPart_extends_relationLimit H i)
      ((C.stage i).links x hxi)

/-- A terminal of an arbitrary honest all-real relation limit was already a
real terminal at some stage. -/
theorem exists_stage_realTerminal_of_compatibleRelationLimit_terminal
    (C : ResolutionChain I compiler hpersistent)
    (H : C.toRealExtensionChain.RelationLimitCore) {x : V}
    (hx : x ∈
      (C.toRealExtensionChain.relationLimit H).realPart.terminals) :
    ∃ i, x ∈ (C.stage i).blueprint.realPart.terminals := by
  rcases hx with ⟨hxv, hxout⟩
  rw [realPart_vertices,
    C.toRealExtensionChain.relationLimit_vertexSet H] at hxv
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxv
  change x ∈ (C.stage i).blueprint.realPart.vertices at hxi
  refine ⟨i, hxi, ?_⟩
  rintro ⟨y, hxy⟩
  apply hxout
  exact ⟨y, C.toRealExtensionChain.realPart_extends_relationLimit H i |>.2
    hxy⟩

/-- Fairness supplies the sink boundary and exact (9.32) accounting once an
honest relation core and raw blueprint boundary have been established. -/
noncomputable def FairResolutionLimit.ofSuccessfulEnumeration_of_core
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (H : C.toRealExtensionChain.RelationLimitCore)
    (D : C.toRealExtensionChain.RelationLimitBoundaryData)
    (E : SuccessfulResolutionEnumeration C seed) :
    FairResolutionLimit compiler hpersistent seed := by
  let L : C.toRealExtensionChain.StableRelationLimitData H :=
    C.toRealExtensionChain
      |>.stableRelationLimitData_of_boundary_eventuallyCompleted
        H D E.eventuallyCompleted
  exact {
    index := I
    stage := C.stage
    scheduled := E.scheduled
    seed_absorbed := E.seed_absorbed
    scheduled_linked := E.scheduled_linked
    limit := compatibleLimitState C H L
    absorbed := fun i ↦
      C.toRealExtensionChain.realPart_extends_relationLimit H i
    fair := by
      intro x hx hxB
      obtain ⟨i, hxi⟩ :=
        C.exists_stage_realTerminal_of_compatibleRelationLimit_terminal H hx
      exact E.covers_stage_realTerminals i x hxi
    real_limit := C.toRealExtensionChain.relationLimit_edge_real H }

/-- Normalization and successful enumeration discharge every final boundary
except the genuine reverse-ray condition stored in `H`. -/
noncomputable def FairResolutionLimit.ofSuccessfulEnumeration_of_normalizedCore
    {C : ResolutionChain I compiler hpersistent}
    {seed : TerminalResolutionState Gamma Y kappa T Z persistent B}
    (H : C.toRealExtensionChain.RelationLimitCore)
    (hYwarp : Gamma.IsWarp Y) (hkappa : aleph0 ≤ kappa)
    (hindex : #I ≤ kappa)
    (hGamma : Gamma.IsNormalized) (hBtarget : B ⊆ Gamma.target)
    (hterminalB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (E : SuccessfulResolutionEnumeration C seed) :
    FairResolutionLimit compiler hpersistent seed := by
  apply FairResolutionLimit.ofSuccessfulEnumeration_of_core H ?_ E
  exact {
    covers_source :=
      C.toRealExtensionChain.compatibleRelationLimit_covers_source hYwarp
    card_vertices :=
      C.toRealExtensionChain.mk_realVertexLimit_le hkappa hindex
    every_relation_ray_strong :=
      C.toRealExtensionChain.realEdgeLimit_every_ray_strong
        hGamma hBtarget
    terminal_boundary :=
      C.toRealExtensionChain
        |>.relationLimit_terminal_boundary_of_eventuallyCompleted
          E.eventuallyCompleted hterminalB
    stable_boundary :=
      C.toRealExtensionChain
        |>.relationLimit_stable_boundary_of_eventuallyCompleted
          E.eventuallyCompleted hstableB }

end ResolutionChain
end TerminalResolutionState
end LinkageBlueprint
end Blueprint
end Erdos599
