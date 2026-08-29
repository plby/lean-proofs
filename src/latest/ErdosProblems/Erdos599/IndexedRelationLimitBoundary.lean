/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IndexedRelationLimit
import ErdosProblems.Erdos599.FiniteFrontierCompactness

/-!
# Source and terminal fields at moving-slice relation limits

These are concrete consequences of real-extension accounting and finite-path
compactness.  They do not assume a limit blueprint certificate.  The actual
frontier identity and its monotone discarded sets remain explicit geometry.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace IndexedRealExtensionChain

universe u v

variable {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {B persistent : Set V}

/-- A sink of the proper relation is a target vertex or an old terminal
at every stage whose carrier contains it. -/
theorem eventualTerminal_mem_target_or_stage_terminal
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    {x : V} (hx : x ∈ C.eventualRelationBlueprint.terminalSet)
    (i : I) (hxi : x ∈ (C.stage i).vertexSet) :
    x ∈ B ∨ x ∈ (C.stage i).terminalSet := by
  rcases (C.realExtends_eventualRelationBlueprint i).2 hxi with
    (hcommon | hedge) | hcompleted
  · exact Or.inr hcommon.2
  · obtain ⟨y, _, hxy⟩ := hedge
    exact False.elim <|
      (mem_familyGraph_terminals_of_mem_terminalSet hx).2 ⟨y, hxy⟩
  · by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · apply False.elim
      apply not_mem_realTerminals_of_realLinksTo hxB
        (realLinksTo_of_mem_completedRealVertices hcompleted)
      have hsink := mem_familyGraph_terminals_of_mem_terminalSet hx
      refine ⟨hsink.1, ?_⟩
      rintro ⟨y, hxy⟩
      exact hsink.2 ⟨y, hxy.1⟩

/-- Stability at each moving slice strengthens the proper-limit terminal
bound to popularity or persistence, with target geometry needed only on
the actual carrier. -/
theorem eventualTerminal_popular_or_persistent
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (slice closed : I → Set V)
    (hstage : ∀ i, (C.stage i).IsLinkageBlueprint
      (slice i) (closed i) persistent)
    (hstable : ∀ i, (C.stage i).Stable (slice i) persistent)
    (hB : B ∩ C.realVertexLimit ⊆ persistent) :
    C.eventualRelationBlueprint.terminalSet ⊆
      {x | IsPopular Gamma Y persistent kappa x} ∪ persistent := by
  intro x hx
  have hxlimit : x ∈ C.realVertexLimit := by
    rw [← C.eventualRelationBlueprint_vertexSet]
    exact (mem_familyGraph_terminals_of_mem_terminalSet hx).1
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxlimit
  rcases C.eventualTerminal_mem_target_or_stage_terminal hx i hxi with
    hxB | hxterm
  · exact Or.inr (hB ⟨hxB, hxlimit⟩)
  · rcases (hstage i).terminals_popular hxterm with hxpop | hxslice
    · exact Or.inl hxpop
    · exact Or.inr (hstable i ⟨hxterm, hxslice⟩)

/-- The final real relation has only target terminals once every appearing
real terminal is eventually completed. -/
theorem realRelationBlueprint_terminals_subset_target
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (hcompleted : ∀ i x, x ∈ (C.stage i).realPart.terminals →
      ∃ j, x ∈ (C.stage j).completedRealVertices B) :
    C.realRelationBlueprint.terminalSet ⊆ B := by
  intro x hx
  have hsink := mem_familyGraph_terminals_of_mem_terminalSet hx
  have hxlimit : x ∈ C.realVertexLimit := by
    rw [← C.realRelationBlueprint_vertexSet]
    exact hsink.1
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxlimit
  have hxterm : x ∈ (C.stage i).realPart.terminals := by
    refine ⟨hxi, ?_⟩
    rintro ⟨y, hxy⟩
    apply hsink.2
    refine ⟨y, ?_⟩
    change (x, y) ∈ C.realRelationBlueprint.edgeSet
    rw [C.realRelationBlueprint_edgeSet]
    exact C.stage_edges_subset_realEdgeLimit i hxy
  obtain ⟨j, hxj⟩ := hcompleted i x hxterm
  by_contra hxB
  apply not_mem_realTerminals_of_realLinksTo hxB
    (realLinksTo_of_mem_completedRealVertices
      (completedRealVertices_mono
        (C.realPart_extends_realRelationBlueprint j) hxj))
  refine ⟨hsink.1, ?_⟩
  rintro ⟨y, hxy⟩
  exact hsink.2 ⟨y, hxy.1⟩

/-- Source coverage at the witnessing stage forbids incoming eventual
edges at source vertices, independently of the moving slice. -/
theorem source_mem_eventualRelationRoots
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (slice : I → Set V)
    (hcover : ∀ i, Gamma.source ⊆ (C.stage i).initialSet ∪
      (C.stage i).retainedReferenceInitials (slice i))
    {a : V} (ha : a ∈ Gamma.source) (haLimit : a ∈ C.realVertexLimit) :
    a ∈ C.realVertexLimit ∧ ¬ ∃ y, (y, a) ∈ C.eventualEdgeLimit := by
  refine ⟨haLimit, ?_⟩
  rintro ⟨y, hya⟩
  obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 hya
  have hyai : (y, a) ∈ (C.stage i).edgeSet := hi i le_rfl
  have haStage : a ∈ (C.stage i).vertexSet :=
    (Alternating.familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hyai).2
  rcases hcover i ha with hainitial | hretained
  · exact RealExtensionChain.no_incoming_edge_of_mem_initialSet (C.stage i) hainitial
      ⟨y, hyai⟩
  · rcases hretained with ⟨p, ⟨hpT, hpnoti⟩, hpinitial⟩
    exact hpnoti ⟨hpT.1,
      ⟨a, hpinitial ▸ p.initial_mem_support, haStage⟩⟩

/-- Finite reference paths preserve source coverage at a moving frontier.
The reference family may be infinite; only each individual support is
finite, and the displayed frontier identity is a separate ladder fact. -/
theorem eventualRelationBlueprint_covers_source
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (slice R D : I → Set V) (T : Set V)
    (hcover : ∀ i, Gamma.source ⊆ (C.stage i).initialSet ∪
      (C.stage i).retainedReferenceInitials (slice i))
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : ∀ p ∈ Y, p.support.Finite)
    (hslice : ∀ i, slice i = R i \ D i)
    (hD : Monotone D) (hT : T = (⋃ i, R i) \ ⋃ i, D i) :
    Gamma.source ⊆ C.eventualRelationBlueprint.initialSet ∪
      C.eventualRelationBlueprint.retainedReferenceInitials T := by
  classical
  intro a ha
  by_cases halimit : a ∈ C.realVertexLimit
  · apply Or.inl
    rw [eventualRelationBlueprint, orientationBlueprint_initialSet_eq_no_incoming,
      C.eventualRelationOrientation_spec.1, C.eventualRelationOrientation_spec.2]
    exact C.source_mem_eventualRelationRoots slice hcover ha halimit
  · have hretained : ∀ i, a ∈ (C.stage i).retainedReferenceInitials (slice i) := by
      intro i
      rcases hcover i ha with hainitial | hr
      · rcases hainitial with ⟨p, hp, rfl⟩
        exact False.elim <| halimit <|
          C.stage_vertices_subset_realVertexLimit i ⟨p, hp, p.initial_mem_support⟩
      · exact hr
    let i₀ : I := Classical.choice inferInstance
    obtain ⟨p, ⟨hpT, hpnot⟩, hpinitial⟩ := hretained i₀
    have hmeet : ∀ i, (p.support ∩ slice i).Nonempty := by
      intro i
      obtain ⟨q, ⟨hqT, _⟩, hqinitial⟩ := hretained i
      have hqp : q = p := by
        by_contra hne
        exact Set.disjoint_left.1 (hYwarp hqT.1 hpT.1 hne)
          (hqinitial ▸ q.initial_mem_support)
          (hpinitial ▸ p.initial_mem_support)
      exact hqp ▸ hqT.2
    have hpmeetT : (p.support ∩ T).Nonempty :=
      FiniteFrontierCompactness.finite_meets_frontier_of_cofinal
        (hYfinite p hpT.1) R D hD hT
        (fun i ↦ ⟨i, le_rfl, by simpa only [← hslice i] using hmeet i⟩)
    have hpnotlimit : ¬ (p.support ∩ C.realVertexLimit).Nonempty := by
      rintro ⟨x, hxp, hxlimit⟩
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxlimit
      obtain ⟨q, ⟨hqT, hqnot⟩, hqinitial⟩ := hretained i
      have hqp : q = p := by
        by_contra hne
        exact Set.disjoint_left.1 (hYwarp hqT.1 hpT.1 hne)
          (hqinitial ▸ q.initial_mem_support)
          (hpinitial ▸ p.initial_mem_support)
      subst q
      exact hqnot ⟨hpT.1, ⟨x, hxp, hxi⟩⟩
    apply Or.inr
    refine ⟨p, ⟨⟨hpT.1, hpmeetT⟩, ?_⟩, hpinitial⟩
    intro hpmeet
    apply hpnotlimit
    simpa only [C.eventualRelationBlueprint_vertexSet] using hpmeet.2

/-- Source retention only needs the union boundary to be contained in the
actual later frontier.  New frontier points do not harm the retained family. -/
theorem eventualRelationBlueprint_covers_source_of_limitBoundary_subset
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (slice R D : I → Set V) (T : Set V)
    (hcover : ∀ i, Gamma.source ⊆ (C.stage i).initialSet ∪
      (C.stage i).retainedReferenceInitials (slice i))
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : ∀ p ∈ Y, p.support.Finite)
    (hslice : ∀ i, slice i = R i \ D i)
    (hD : Monotone D) (hT : ((⋃ i, R i) \ ⋃ i, D i) ⊆ T) :
    Gamma.source ⊆ C.eventualRelationBlueprint.initialSet ∪
      C.eventualRelationBlueprint.retainedReferenceInitials T := by
  intro a ha
  rcases C.eventualRelationBlueprint_covers_source slice R D
      ((⋃ i, R i) \ ⋃ i, D i) hcover hYwarp hYfinite hslice hD rfl ha with
      haroot | haretained
  · exact Or.inl haroot
  · rcases haretained with ⟨p, ⟨⟨hpY, x, hxp, hxBoundary⟩, hpnot⟩, hpinitial⟩
    exact Or.inr ⟨p, ⟨⟨hpY, x, hxp, hT hxBoundary⟩, hpnot⟩, hpinitial⟩

#print axioms eventualTerminal_mem_target_or_stage_terminal
#print axioms eventualTerminal_popular_or_persistent
#print axioms realRelationBlueprint_terminals_subset_target
#print axioms eventualRelationBlueprint_covers_source

end IndexedRealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599

