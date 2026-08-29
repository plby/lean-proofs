/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantForwardRetainedInterval

/-!
# Ordering the finite forward component cluster

Every retained occurrence on one selected forward link is reached from the
same link start in the stopped retained relation.  Right-uniqueness of the
finite link therefore compares any two occurrence heads.  In a full
source-reachable component warp, such a comparison stays in one warp member.
Consequently distinct displaced components use distinct forward links, not
merely distinct forward edges.

This is the ordered finite measure needed by the simultaneous component
exchange.  It is proved from the literal stopped relation and the canonical
component equations; no realization or exchange provider is assumed.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedDecode

open DirectedPath Alternating GroundingSourceReachableSinkWarp

universe u

variable {V : Type u} {Gamma : DWeb V}

private theorem retainedForwardLink_chain_mono
    {T : Set V} {Q : AltPath Gamma.graph}
    (l : Link Gamma.graph) (hl : l ∈ Q.links)
    (hldir : l.direction = .forward) {x y : V}
    (hstart : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) l.path.start x)
    (hxy : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) x y) :
    Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ retainedForwardEdgesAt T Q) x y := by
  induction hxy with
  | refl => exact .refl
  | tail hab hbc ih =>
      exact ih.tail ⟨l, hl, hldir, hbc.1, hbc.2,
        hstart.trans hab⟩

/-- Two retained edge heads on the same selected forward link are comparable
inside the actual stopped retained relation.  No global no-frontier premise
is needed: the two occurrence records already retain their complete stopped
prefixes from the common link start. -/
theorem RetainedForwardOccurrence.head_reaches_or_reached_by_of_sameLink
    {T : Set V} {Q : AltPath Gamma.graph} {e f : V × V}
    (Oe : RetainedForwardOccurrence T Q e)
    (Of : RetainedForwardOccurrence T Q f)
    (hlink : Of.trace.link Of.linkIndex =
      Oe.trace.link Oe.linkIndex) :
    Relation.ReflTransGen
        (fun a b ↦ (a, b) ∈ retainedForwardEdgesAt T Q) e.2 f.2 ∨
      Relation.ReflTransGen
        (fun a b ↦ (a, b) ∈ retainedForwardEdgesAt T Q) f.2 e.2 := by
  let l := Oe.trace.link Oe.linkIndex
  have hl : l ∈ Q.links := by
    rw [Oe.path_eq]
    exact ⟨Oe.linkIndex, rfl⟩
  have heStart : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) l.path.start e.2 :=
    Oe.tail_reachable.tail ⟨Oe.edge_mem, Oe.tail_not_frontier⟩
  have hfStart : Relation.ReflTransGen
      (retainedForwardLinkStepAt T l) l.path.start f.2 := by
    have h := Of.tail_reachable.tail
      ⟨Of.edge_mem, Of.tail_not_frontier⟩
    simpa only [l, hlink] using h
  have hright : Relator.RightUnique (retainedForwardLinkStepAt T l) := by
    intro a b c hab hac
    exact (FinitePath.edgeSet_biUnique l.path).2 hab.1 hac.1
  rcases Relation.ReflTransGen.total_of_right_unique hright heStart hfStart with
    hef | hfe
  · exact Or.inl
      (retainedForwardLink_chain_mono l hl Oe.direction heStart hef)
  · have hldir : l.direction = .forward := by
      simpa only [l, ← hlink] using Of.direction
    exact Or.inr
      (retainedForwardLink_chain_mono l hl hldir hfStart hfe)

/-- Equality of the numerical forward-link indices determines equality of
the literal selected links.  The occurrence records may initially package
different finite traces, but both traces represent the same selected
alternating path. -/
theorem RetainedForwardOccurrence.link_eq_of_linkIndex_val_eq
    {T : Set V} {Q : AltPath Gamma.graph} {e f : V × V}
    (Oe : RetainedForwardOccurrence T Q e)
    (Of : RetainedForwardOccurrence T Q f)
    (hindex : Oe.linkIndex.1 = Of.linkIndex.1) :
    Of.trace.link Of.linkIndex = Oe.trace.link Oe.linkIndex := by
  rcases Oe with ⟨traceE, hQE, iE, hdirE, hmemE, nE, hnE,
    hedgeE, htailE, hreachE⟩
  rcases Of with ⟨traceF, hQF, iF, hdirF, hmemF, nF, hnF,
    hedgeF, htailF, hreachF⟩
  have htrace : traceE = traceF :=
    AltPath.finite.inj (hQE.symm.trans hQF)
  subst traceF
  have hfin : iF = iE := Fin.ext hindex.symm
  simpa only [hfin]

private theorem reflTransGen_stays_in_component
    {E : Set (V × V)} {A : Set V} {W : Set Gamma.DPath}
    (hW : Gamma.IsWarp W)
    (hWEdges : familyEdges W = RootReachableRelation.edges E A)
    (hWVertex : Gamma.vertexSet W = RootReachableRelation.carrier E A)
    (p : Gamma.DPath) (hpW : p ∈ W) {x y : V}
    (hx : x ∈ p.support)
    (hxy : Relation.ReflTransGen (fun a b ↦ (a, b) ∈ E) x y) :
    y ∈ p.support := by
  induction hxy with
  | refl => exact hx
  | @tail b c _hab hbc ih =>
      have htailCarrier : b ∈ RootReachableRelation.carrier E A := by
        rw [← hWVertex]
        exact ⟨p, hpW, ih⟩
      have hbcFamily : (b, c) ∈ familyEdges W := by
        rw [hWEdges]
        exact ⟨hbc, htailCarrier⟩
      simp only [familyEdges, Set.mem_iUnion] at hbcFamily
      obtain ⟨q, hqW, hbcQ⟩ := hbcFamily
      have htailQ : b ∈ q.support :=
        (q.edgeSet_subset_support_prod hbcQ).1
      have hpq : p = q := by
        by_contra hpq
        exact Set.disjoint_left.1 (hW hpW hqW hpq) ih htailQ
      rw [hpq]
      exact (q.edgeSet_subset_support_prod hbcQ).2

/-- In the canonical source-reachable component realization, two components
whose selected entry edges occur on the same retained forward link are the
same component.  Thus a component-to-occurrence assignment is automatically
injective already at the level of link indices. -/
theorem retainedForwardOccurrences_component_eq_of_sameLink
    {E : Set (V × V)} {A T : Set V}
    {Q : AltPath Gamma.graph} {W : Set Gamma.DPath}
    (hW : Gamma.IsWarp W)
    (hWEdges : familyEdges W = RootReachableRelation.edges E A)
    (hWVertex : Gamma.vertexSet W = RootReachableRelation.carrier E A)
    (hretained : retainedForwardEdgesAt T Q ⊆ E)
    {p q : FinitePath Gamma.graph} (hpW : (Sum.inl p : Gamma.DPath) ∈ W)
    (hqW : (Sum.inl q : Gamma.DPath) ∈ W)
    {e f : V × V} (heP : e ∈ p.edgeSet) (hfQ : f ∈ q.edgeSet)
    (Oe : RetainedForwardOccurrence T Q e)
    (Of : RetainedForwardOccurrence T Q f)
    (hlink : Of.trace.link Of.linkIndex =
      Oe.trace.link Oe.linkIndex) :
    p = q := by
  have hePHead : e.2 ∈ p.support :=
    (p.edgeSet_subset_support_prod heP).2
  have hfQHead : f.2 ∈ q.support :=
    (q.edgeSet_subset_support_prod hfQ).2
  rcases Oe.head_reaches_or_reached_by_of_sameLink Of hlink with hef | hfe
  · have hefE : Relation.ReflTransGen (fun a b ↦ (a, b) ∈ E) e.2 f.2 :=
      Relation.ReflTransGen.mono (fun _ _ h ↦ hretained h) _ _ hef
    have hfP : f.2 ∈ p.support :=
      reflTransGen_stays_in_component hW hWEdges hWVertex
        (.inl p) hpW hePHead hefE
    by_contra hpq
    exact Set.disjoint_left.1 (hW hpW hqW (fun h ↦ hpq (Sum.inl.inj h)))
      hfP hfQHead
  · have hfeE : Relation.ReflTransGen (fun a b ↦ (a, b) ∈ E) f.2 e.2 :=
      Relation.ReflTransGen.mono (fun _ _ h ↦ hretained h) _ _ hfe
    have heQ : e.2 ∈ q.support :=
      reflTransGen_stays_in_component hW hWEdges hWVertex
        (.inl q) hqW hfQHead hfeE
    by_contra hpq
    exact Set.disjoint_left.1 (hW hpW hqW (fun h ↦ hpq (Sum.inl.inj h)))
      hePHead heQ

/-- A selected retained entry for every finite component is injective
already at the numerical forward-link index.  Hence the displaced component
cluster embeds in the finite list of forward links of the one selected
compression, rather than merely in its edge set.

The component membership and the exact retained occurrence are preserved,
so the resulting link order can drive the simultaneous exchange. -/
theorem exists_injective_retainedForwardLinkIndices
    {E : Set (V × V)} {A T : Set V}
    {Q : AltPath Gamma.graph} {W : Set Gamma.DPath}
    (hfinite : Q.IsFinite)
    (hW : Gamma.IsWarp W)
    (hWEdges : familyEdges W = RootReachableRelation.edges E A)
    (hWVertex : Gamma.vertexSet W = RootReachableRelation.carrier E A)
    (hretained : retainedForwardEdgesAt T Q ⊆ E)
    {C : Set (FinitePath Gamma.graph)}
    (hCW : ∀ p : C, (Sum.inl p.1 : Gamma.DPath) ∈ W)
    (hentry : ∃ entry : C → {e // e ∈ retainedForwardEdgesAt T Q},
      Function.Injective entry ∧ ∀ p, (entry p).1 ∈ p.1.edgeSet) :
    ∃ occurrence : C → Σ e, RetainedForwardOccurrence T Q e,
      Function.Injective (fun p ↦ (occurrence p).2.linkIndex.1) ∧
        ∀ p, (occurrence p).1 ∈ p.1.edgeSet := by
  obtain ⟨occurrence, _hedgeInjective, hoccurs⟩ :=
    exists_injective_retainedForwardOccurrences hfinite
      (fun p : C ↦ p.1.edgeSet) hentry
  refine ⟨occurrence, ?_, hoccurs⟩
  intro p q hindex
  apply Subtype.ext
  apply retainedForwardOccurrences_component_eq_of_sameLink
    hW hWEdges hWVertex hretained (hCW p) (hCW q)
    (hoccurs p) (hoccurs q) (occurrence p).2 (occurrence q).2
  exact (occurrence p).2.link_eq_of_linkIndex_val_eq
    (occurrence q).2 hindex

end GroundingErasedDecode
end Erdos599

#print axioms
  Erdos599.GroundingErasedDecode.RetainedForwardOccurrence.head_reaches_or_reached_by_of_sameLink
#print axioms
  Erdos599.GroundingErasedDecode.retainedForwardOccurrences_component_eq_of_sameLink
#print axioms
  Erdos599.GroundingErasedDecode.exists_injective_retainedForwardLinkIndices
