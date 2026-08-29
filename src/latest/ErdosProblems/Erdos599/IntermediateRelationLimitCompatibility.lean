/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IntermediateRelationLimitRay

/-!
# Source-faithful compatibility for intermediate relation limits

Replacing an imaginary edge by a new real path can introduce a new incoming
edge at the old head.  Thus the full predecessor-preservation hypothesis in
`IntermediateRelationLimit` is stronger than the extension relation used in
Assertion 9.32.  This file gives an additive compiler which instead asks only
for the actual missing well-foundedness boundary: the eventual full relation
must contain no reverse directed ray.

Source roots do not require predecessor preservation.  If a source vertex is
incident with an eventual incoming edge, it occurs in that stage.  The source
coverage condition of that very stage then makes it initial, contradicting
the incoming edge; the retained-reference alternative also contradicts the
fact that the reference path meets the stage at its own initial vertex.

Countable boundedness of the stage order supplies the compatibility datum by
localizing every countable reverse ray at one stage.  This is particularly
useful at final limits; at arbitrary proper limits it is deliberately exposed
as a separate, honest hypothesis.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace RealExtensionChain

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {T Z persistent B : Set V}
variable {I : Type v} [LinearOrder I] [Nonempty I]

/-- The precise extra boundary needed to orient the eventual full relation.
It is invariant under subdivision and makes no claim about predecessors of
vertices already present at an earlier stage. -/
structure EventualRelationLimitCompatibility
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop where
  no_reverse_ray :
    ¬ Alternating.ContainsReverseDirectedRay C.eventualEdgeLimit

/-- Compatibility with the older, stronger API.  This adapter is useful
when a concrete transition really does preserve every predecessor; the
source-faithful compiler itself does not require that property. -/
def EventualRelationLimitCompatibility.ofNoNewPredecessors
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) : C.EventualRelationLimitCompatibility where
  no_reverse_ray :=
    C.eventualEdgeLimit_not_containsReverseDirectedRay H

/-- A countably bounded stage order supplies the compatibility datum by
capturing all edges of a reverse ray at one stage. -/
def EventualRelationLimitCompatibility.ofCountablyBounded
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.CountablyBounded) : C.EventualRelationLimitCompatibility where
  no_reverse_ray :=
    C.eventualEdgeLimit_not_containsReverseDirectedRay_of_countablyBounded H

/-- The decomposition core for a source-faithful compatible intermediate
limit. -/
def compatibleEventualRelationLimitCore
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility) :
    Alternating.RelationDecomposition.ForwardOrientation
      (imaginaryGraph Gamma Y kappa) :=
  Classical.choose (exists_forwardOrientation_exact
    C.eventualEdgeLimit C.realVertexLimit C.eventualEdgeLimit_in_graph
      C.eventualEdgeLimit_endpoints C.eventualEdgeLimit_biUnique
      C.eventualEdgeLimit_not_containsDirectedCycle K.no_reverse_ray)

theorem compatibleEventualRelationLimitCore_spec
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility) :
    (C.compatibleEventualRelationLimitCore K).edge = C.eventualEdgeLimit ∧
      (C.compatibleEventualRelationLimitCore K).carrier =
        C.realVertexLimit :=
  Classical.choose_spec (exists_forwardOrientation_exact
    C.eventualEdgeLimit C.realVertexLimit C.eventualEdgeLimit_in_graph
      C.eventualEdgeLimit_endpoints C.eventualEdgeLimit_biUnique
      C.eventualEdgeLimit_not_containsDirectedCycle K.no_reverse_ray)

/-- The proper-limit blueprint obtained from the eventual full-edge relation
under the direct reverse-ray compatibility boundary. -/
def compatibleEventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility) :
    LinkageBlueprint Gamma Y kappa :=
  orientationBlueprint (C.compatibleEventualRelationLimitCore K)

theorem compatibleEventualRelationLimit_vertexSet
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility) :
    (C.compatibleEventualRelationLimit K).vertexSet =
      C.realVertexLimit := by
  rw [compatibleEventualRelationLimit, orientationBlueprint_vertexSet,
    (C.compatibleEventualRelationLimitCore_spec K).2]

theorem compatibleEventualRelationLimit_edgeSet
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility) :
    (C.compatibleEventualRelationLimit K).edgeSet =
      C.eventualEdgeLimit := by
  rw [compatibleEventualRelationLimit, orientationBlueprint_edgeSet,
    (C.compatibleEventualRelationLimitCore_spec K).1]

/-- The real part is exactly the monotone union of stage real edges. -/
theorem compatibleEventualRelationLimit_realPart_edges
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility) :
    (C.compatibleEventualRelationLimit K).realPart.edges =
      C.realEdgeLimit := by
  rw [realPart_edges, C.compatibleEventualRelationLimit_edgeSet K]
  apply Set.Subset.antisymm
  · rintro e ⟨he, hereal⟩
    obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 he
    exact Set.mem_iUnion.2 ⟨i, hi i le_rfl, hereal⟩
  · intro e he
    exact ⟨C.realEdgeLimit_subset_eventualEdgeLimit he, by
      obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
      exact hei.2⟩

/-- Every stage real part includes into the compatible proper limit. -/
theorem realPart_extends_compatibleEventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility) (i : I) :
    (C.stage i).realPart.Extends
      (C.compatibleEventualRelationLimit K).realPart := by
  constructor
  · change (C.stage i).vertexSet ⊆
      (C.compatibleEventualRelationLimit K).vertexSet
    rw [C.compatibleEventualRelationLimit_vertexSet K]
    exact C.stage_vertices_subset_realVertexLimit i
  · rw [C.compatibleEventualRelationLimit_realPart_edges K]
    exact C.stage_edges_subset_realEdgeLimit i

/-- A source vertex in the union carrier has no eventual incoming edge.
Unlike the older stage-initial-root lemma, this uses source coverage at the
stage witnessing the alleged incoming edge and needs no predecessor
preservation. -/
theorem source_mem_eventualRelationRoots
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    {a : V} (ha : a ∈ Gamma.source) (haLimit : a ∈ C.realVertexLimit) :
    a ∈ C.realVertexLimit ∧
      ¬ ∃ y, (y, a) ∈ C.eventualEdgeLimit := by
  refine ⟨haLimit, ?_⟩
  rintro ⟨y, hya⟩
  obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 hya
  have hyai : (y, a) ∈ (C.stage i).edgeSet := hi i le_rfl
  have haStage : a ∈ (C.stage i).vertexSet :=
    (Alternating.familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hyai).2
  rcases (C.isBlueprint i).covers_source ha with hainitial | hretained
  · exact no_incoming_edge_of_mem_initialSet (C.stage i) hainitial
      ⟨y, hyai⟩
  · rcases hretained with ⟨p, ⟨hpT, hpnoti⟩, hpinitial⟩
    exact hpnoti
      ⟨hpT.1, ⟨a, hpinitial ▸ p.initial_mem_support,
        by simpa only [realPart_vertices] using haStage⟩⟩

/-- Source coverage passes to the compatible limit using only the stage
blueprint conditions and source-root lemma above. -/
theorem compatibleEventualRelationLimit_covers_source
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (hYwarp : Gamma.IsWarp Y) :
    Gamma.source ⊆
      {x | x ∈ C.realVertexLimit ∧
        ¬ ∃ y, (y, x) ∈ C.eventualEdgeLimit} ∪
        Gamma.initialSet
          (referencePathsMeeting Y T \
            referencePathsMeeting Y C.realVertexLimit) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  intro a ha
  rcases (C.isBlueprint i₀).covers_source ha with hainitial | hretained
  · apply Or.inl
    apply C.source_mem_eventualRelationRoots ha
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
        apply C.source_mem_eventualRelationRoots ha
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

/-- Exact (9.32) accounting for every old vertex. -/
theorem accounted_compatibleEventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility) (i : I) :
    (C.stage i).vertexSet ⊆
      ((C.compatibleEventualRelationLimit K).terminalSet ∩
          (C.stage i).terminalSet) ∪
        {x | ∃ y, (x, y) ∈
          (C.stage i).familyGraph.edges ∩
            (C.compatibleEventualRelationLimit K).familyGraph.edges} ∪
          (C.compatibleEventualRelationLimit K).completedRealVertices B := by
  classical
  intro x hxi
  by_cases hxterm :
      x ∈ (C.compatibleEventualRelationLimit K).terminalSet
  · by_cases hxiterm : x ∈ (C.stage i).terminalSet
    · exact Or.inl (Or.inl ⟨hxterm, hxiterm⟩)
    · by_cases hcompleted :
        ∃ j, x ∈ (C.stage j).completedRealVertices B
      · obtain ⟨j, hxcompleted⟩ := hcompleted
        exact Or.inr <| completedRealVertices_mono
          (C.realPart_extends_compatibleEventualRelationLimit K j)
          hxcompleted
      · obtain ⟨y, hxyi⟩ :=
          (C.stage i).exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
            hxi hxiterm
        have hxyeventual : (x, y) ∈ C.eventualEdgeLimit := by
          apply (WarpLimits.mem_setLiminf _ _).2
          refine ⟨i, fun j hij ↦ ?_⟩
          rcases (C.realExtends hij).2 hxi with (hcommon | hdone)
          · rcases hcommon with hterm | hedge
            · exact False.elim (hxiterm hterm.2)
            · rcases hedge with ⟨z, hxzi, hxzj⟩
              have hyz : y = z :=
                Alternating.IsWarp.familyEdges_rightUnique
                  (C.stage i).isWarp hxyi hxzi
              change (x, z) ∈ (C.stage j).edgeSet at hxzj
              simpa [hyz] using hxzj
          · exact False.elim (hcompleted ⟨j, hdone⟩)
        have hxyLimit :
            (x, y) ∈ (C.compatibleEventualRelationLimit K).edgeSet := by
          rwa [C.compatibleEventualRelationLimit_edgeSet K]
        exact False.elim <|
          (mem_familyGraph_terminals_of_mem_terminalSet hxterm).2
            ⟨y, hxyLimit⟩
  · have hxlimitVertex :
        x ∈ (C.compatibleEventualRelationLimit K).vertexSet := by
      rw [C.compatibleEventualRelationLimit_vertexSet K]
      exact C.stage_vertices_subset_realVertexLimit i
        (by simpa only [realPart_vertices] using hxi)
    obtain ⟨y, hxyLimit⟩ :=
      (C.compatibleEventualRelationLimit K)
        |>.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
          hxlimitVertex hxterm
    have hxyEventual : (x, y) ∈ C.eventualEdgeLimit := by
      change (x, y) ∈
        (C.compatibleEventualRelationLimit K).edgeSet at hxyLimit
      rwa [C.compatibleEventualRelationLimit_edgeSet K] at hxyLimit
    obtain ⟨j₀, hj₀⟩ :=
      (WarpLimits.mem_setLiminf _ _).1 hxyEventual
    obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
    have hxyj : (x, y) ∈ (C.stage j).edgeSet := hj₀ j hj₀j
    rcases (C.realExtends hij).2 hxi with (hcommon | hcompleted)
    · rcases hcommon with hterm | hedge
      · exact False.elim <|
          (mem_familyGraph_terminals_of_mem_terminalSet hterm.1).2
            ⟨y, hxyj⟩
      · rcases hedge with ⟨z, hxzi, hxzj⟩
        have hzy : z = y :=
          Alternating.IsWarp.familyEdges_rightUnique
            (C.stage j).isWarp hxzj hxyj
        exact Or.inl (Or.inr ⟨y, hzy ▸ hxzi, hxyLimit⟩)
    · exact Or.inr <| completedRealVertices_mono
        (C.realPart_extends_compatibleEventualRelationLimit K j)
        hcompleted

/-- A sink is either already in the completion target or is a terminal of
every stage in which it occurs. -/
theorem compatibleEventualRelationSink_mem_B_or_stage_terminal
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    {x : V}
    (hx : x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.eventualEdgeLimit) (i : I)
    (hxi : x ∈ (C.stage i).vertexSet) :
    x ∈ B ∨ x ∈ (C.stage i).terminalSet := by
  classical
  by_cases hxiterm : x ∈ (C.stage i).terminalSet
  · exact Or.inr hxiterm
  · obtain ⟨y, hxyi⟩ :=
      (C.stage i).exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
        hxi hxiterm
    by_cases hxyeventual : (x, y) ∈ C.eventualEdgeLimit
    · exact False.elim (hx.2 ⟨y, hxyeventual⟩)
    · have hcompleted :
          ∃ j, i ≤ j ∧ x ∈ (C.stage j).completedRealVertices B := by
        by_contra hnone
        apply hxyeventual
        apply (WarpLimits.mem_setLiminf _ _).2
        refine ⟨i, fun j hij ↦ ?_⟩
        rcases (C.realExtends hij).2 hxi with (hcommon | hdone)
        · rcases hcommon with hterm | hedge
          · exact False.elim (hxiterm hterm.2)
          · rcases hedge with ⟨z, hxzi, hxzj⟩
            have hyz : y = z :=
              Alternating.IsWarp.familyEdges_rightUnique
                (C.stage i).isWarp hxyi hxzi
            change (x, z) ∈ (C.stage j).edgeSet at hxzj
            simpa [hyz] using hxzj
        · exact False.elim (hnone ⟨j, hij, hdone⟩)
      obtain ⟨j, hij, hxcompleted⟩ := hcompleted
      by_cases hxB : x ∈ B
      · exact Or.inl hxB
      · have hxrealterm : x ∈ (C.stage j).realPart.terminals := by
          refine ⟨by
            simpa only [realPart_vertices] using C.stage_vertices_mono hij
              (by simpa only [realPart_vertices] using hxi), ?_⟩
          rintro ⟨z, hxzj⟩
          apply hx.2
          refine ⟨z, C.realEdgeLimit_subset_eventualEdgeLimit ?_⟩
          exact C.stage_edges_subset_realEdgeLimit j hxzj
        exact False.elim <|
          (not_mem_realTerminals_of_realLinksTo hxB
            (realLinksTo_of_mem_completedRealVertices hxcompleted))
              hxrealterm

theorem compatibleEventualRelationLimit_terminalBoundary
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T) :
    {x | x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.eventualEdgeLimit} ⊆
        {x | IsPopular Gamma Y persistent kappa x} ∪ T := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx.1
  rcases C.compatibleEventualRelationSink_mem_B_or_stage_terminal hx i
      (by simpa only [realPart_vertices] using hxi) with hxB | hxterm
  · exact hB hxB
  · exact (C.isBlueprint i).terminals_popular hxterm

theorem compatibleEventualRelationLimit_stableBoundary
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (hstableB : B ∩ T ⊆ persistent) :
    {x | x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.eventualEdgeLimit} ∩ T ⊆ persistent := by
  rintro x ⟨hx, hxT⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx.1
  rcases C.compatibleEventualRelationSink_mem_B_or_stage_terminal hx i
      (by simpa only [realPart_vertices] using hxi) with hxB | hxterm
  · exact hstableB ⟨hxB, hxT⟩
  · exact (C.stable i) ⟨hxterm, hxT⟩

/-- All linkage-blueprint fields for the source-faithful proper limit. -/
theorem compatibleEventualRelationLimit_isLinkageBlueprint
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility)
    (hYwarp : Gamma.IsWarp Y)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (D : C.EventualRelationLimitBoundary) :
    (C.compatibleEventualRelationLimit K).IsLinkageBlueprint
      T Z persistent := by
  let O := C.compatibleEventualRelationLimitCore K
  have hOE : O.edge = C.eventualEdgeLimit :=
    (C.compatibleEventualRelationLimitCore_spec K).1
  have hOC : O.carrier = C.realVertexLimit :=
    (C.compatibleEventualRelationLimitCore_spec K).2
  refine
    { vertices_roofed := ?_
      covers_source := ?_
      vertices_closed := ?_
      card_paths := ?_
      infinitely_many_strong := ?_
      terminals_popular := ?_ }
  · intro x hx
    rw [C.compatibleEventualRelationLimit_vertexSet K] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact (C.isBlueprint i).vertices_roofed (by simpa using hxi)
  · rw [compatibleEventualRelationLimit,
      orientationBlueprint_initialSet_eq_no_incoming,
      retainedReferenceInitials, orientationBlueprint_vertexSet, hOC, hOE]
    exact C.compatibleEventualRelationLimit_covers_source hYwarp
  · intro x hx
    rw [C.compatibleEventualRelationLimit_vertexSet K] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact (C.isBlueprint i).vertices_closed (by simpa using hxi)
  · change #(Set.range O.rootPath) ≤ kappa
    refine Cardinal.mk_range_le.trans ?_
    refine (Cardinal.mk_subtype_mono (fun x hx ↦ hx.1)).trans ?_
    simpa only [hOC] using D.card_vertices
  · intro r hr
    apply D.every_relation_ray_strong r
    intro e he
    rw [← hOE, ← orientationBlueprint_edgeSet O]
    exact Set.mem_iUnion.2
      ⟨(Sum.inr r : DirectedPath.Path (imaginaryGraph Gamma Y kappa)),
        Set.mem_iUnion.2 ⟨hr, he⟩⟩
  · rw [compatibleEventualRelationLimit,
      orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
    exact C.compatibleEventualRelationLimit_terminalBoundary hB

theorem compatibleEventualRelationLimit_stable
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility)
    (hstableB : B ∩ T ⊆ persistent) :
    (C.compatibleEventualRelationLimit K).Stable T persistent := by
  rw [Stable, compatibleEventualRelationLimit,
    orientationBlueprint_terminalSet_eq_no_outgoing,
    (C.compatibleEventualRelationLimitCore_spec K).2,
    (C.compatibleEventualRelationLimitCore_spec K).1]
  exact C.compatibleEventualRelationLimit_stableBoundary hstableB

/-- Every stage is related to the compatible limit by the actual 9.32
`RealExtends` relation. -/
theorem realExtends_compatibleEventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility) (i : I) :
    (C.stage i).RealExtends (C.compatibleEventualRelationLimit K) B :=
  ⟨C.realPart_extends_compatibleEventualRelationLimit K i,
    C.accounted_compatibleEventualRelationLimit K i⟩

/-- Source-faithful proper-limit compiler.  It intentionally does not claim
that full predecessor preservation propagates through the limit. -/
theorem stableLimitConclusion_compatibleEventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (K : C.EventualRelationLimitCompatibility)
    (hYwarp : Gamma.IsWarp Y)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (D : C.EventualRelationLimitBoundary) :
    StableLimitConclusion C.stage
      (C.compatibleEventualRelationLimit K) T Z persistent B :=
  ⟨C.compatibleEventualRelationLimit_isLinkageBlueprint K hYwarp hB D,
    C.compatibleEventualRelationLimit_stable K hstableB,
    C.realExtends_compatibleEventualRelationLimit K⟩

/-- Under countable boundedness both infinitary relation boundaries follow
from stage blueprints, leaving only the cardinal estimate. -/
def EventualRelationLimitBoundary.ofCountablyBounded
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.CountablyBounded) (hcard : #C.realVertexLimit ≤ kappa) :
    C.EventualRelationLimitBoundary where
  card_vertices := hcard
  every_relation_ray_strong :=
    C.eventualEdgeLimit_every_ray_strong_of_countablyBounded H

end RealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599
