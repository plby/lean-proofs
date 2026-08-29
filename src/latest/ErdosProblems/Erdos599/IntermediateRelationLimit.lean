/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RealExtensionRelationLimit
import ErdosProblems.Erdos599.GlobalAdvance931

/-!
# Intermediate relation limits for the half-way scheduler

The all-real relation limit in `RealExtensionRelationLimit` is the correct
*final* scheduler limit, after fairness has resolved every real terminal.  It
is not the correct object at a proper limit ordinal: deleting every imaginary
edge can create new terminals and destroy stability.

At a proper limit we instead keep every full blueprint edge which is present
eventually.  Real edges are monotone under `RealExtends`, so their union is
contained in this eventual full-edge relation and is exactly its real part.
The carrier remains the union of the stage vertex sets.  The exact accounting
disjunction (9.32) then proves, without an eventual-completion hypothesis,
that every stage really extends the intermediate limit: an old vertex is
completed, remains a common terminal, or its unique old outgoing edge is
eventually present.

The only genuinely infinitary blueprint boundary left explicit below is the
strong-edge condition for rays of the eventual relation.  All source, roof,
closure, cardinal, terminal-popularity, stability, and (9.32) fields are
derived from the stage blueprints and the displayed compatibility conditions.
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

/-- Full blueprint edges which occur at every sufficiently late stage.  This
is the relation used at nonfinal limit ordinals of the half-way scheduler. -/
def eventualEdgeLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Set (V × V) :=
  WarpLimits.setLiminf fun i ↦ (C.stage i).edgeSet

/-- Full predecessor preservation along the chain.  The real-only version is
enough for the final all-real limit; the full version is needed while
imaginary edges are retained at proper limit ordinals. -/
structure NoNewPredecessors
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop where
  of_le : ∀ {i j : I}, i ≤ j → (C.stage i).NoNewPredecessorsTo (C.stage j)

/-- Every monotone real edge survives in the eventual full-edge relation. -/
theorem realEdgeLimit_subset_eventualEdgeLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    C.realEdgeLimit ⊆ C.eventualEdgeLimit := by
  intro e he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  apply (WarpLimits.mem_setLiminf _ _).2
  refine ⟨i, fun j hij ↦ ?_⟩
  exact (C.stage_edges_mono hij hei).1

/-- An eventual full edge already occurs at one stage and therefore is an
edge of the imaginary augmentation. -/
theorem eventualEdgeLimit_in_graph
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    C.eventualEdgeLimit ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 he
  have hei : e ∈ (C.stage i).edgeSet := hi i le_rfl
  simp only [edgeSet, Set.mem_iUnion] at hei
  obtain ⟨p, hp, hep⟩ := hei
  exact p.edgeSet_subset_adj hep

/-- Both endpoints of an eventual full edge belong to the union carrier. -/
theorem eventualEdgeLimit_endpoints
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    ∀ e ∈ C.eventualEdgeLimit,
      e.1 ∈ C.realVertexLimit ∧ e.2 ∈ C.realVertexLimit := by
  intro e he
  obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 he
  have hei := hi i le_rfl
  have hends :
      e.1 ∈ (C.stage i).vertexSet ∧ e.2 ∈ (C.stage i).vertexSet :=
    Alternating.familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hei
  exact ⟨C.stage_vertices_subset_realVertexLimit i (by simpa using hends.1),
    C.stage_vertices_subset_realVertexLimit i (by simpa using hends.2)⟩

/-- Eventual full edges remain bi-unique.  Two competing edges can be moved
to a common late stage and compared in that stage's warp. -/
theorem eventualEdgeLimit_biUnique
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ C.eventualEdgeLimit) := by
  constructor
  · intro x y z hxz hyz
    obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 hxz
    obtain ⟨j, hj⟩ := (WarpLimits.mem_setLiminf _ _).1 hyz
    rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
    exact (Alternating.IsWarp.familyEdges_leftUnique (C.stage k).isWarp)
      (hi k hik) (hj k hjk)
  · intro x y z hxy hxz
    obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 hxy
    obtain ⟨j, hj⟩ := (WarpLimits.mem_setLiminf _ _).1 hxz
    rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
    exact (Alternating.IsWarp.familyEdges_rightUnique (C.stage k).isWarp)
      (hi k hik) (hj k hjk)

/-- A finite directed cycle in the eventual relation already occurs at one
stage, contradicting the path-family representation there. -/
theorem eventualEdgeLimit_not_containsDirectedCycle
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    ¬ Alternating.ContainsDirectedCycle C.eventualEdgeLimit := by
  rintro ⟨Q, hQ⟩
  let stageOf : Fin Q.length → I := fun n ↦
    Classical.choose ((WarpLimits.mem_setLiminf _ _).1 (hQ ⟨n, rfl⟩))
  have hstageOf (n : Fin Q.length) :
      ∀ j, stageOf n ≤ j →
        (Q.vertex n, Q.vertex (Q.next n)) ∈ (C.stage j).edgeSet :=
    Classical.choose_spec
      ((WarpLimits.mem_setLiminf _ _).1 (hQ ⟨n, rfl⟩))
  obtain ⟨j, hj⟩ := Finite.exists_le stageOf
  have hQj : Q.EdgeSet ⊆ (C.stage j).edgeSet := by
    rintro e ⟨n, rfl⟩
    exact hstageOf n j (hj n)
  exact blueprint_edgeSet_not_containsDirectedCycle (C.stage j) ⟨Q, hQj⟩

/-- Full predecessor preservation rules out a reverse ray in the eventual
full-edge relation.  Starting at a stage containing the first edge, pull
each later predecessor edge back to that same stage. -/
theorem eventualEdgeLimit_not_containsReverseDirectedRay
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) :
    ¬ Alternating.ContainsReverseDirectedRay C.eventualEdgeLimit := by
  rintro ⟨R, hR⟩
  obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 (hR 0)
  have hstage : ∀ n : ℕ, (R.vertex (n + 1), R.vertex n) ∈
      (C.stage i).edgeSet := by
    intro n
    induction n with
    | zero => simpa using hi i le_rfl
    | succ n ih =>
        obtain ⟨j, hj⟩ := (WarpLimits.mem_setLiminf _ _).1 (hR (n + 1))
        rcases le_total i j with hij | hji
        · have hx : R.vertex (n + 1) ∈ (C.stage i).vertexSet :=
            (Alternating.familyEdges_subset_vertexSet_prod
              (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths ih).1
          exact H.of_le hij hx (hj j le_rfl)
        · exact hj i hji
  exact blueprint_edgeSet_not_containsReverseDirectedRay (C.stage i)
    ⟨R, hstage⟩

/-- The complete decomposition core for the intermediate relation. -/
def eventualRelationLimitCore
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) :
    Alternating.RelationDecomposition.ForwardOrientation
      (imaginaryGraph Gamma Y kappa) :=
  Classical.choose (exists_forwardOrientation_exact
    C.eventualEdgeLimit C.realVertexLimit C.eventualEdgeLimit_in_graph
      C.eventualEdgeLimit_endpoints C.eventualEdgeLimit_biUnique
      C.eventualEdgeLimit_not_containsDirectedCycle
      (C.eventualEdgeLimit_not_containsReverseDirectedRay H))

theorem eventualRelationLimitCore_spec
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) :
    (C.eventualRelationLimitCore H).edge = C.eventualEdgeLimit ∧
      (C.eventualRelationLimitCore H).carrier = C.realVertexLimit :=
  Classical.choose_spec (exists_forwardOrientation_exact
    C.eventualEdgeLimit C.realVertexLimit C.eventualEdgeLimit_in_graph
      C.eventualEdgeLimit_endpoints C.eventualEdgeLimit_biUnique
      C.eventualEdgeLimit_not_containsDirectedCycle
      (C.eventualEdgeLimit_not_containsReverseDirectedRay H))

/-- The actual proper-limit blueprint: root orbits of the eventual full-edge
relation, with the full union of stage vertices as carrier. -/
def eventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) : LinkageBlueprint Gamma Y kappa :=
  orientationBlueprint (C.eventualRelationLimitCore H)

theorem eventualRelationLimit_vertexSet
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) :
    (C.eventualRelationLimit H).vertexSet = C.realVertexLimit := by
  rw [eventualRelationLimit, orientationBlueprint_vertexSet,
    (C.eventualRelationLimitCore_spec H).2]

theorem eventualRelationLimit_edgeSet
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) :
    (C.eventualRelationLimit H).edgeSet = C.eventualEdgeLimit := by
  rw [eventualRelationLimit, orientationBlueprint_edgeSet,
    (C.eventualRelationLimitCore_spec H).1]

/-- The real part of the intermediate limit is exactly the monotone union of
the stage real parts.  Thus imaginary edges are retained for blueprint
stability without contaminating the final real observable. -/
theorem eventualRelationLimit_realPart_edges
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) :
    (C.eventualRelationLimit H).realPart.edges = C.realEdgeLimit := by
  rw [realPart_edges, C.eventualRelationLimit_edgeSet H]
  apply Set.Subset.antisymm
  · rintro e ⟨he, hereal⟩
    obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 he
    exact Set.mem_iUnion.2 ⟨i, hi i le_rfl, hereal⟩
  · intro e he
    exact ⟨C.realEdgeLimit_subset_eventualEdgeLimit he, by
      obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
      exact hei.2⟩

/-- Every stage real part includes into the intermediate proper limit. -/
theorem realPart_extends_eventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (i : I) :
    (C.stage i).realPart.Extends (C.eventualRelationLimit H).realPart := by
  constructor
  · change (C.stage i).vertexSet ⊆ (C.eventualRelationLimit H).vertexSet
    rw [C.eventualRelationLimit_vertexSet H]
    exact C.stage_vertices_subset_realVertexLimit i
  · rw [C.eventualRelationLimit_realPart_edges H]
    exact C.stage_edges_subset_realEdgeLimit i

/-- Initial vertices at a stage remain roots of the eventual full relation.
This is the exact place where the full, rather than real-only, predecessor
invariant is required. -/
theorem stage_initialSet_subset_eventualRelationRoots
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (i : I) :
    (C.stage i).initialSet ⊆
      {x | x ∈ C.realVertexLimit ∧
        ¬ ∃ y, (y, x) ∈ C.eventualEdgeLimit} := by
  intro x hx
  have hxvertex : x ∈ (C.stage i).vertexSet := by
    rcases hx with ⟨p, hp, rfl⟩
    exact ⟨p, hp, p.initial_mem_support⟩
  refine ⟨C.stage_vertices_subset_realVertexLimit i (by simpa using hxvertex), ?_⟩
  rintro ⟨y, hyx⟩
  obtain ⟨j, hj⟩ := (WarpLimits.mem_setLiminf _ _).1 hyx
  rcases le_total i j with hij | hji
  · exact no_incoming_edge_of_mem_initialSet (C.stage i) hx
      ⟨y, H.of_le hij hxvertex (hj j le_rfl)⟩
  · exact no_incoming_edge_of_mem_initialSet (C.stage i) hx
      ⟨y, hj i hji⟩

/-- Source coverage passes to the intermediate relation limit. -/
theorem eventualRelationLimit_covers_source
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (hYwarp : Gamma.IsWarp Y) :
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
  · exact Or.inl (C.stage_initialSet_subset_eventualRelationRoots H i₀ hainitial)
  · rcases hretained with ⟨p, ⟨hpT, hpnoti₀⟩, hpinitial⟩
    by_cases hpmeet : (p.support ∩ C.realVertexLimit).Nonempty
    · obtain ⟨x, hxp, hxlimit⟩ := hpmeet
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 hxlimit
      rcases (C.isBlueprint j).covers_source ha with hjinitial | hjretained
      · exact Or.inl
          (C.stage_initialSet_subset_eventualRelationRoots H j hjinitial)
      · rcases hjretained with ⟨q, ⟨hqT, hqnotj⟩, hqinitial⟩
        have hqp : q = p := by
          by_contra hne
          have hd := hYwarp hqT.1 hpT.1 hne
          exact Set.disjoint_left.1 hd
            (hqinitial ▸ q.initial_mem_support)
            (hpinitial ▸ p.initial_mem_support)
        subst q
        exact False.elim <| hqnotj
          ⟨hpT.1, ⟨x, hxp, by simpa only [realPart_vertices] using hxj⟩⟩
    · exact Or.inr ⟨p, ⟨hpT, fun hp ↦ hpmeet hp.2⟩, hpinitial⟩

/-- The exact (9.32) accounting statement at an intermediate limit.  Unlike
the final all-real limit theorem, this needs no fairness or eventual terminal
completion: an uncompleted old outgoing edge is forced to survive in the
eventual full-edge relation. -/
theorem accounted_eventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (i : I) :
    (C.stage i).vertexSet ⊆
      ((C.eventualRelationLimit H).terminalSet ∩
          (C.stage i).terminalSet) ∪
        {x | ∃ y, (x, y) ∈
          (C.stage i).familyGraph.edges ∩
            (C.eventualRelationLimit H).familyGraph.edges} ∪
          (C.eventualRelationLimit H).completedRealVertices B := by
  classical
  intro x hxi
  by_cases hxterm : x ∈ (C.eventualRelationLimit H).terminalSet
  · by_cases hxiterm : x ∈ (C.stage i).terminalSet
    · exact Or.inl (Or.inl ⟨hxterm, hxiterm⟩)
    · by_cases hcompleted : ∃ j, x ∈ (C.stage j).completedRealVertices B
      · obtain ⟨j, hxcompleted⟩ := hcompleted
        exact Or.inr <| completedRealVertices_mono
          (C.realPart_extends_eventualRelationLimit H j) hxcompleted
      · obtain ⟨y, hxyi⟩ :=
          (C.stage i).exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
            hxi hxiterm
        have hxyeventual : (x, y) ∈ C.eventualEdgeLimit := by
          apply (WarpLimits.mem_setLiminf _ _).2
          refine ⟨i, fun j hij ↦ ?_⟩
          rcases (C.realExtends hij).2 hxi with (hcommon | hdone)
          · rcases hcommon with hterm | hedge
            · exact False.elim <|
                hxiterm hterm.2
            · rcases hedge with ⟨z, hxzi, hxzj⟩
              have hyz : y = z :=
                Alternating.IsWarp.familyEdges_rightUnique
                  (C.stage i).isWarp hxyi hxzi
              change (x, z) ∈ (C.stage j).edgeSet at hxzj
              simpa [hyz] using hxzj
          · exact False.elim (hcompleted ⟨j, hdone⟩)
        have hxyLimit : (x, y) ∈ (C.eventualRelationLimit H).edgeSet := by
          rwa [C.eventualRelationLimit_edgeSet H]
        exact False.elim <|
          (mem_familyGraph_terminals_of_mem_terminalSet hxterm).2
            ⟨y, hxyLimit⟩
  · have hxlimitVertex : x ∈ (C.eventualRelationLimit H).vertexSet := by
      rw [C.eventualRelationLimit_vertexSet H]
      exact C.stage_vertices_subset_realVertexLimit i
        (by simpa only [realPart_vertices] using hxi)
    obtain ⟨y, hxyLimit⟩ :=
      (C.eventualRelationLimit H)
        |>.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
          hxlimitVertex hxterm
    have hxyEventual : (x, y) ∈ C.eventualEdgeLimit := by
      change (x, y) ∈ (C.eventualRelationLimit H).edgeSet at hxyLimit
      rwa [C.eventualRelationLimit_edgeSet H] at hxyLimit
    obtain ⟨j₀, hj₀⟩ := (WarpLimits.mem_setLiminf _ _).1 hxyEventual
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
        (C.realPart_extends_eventualRelationLimit H j) hcompleted

/-- A sink of the eventual full relation is either already a full terminal
at every stage where it occurs, or belongs to the completion target `B`. -/
theorem eventualRelationSink_mem_B_or_stage_terminal
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) {x : V}
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
            (realLinksTo_of_mem_completedRealVertices hxcompleted)) hxrealterm

/-- Terminal popularity for the intermediate limit is inherited from a
stage terminal unless the sink has already reached `B`. -/
theorem eventualRelationLimit_terminalBoundary
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T) :
    {x | x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.eventualEdgeLimit} ⊆
        {x | IsPopular Gamma Y persistent kappa x} ∪ T := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx.1
  rcases C.eventualRelationSink_mem_B_or_stage_terminal H hx i
      (by simpa only [realPart_vertices] using hxi) with hxB | hxterm
  · exact hB hxB
  · exact (C.isBlueprint i).terminals_popular hxterm

/-- Stability of the intermediate limit follows from stage stability, with
the only extra case being a sink already completed at `B`. -/
theorem eventualRelationLimit_stableBoundary
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (hstableB : B ∩ T ⊆ persistent) :
    {x | x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.eventualEdgeLimit} ∩ T ⊆ persistent := by
  rintro x ⟨hx, hxT⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx.1
  rcases C.eventualRelationSink_mem_B_or_stage_terminal H hx i
      (by simpa only [realPart_vertices] using hxi) with hxB | hxterm
  · exact hstableB ⟨hxB, hxT⟩
  · exact (C.stable i) ⟨hxterm, hxT⟩

/-- The two nonautomatic bounds for a proper relation limit.  The cardinal
field is normally discharged from the number of earlier stages; the ray
field is the genuinely infinitary 9.33 input. -/
structure EventualRelationLimitBoundary
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop where
  card_vertices : #C.realVertexLimit ≤ kappa
  every_relation_ray_strong :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ C.eventualEdgeLimit → (strongEdgeIndices r).Infinite

/-- All six linkage-blueprint conditions for the proper limit.  Roof and
closure pass pointwise from the stage containing a vertex; source coverage
uses full predecessor preservation; terminal popularity uses the
terminal-or-completed dichotomy above. -/
theorem eventualRelationLimit_isLinkageBlueprint
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (hYwarp : Gamma.IsWarp Y)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (D : C.EventualRelationLimitBoundary) :
    (C.eventualRelationLimit H).IsLinkageBlueprint T Z persistent := by
  let O := C.eventualRelationLimitCore H
  have hOE : O.edge = C.eventualEdgeLimit :=
    (C.eventualRelationLimitCore_spec H).1
  have hOC : O.carrier = C.realVertexLimit :=
    (C.eventualRelationLimitCore_spec H).2
  refine
    { vertices_roofed := ?_
      covers_source := ?_
      vertices_closed := ?_
      card_paths := ?_
      infinitely_many_strong := ?_
      terminals_popular := ?_ }
  · intro x hx
    rw [C.eventualRelationLimit_vertexSet H] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact (C.isBlueprint i).vertices_roofed (by simpa using hxi)
  · rw [eventualRelationLimit, orientationBlueprint_initialSet_eq_no_incoming,
      retainedReferenceInitials, orientationBlueprint_vertexSet, hOC, hOE]
    exact C.eventualRelationLimit_covers_source H hYwarp
  · intro x hx
    rw [C.eventualRelationLimit_vertexSet H] at hx
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
    exact Set.mem_iUnion.2 ⟨(Sum.inr r :
      DirectedPath.Path (imaginaryGraph Gamma Y kappa)),
        Set.mem_iUnion.2 ⟨hr, he⟩⟩
  · rw [eventualRelationLimit,
      orientationBlueprint_terminalSet_eq_no_outgoing, hOC, hOE]
    exact C.eventualRelationLimit_terminalBoundary H hB

/-- The proper limit is stable under the natural compatibility condition on
already completed target vertices. -/
theorem eventualRelationLimit_stable
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (hstableB : B ∩ T ⊆ persistent) :
    (C.eventualRelationLimit H).Stable T persistent := by
  rw [Stable, eventualRelationLimit,
    orientationBlueprint_terminalSet_eq_no_outgoing,
    (C.eventualRelationLimitCore_spec H).2,
    (C.eventualRelationLimitCore_spec H).1]
  exact C.eventualRelationLimit_stableBoundary H hstableB

/-- Every stage is a real extension below the proper limit.  This is the
complete (9.32) conclusion, including common imaginary edges and common
terminals. -/
theorem realExtends_eventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (i : I) :
    (C.stage i).RealExtends (C.eventualRelationLimit H) B :=
  ⟨C.realPart_extends_eventualRelationLimit H i,
    C.accounted_eventualRelationLimit H i⟩

/-- Full predecessor preservation also passes from every stage to the proper
limit, so the transfinite recursion can continue after this limit stage. -/
theorem noNewPredecessorsTo_eventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (i : I) :
    (C.stage i).NoNewPredecessorsTo (C.eventualRelationLimit H) := by
  intro x y hxi hyx
  change (y, x) ∈ (C.eventualRelationLimit H).edgeSet at hyx
  rw [C.eventualRelationLimit_edgeSet H] at hyx
  obtain ⟨j, hj⟩ := (WarpLimits.mem_setLiminf _ _).1 hyx
  rcases le_total i j with hij | hji
  · exact H.of_le hij hxi (hj j le_rfl)
  · exact hj i hji

/-- Dedicated proper-limit compiler for Assertion 9.33. -/
theorem stableLimitConclusion_eventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) (hYwarp : Gamma.IsWarp Y)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T)
    (hstableB : B ∩ T ⊆ persistent)
    (D : C.EventualRelationLimitBoundary) :
    StableLimitConclusion C.stage (C.eventualRelationLimit H)
      T Z persistent B :=
  ⟨C.eventualRelationLimit_isLinkageBlueprint H hYwarp hB D,
    C.eventualRelationLimit_stable H hstableB,
    C.realExtends_eventualRelationLimit H⟩

end RealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599
