/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IntermediateRelationLimitRefinement

/-!
# Relation limits for stages with varying slice parameters

The half-way recursion changes its terminal slice and closure set between
stages.  Consequently its relation-level limit arguments must not be routed
through a `RealExtensionChain` with fictitious fixed `T`, `Z`, or
`persistent` parameters.

`IndexedRealExtensionChain` retains exactly the slice-independent data:
stage linkage blueprints, the actual real-extension relation with fixed
completion target `B`, and real predecessor refinement.  This is enough to
construct both the eventual-full proper-limit relation and the all-real
final relation, prove their exact carrier and edge identities, exclude
reverse rays, and transport `RealExtends` and predecessor refinement.

No `IsLinkageBlueprint`, stability, roof, closure, terminal, or source
boundary is asserted here.  Those fields must be supplied at the scheduler's
actual limit slice.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- Slice-independent relation data for a linearly ordered family of
blueprints. -/
structure IndexedRealExtensionChain (I : Type v) [LinearOrder I]
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (B : Set V) where
  stage : I → LinkageBlueprint Gamma Y kappa
  realExtends : ∀ ⦃i j : I⦄, i ≤ j →
    (stage i).RealExtends (stage j) B
  predecessorRefines : ∀ ⦃i j : I⦄, i ≤ j →
    (stage i).PredecessorRefines (stage j)

namespace IndexedRealExtensionChain

variable {B : Set V}
variable {I : Type v} [LinearOrder I] [Nonempty I]

def realVertexLimit
    (C : IndexedRealExtensionChain I Gamma Y kappa B) : Set V :=
  ⋃ i, (C.stage i).realPart.vertices

def realEdgeLimit
    (C : IndexedRealExtensionChain I Gamma Y kappa B) : Set (V × V) :=
  ⋃ i, (C.stage i).realPart.edges

def eventualEdgeLimit
    (C : IndexedRealExtensionChain I Gamma Y kappa B) : Set (V × V) :=
  WarpLimits.setLiminf fun i ↦ (C.stage i).edgeSet

theorem stage_vertices_mono
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    {i j : I} (hij : i ≤ j) :
    (C.stage i).realPart.vertices ⊆
      (C.stage j).realPart.vertices :=
  (C.realExtends hij).realPart_extends.1

theorem stage_edges_mono
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    {i j : I} (hij : i ≤ j) :
    (C.stage i).realPart.edges ⊆
      (C.stage j).realPart.edges :=
  (C.realExtends hij).realEdges_mono

theorem stage_vertices_subset_realVertexLimit
    (C : IndexedRealExtensionChain I Gamma Y kappa B) (i : I) :
    (C.stage i).realPart.vertices ⊆ C.realVertexLimit :=
  Set.subset_iUnion (fun j ↦ (C.stage j).realPart.vertices) i

theorem stage_edges_subset_realEdgeLimit
    (C : IndexedRealExtensionChain I Gamma Y kappa B) (i : I) :
    (C.stage i).realPart.edges ⊆ C.realEdgeLimit :=
  Set.subset_iUnion (fun j ↦ (C.stage j).realPart.edges) i

theorem realEdgeLimit_subset_eventualEdgeLimit
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.realEdgeLimit ⊆ C.eventualEdgeLimit := by
  intro e he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  apply (WarpLimits.mem_setLiminf _ _).2
  exact ⟨i, fun j hij ↦ (C.stage_edges_mono hij hei).1⟩

theorem eventualEdgeLimit_in_graph
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.eventualEdgeLimit ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 he
  have hei : e ∈ (C.stage i).edgeSet := hi i le_rfl
  simp only [edgeSet, Set.mem_iUnion] at hei
  obtain ⟨p, hp, hep⟩ := hei
  exact p.edgeSet_subset_adj hep

theorem eventualEdgeLimit_endpoints
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
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

theorem eventualEdgeLimit_biUnique
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ C.eventualEdgeLimit) := by
  constructor
  · intro x y z hxz hyz
    obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 hxz
    obtain ⟨j, hj⟩ := (WarpLimits.mem_setLiminf _ _).1 hyz
    rcases exists_ge_ge i j with ⟨m, him, hjm⟩
    exact (Alternating.IsWarp.familyEdges_leftUnique (C.stage m).isWarp)
      (hi m him) (hj m hjm)
  · intro x y z hxy hxz
    obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 hxy
    obtain ⟨j, hj⟩ := (WarpLimits.mem_setLiminf _ _).1 hxz
    rcases exists_ge_ge i j with ⟨m, him, hjm⟩
    exact (Alternating.IsWarp.familyEdges_rightUnique (C.stage m).isWarp)
      (hi m him) (hj m hjm)

theorem eventualEdgeLimit_not_containsDirectedCycle
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
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
  exact blueprint_edgeSet_not_containsDirectedCycle (C.stage j)
    ⟨Q, by
      rintro e ⟨n, rfl⟩
      exact hstageOf n j (hj n)⟩

private theorem walk_reflTransGen_edgeSet
    {D : Digraph V} {a b : V} (p : DirectedPath.Walk D a b) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ p.edgeSet) a b := by
  induction p with
  | nil => exact .refl
  | @cons a c b h p ih =>
      have ih' := Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ p.edgeSet)
        (p := fun x y ↦
          (x, y) ∈ (DirectedPath.Walk.cons h p).edgeSet)
        (by
          intro x y hxy
          simp only [DirectedPath.Walk.edgeSet_cons, Set.mem_union,
            Set.mem_singleton_iff]
          exact Or.inr hxy) c b ih
      exact ih'.head (by simp [DirectedPath.Walk.edgeSet_cons])

private theorem exists_initialFinitePrefix
    (p : Gamma.DPath) {x : V} (hx : x ∈ p.support) :
    ∃ q : DirectedPath.FinitePath Gamma.graph,
      q.start = p.initial ∧ q.finish = x ∧ q.edgeSet ⊆ p.edgeSet := by
  rcases p with p | r
  · let hmeet : p.walk.Meets ({x} : Set V) :=
      ⟨x, hx, Set.mem_singleton x⟩
    let q := p.firstHit ({x} : Set V) hmeet
    refine ⟨q, rfl, ?_, p.firstHit_edgeSet_subset {x} hmeet⟩
    exact Set.mem_singleton_iff.mp (p.firstHit_finish_mem {x} hmeet)
  · obtain ⟨n, rfl⟩ := hx
    let q := Alternating.SwitchingCore.rayPrefixPath r n
    refine ⟨q, rfl, rfl, ?_⟩
    intro e he
    rw [Alternating.SwitchingCore.rayPrefixPath_edgeSet] at he
    obtain ⟨m, _hm, rfl⟩ := he
    exact ⟨m, rfl⟩

private theorem exists_initial_reflTransGen
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (i : I) {x : V} (hx : x ∈ (C.stage i).vertexSet) :
    ∃ a, a ∈ (C.stage i).initialSet ∧
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ (C.stage i).edgeSet) a x := by
  obtain ⟨p, hp, hxp⟩ := hx
  obtain ⟨q, hqstart, hqfinish, hqedges⟩ :=
    exists_initialFinitePrefix p hxp
  refine ⟨p.initial, ⟨p, hp, rfl⟩, ?_⟩
  have hreach := walk_reflTransGen_edgeSet q.walk
  have hreach' := Relation.ReflTransGen.mono
    (r := fun u v ↦ (u, v) ∈ q.walk.edgeSet)
    (p := fun u v ↦ (u, v) ∈ (C.stage i).edgeSet)
    (by
      intro u v huv
      exact Set.mem_iUnion.2
        ⟨p, Set.mem_iUnion.2 ⟨hp, hqedges huv⟩⟩)
    q.start q.finish hreach
  simpa only [hqstart, hqfinish] using hreach'

private theorem walk_start_eq_eventual_reverseRay
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    {a b : V} (p : DirectedPath.Walk Gamma.graph a b) (j : I)
    (R : Alternating.DirectedRay V)
    (hR : ∀ n, (R.vertex (n + 1), R.vertex n) ∈ C.eventualEdgeLimit)
    (n : ℕ) (hfinish : b = R.vertex n)
    (hp : p.edgeSet ⊆ (C.stage j).realPart.edges) :
    a = R.vertex (n + p.length) := by
  induction p generalizing n with
  | nil => simpa using hfinish
  | @cons a c b hac q ih =>
      have hq : q.edgeSet ⊆ (C.stage j).realPart.edges := by
        intro e he
        apply hp
        simp only [DirectedPath.Walk.edgeSet_cons, Set.mem_union]
        exact Or.inr he
      have hc : c = R.vertex (n + q.length) := ih n hfinish hq
      obtain ⟨i, hi⟩ :=
        (WarpLimits.mem_setLiminf _ _).1 (hR (n + q.length))
      obtain ⟨m, hjm, him⟩ := exists_ge_ge j i
      have hacj : (a, c) ∈ (C.stage j).realPart.edges := by
        apply hp
        simp [DirectedPath.Walk.edgeSet_cons]
      have hacm : (a, c) ∈ (C.stage m).edgeSet :=
        (C.stage_edges_mono hjm hacj).1
      have hrm :
          (R.vertex (n + q.length + 1), R.vertex (n + q.length)) ∈
            (C.stage m).edgeSet := by
        simpa only [Nat.add_assoc] using hi m him
      change (a, c) ∈ Alternating.familyEdges
        (Γ := imaginaryWeb Gamma Y kappa) (C.stage m).paths at hacm
      change (R.vertex (n + q.length + 1),
        R.vertex (n + q.length)) ∈ Alternating.familyEdges
          (Γ := imaginaryWeb Gamma Y kappa) (C.stage m).paths at hrm
      have ha : a = R.vertex (n + q.length + 1) := by
        apply Alternating.IsWarp.familyEdges_leftUnique
          (C.stage m).isWarp hacm
        simpa only [hc] using hrm
      simpa only [DirectedPath.Walk.length, Nat.add_assoc] using ha

theorem eventualEdgeLimit_not_containsReverseDirectedRay
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    ¬ Alternating.ContainsReverseDirectedRay C.eventualEdgeLimit := by
  rintro ⟨R, hR⟩
  obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 (hR 0)
  have hR0i : (R.vertex 1, R.vertex 0) ∈ (C.stage i).edgeSet :=
    hi i le_rfl
  have hR0vertex : R.vertex 0 ∈ (C.stage i).vertexSet :=
    (Alternating.familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hR0i).2
  obtain ⟨a, haInitial, hreach⟩ :=
    C.exists_initial_reflTransGen i hR0vertex
  have hrootNoIncoming : ¬ ∃ y, (y, a) ∈ (C.stage i).edgeSet :=
    RealExtensionChain.no_incoming_edge_of_mem_initialSet
      (C.stage i) haInitial
  have hrootVertex : a ∈ (C.stage i).vertexSet := by
    rcases haInitial with ⟨p, hp, rfl⟩
    exact ⟨p, hp, p.initial_mem_support⟩
  have himpossible : ∀ {x : V},
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ (C.stage i).edgeSet) a x →
      ∀ n, x = R.vertex n → False := by
    intro x hax
    induction hax with
    | refl =>
        intro n han
        obtain ⟨j₀, hj₀⟩ :=
          (WarpLimits.mem_setLiminf _ _).1 (hR n)
        obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
        have hrj : (R.vertex (n + 1), a) ∈ (C.stage j).edgeSet := by
          simpa only [han] using hj₀ j hj₀j
        rcases C.predecessorRefines hij hrootVertex hrj with hold | href
        · exact hrootNoIncoming ⟨R.vertex (n + 1), hold⟩
        · rcases href with ⟨z, p, hza, _hs, _hf, _hr⟩
          exact hrootNoIncoming ⟨z, hza⟩
    | @tail u x hau hux ih =>
        intro n hxn
        obtain ⟨j₀, hj₀⟩ :=
          (WarpLimits.mem_setLiminf _ _).1 (hR n)
        obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
        have hrj : (R.vertex (n + 1), x) ∈ (C.stage j).edgeSet := by
          simpa only [hxn] using hj₀ j hj₀j
        have hxVertex : x ∈ (C.stage i).vertexSet :=
          (Alternating.familyEdges_subset_vertexSet_prod
            (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hux).2
        rcases C.predecessorRefines hij hxVertex hrj with hold | href
        · have hyu : R.vertex (n + 1) = u :=
            Alternating.IsWarp.familyEdges_leftUnique
              (C.stage i).isWarp hold hux
          exact ih (n + 1) hyu.symm
        · rcases href with ⟨z, p, hzx, hpstart, hpfinish, hpReal⟩
          have hzu : z = u :=
            Alternating.IsWarp.familyEdges_leftUnique
              (C.stage i).isWarp hzx hux
          have hpstartR : p.start =
              R.vertex (n + p.walk.length) :=
            C.walk_start_eq_eventual_reverseRay p.walk j R hR n
              (hpfinish.trans hxn) hpReal
          exact ih (n + p.walk.length)
            ((hpstart.trans hzu).symm.trans hpstartR)
  exact himpossible hreach 0 rfl

/-! ### Eventual-full proper relation -/

noncomputable def eventualRelationOrientation
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    Alternating.RelationDecomposition.ForwardOrientation
      (imaginaryGraph Gamma Y kappa) :=
  Classical.choose (exists_forwardOrientation_exact
    C.eventualEdgeLimit C.realVertexLimit C.eventualEdgeLimit_in_graph
      C.eventualEdgeLimit_endpoints C.eventualEdgeLimit_biUnique
      C.eventualEdgeLimit_not_containsDirectedCycle
      C.eventualEdgeLimit_not_containsReverseDirectedRay)

theorem eventualRelationOrientation_spec
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.eventualRelationOrientation.edge = C.eventualEdgeLimit ∧
      C.eventualRelationOrientation.carrier = C.realVertexLimit :=
  Classical.choose_spec (exists_forwardOrientation_exact
    C.eventualEdgeLimit C.realVertexLimit C.eventualEdgeLimit_in_graph
      C.eventualEdgeLimit_endpoints C.eventualEdgeLimit_biUnique
      C.eventualEdgeLimit_not_containsDirectedCycle
      C.eventualEdgeLimit_not_containsReverseDirectedRay)

noncomputable def eventualRelationBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    LinkageBlueprint Gamma Y kappa :=
  orientationBlueprint C.eventualRelationOrientation

@[simp] theorem eventualRelationBlueprint_vertexSet
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.eventualRelationBlueprint.vertexSet = C.realVertexLimit := by
  rw [eventualRelationBlueprint, orientationBlueprint_vertexSet,
    C.eventualRelationOrientation_spec.2]

@[simp] theorem eventualRelationBlueprint_edgeSet
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.eventualRelationBlueprint.edgeSet = C.eventualEdgeLimit := by
  rw [eventualRelationBlueprint, orientationBlueprint_edgeSet,
    C.eventualRelationOrientation_spec.1]

@[simp] theorem eventualRelationBlueprint_realPart_edges
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.eventualRelationBlueprint.realPart.edges = C.realEdgeLimit := by
  rw [realPart_edges, C.eventualRelationBlueprint_edgeSet]
  apply Set.Subset.antisymm
  · rintro e ⟨he, hereal⟩
    obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 he
    exact Set.mem_iUnion.2 ⟨i, hi i le_rfl, hereal⟩
  · intro e he
    exact ⟨C.realEdgeLimit_subset_eventualEdgeLimit he, by
      obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
      exact hei.2⟩

theorem realPart_extends_eventualRelationBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B) (i : I) :
    (C.stage i).realPart.Extends C.eventualRelationBlueprint.realPart := by
  constructor
  · change (C.stage i).vertexSet ⊆ C.eventualRelationBlueprint.vertexSet
    rw [C.eventualRelationBlueprint_vertexSet]
    exact C.stage_vertices_subset_realVertexLimit i
  · rw [C.eventualRelationBlueprint_realPart_edges]
    exact C.stage_edges_subset_realEdgeLimit i

theorem accounted_eventualRelationBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B) (i : I) :
    (C.stage i).vertexSet ⊆
      (C.eventualRelationBlueprint.terminalSet ∩
          (C.stage i).terminalSet) ∪
        {x | ∃ y, (x, y) ∈
          (C.stage i).familyGraph.edges ∩
            C.eventualRelationBlueprint.familyGraph.edges} ∪
          C.eventualRelationBlueprint.completedRealVertices B := by
  classical
  intro x hxi
  by_cases hxterm : x ∈ C.eventualRelationBlueprint.terminalSet
  · by_cases hxiterm : x ∈ (C.stage i).terminalSet
    · exact Or.inl (Or.inl ⟨hxterm, hxiterm⟩)
    · by_cases hcompleted :
        ∃ j, x ∈ (C.stage j).completedRealVertices B
      · obtain ⟨j, hxcompleted⟩ := hcompleted
        exact Or.inr <| completedRealVertices_mono
          (C.realPart_extends_eventualRelationBlueprint j) hxcompleted
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
        have hxyLimit : (x, y) ∈ C.eventualRelationBlueprint.edgeSet := by
          rwa [C.eventualRelationBlueprint_edgeSet]
        exact False.elim <|
          (mem_familyGraph_terminals_of_mem_terminalSet hxterm).2
            ⟨y, hxyLimit⟩
  · have hxlimitVertex : x ∈ C.eventualRelationBlueprint.vertexSet := by
      rw [C.eventualRelationBlueprint_vertexSet]
      exact C.stage_vertices_subset_realVertexLimit i
        (by simpa only [realPart_vertices] using hxi)
    obtain ⟨y, hxyLimit⟩ :=
      C.eventualRelationBlueprint
        |>.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
          hxlimitVertex hxterm
    have hxyEventual : (x, y) ∈ C.eventualEdgeLimit := by
      change (x, y) ∈ C.eventualRelationBlueprint.edgeSet at hxyLimit
      rwa [C.eventualRelationBlueprint_edgeSet] at hxyLimit
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
        (C.realPart_extends_eventualRelationBlueprint j) hcompleted

theorem realExtends_eventualRelationBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B) (i : I) :
    (C.stage i).RealExtends C.eventualRelationBlueprint B :=
  ⟨C.realPart_extends_eventualRelationBlueprint i,
    C.accounted_eventualRelationBlueprint i⟩

theorem predecessorRefines_eventualRelationBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B) (i : I) :
    (C.stage i).PredecessorRefines C.eventualRelationBlueprint := by
  intro x y hx hyx
  have hyxEventual : (y, x) ∈ C.eventualEdgeLimit := by
    rwa [← C.eventualRelationBlueprint_edgeSet]
  obtain ⟨j₀, hj₀⟩ := (WarpLimits.mem_setLiminf _ _).1 hyxEventual
  obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
  rcases C.predecessorRefines hij hx (hj₀ j hj₀j) with hold | href
  · exact Or.inl hold
  · rcases href with ⟨z, p, hzx, hs, hf, hp⟩
    exact Or.inr ⟨z, p, hzx, hs, hf,
      hp.trans (C.realPart_extends_eventualRelationBlueprint j).2⟩

/-! ### All-real final relation -/

theorem realEdgeLimit_in_graph
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.realEdgeLimit ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  exact Or.inl hei.2

theorem realEdgeLimit_endpoints
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    ∀ e ∈ C.realEdgeLimit,
      e.1 ∈ C.realVertexLimit ∧ e.2 ∈ C.realVertexLimit := by
  intro e he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  have hends :
      e.1 ∈ (C.stage i).vertexSet ∧ e.2 ∈ (C.stage i).vertexSet :=
    Alternating.familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hei.1
  exact ⟨C.stage_vertices_subset_realVertexLimit i
      (by simpa only [realPart_vertices] using hends.1),
    C.stage_vertices_subset_realVertexLimit i
      (by simpa only [realPart_vertices] using hends.2)⟩

theorem realEdgeLimit_biUnique
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ C.realEdgeLimit) := by
  constructor
  · intro x y z hxz hyz
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxz
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.1 hyz
    rcases le_total i j with hij | hji
    · exact (Alternating.IsWarp.familyEdges_leftUnique (C.stage j).isWarp)
        (C.stage_edges_mono hij hxi).1 hyj.1
    · exact (Alternating.IsWarp.familyEdges_leftUnique (C.stage i).isWarp)
        hxi.1 (C.stage_edges_mono hji hyj).1
  · intro x y z hxy hxz
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.1 hxy
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hxz
    rcases le_total i j with hij | hji
    · exact (Alternating.IsWarp.familyEdges_rightUnique (C.stage j).isWarp)
        (C.stage_edges_mono hij hyi).1 hzj.1
    · exact (Alternating.IsWarp.familyEdges_rightUnique (C.stage i).isWarp)
        hyi.1 (C.stage_edges_mono hji hzj).1

theorem realEdgeLimit_not_containsDirectedCycle
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    ¬ Alternating.ContainsDirectedCycle C.realEdgeLimit := by
  rintro ⟨Q, hQ⟩
  let stageOf : Fin Q.length → I := fun n ↦
    Classical.choose (Set.mem_iUnion.1 (hQ ⟨n, rfl⟩))
  have hstageOf (n : Fin Q.length) :
      (Q.vertex n, Q.vertex (Q.next n)) ∈
        (C.stage (stageOf n)).realPart.edges :=
    Classical.choose_spec (Set.mem_iUnion.1 (hQ ⟨n, rfl⟩))
  obtain ⟨j, hj⟩ := Finite.exists_le stageOf
  exact blueprint_edgeSet_not_containsDirectedCycle (C.stage j)
    ⟨Q, by
      rintro e ⟨n, rfl⟩
      exact (C.stage_edges_mono (hj n) (hstageOf n)).1⟩

theorem realEdgeLimit_not_containsReverseDirectedRay
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    ¬ Alternating.ContainsReverseDirectedRay C.realEdgeLimit := by
  rintro ⟨R, hR⟩
  exact C.eventualEdgeLimit_not_containsReverseDirectedRay
    ⟨R, fun n ↦ C.realEdgeLimit_subset_eventualEdgeLimit (hR n)⟩

noncomputable def realRelationOrientation
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    Alternating.RelationDecomposition.ForwardOrientation
      (imaginaryGraph Gamma Y kappa) :=
  Classical.choose (exists_forwardOrientation_exact
    C.realEdgeLimit C.realVertexLimit C.realEdgeLimit_in_graph
      C.realEdgeLimit_endpoints C.realEdgeLimit_biUnique
      C.realEdgeLimit_not_containsDirectedCycle
      C.realEdgeLimit_not_containsReverseDirectedRay)

theorem realRelationOrientation_spec
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.realRelationOrientation.edge = C.realEdgeLimit ∧
      C.realRelationOrientation.carrier = C.realVertexLimit :=
  Classical.choose_spec (exists_forwardOrientation_exact
    C.realEdgeLimit C.realVertexLimit C.realEdgeLimit_in_graph
      C.realEdgeLimit_endpoints C.realEdgeLimit_biUnique
      C.realEdgeLimit_not_containsDirectedCycle
      C.realEdgeLimit_not_containsReverseDirectedRay)

noncomputable def realRelationBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    LinkageBlueprint Gamma Y kappa :=
  orientationBlueprint C.realRelationOrientation

@[simp] theorem realRelationBlueprint_vertexSet
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.realRelationBlueprint.vertexSet = C.realVertexLimit := by
  rw [realRelationBlueprint, orientationBlueprint_vertexSet,
    C.realRelationOrientation_spec.2]

@[simp] theorem realRelationBlueprint_edgeSet
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.realRelationBlueprint.edgeSet = C.realEdgeLimit := by
  rw [realRelationBlueprint, orientationBlueprint_edgeSet,
    C.realRelationOrientation_spec.1]

@[simp] theorem realRelationBlueprint_realPart_edges
    (C : IndexedRealExtensionChain I Gamma Y kappa B) :
    C.realRelationBlueprint.realPart.edges = C.realEdgeLimit := by
  rw [realPart_edges, C.realRelationBlueprint_edgeSet]
  ext e
  constructor
  · exact fun h ↦ h.1
  · intro he
    refine ⟨he, ?_⟩
    obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
    exact hei.2

theorem realPart_extends_realRelationBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B) (i : I) :
    (C.stage i).realPart.Extends C.realRelationBlueprint.realPart := by
  constructor
  · change (C.stage i).vertexSet ⊆ C.realRelationBlueprint.vertexSet
    rw [C.realRelationBlueprint_vertexSet]
    exact C.stage_vertices_subset_realVertexLimit i
  · rw [C.realRelationBlueprint_realPart_edges]
    exact C.stage_edges_subset_realEdgeLimit i

theorem accounted_realRelationBlueprint_of_eventuallyCompleted
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
      x ∉ (C.stage i).terminalSet →
        ∃ j, x ∈ (C.stage j).completedRealVertices B)
    (i : I) :
    (C.stage i).vertexSet ⊆
      (C.realRelationBlueprint.terminalSet ∩ (C.stage i).terminalSet) ∪
        {x | ∃ y, (x, y) ∈
          (C.stage i).familyGraph.edges ∩
            C.realRelationBlueprint.familyGraph.edges} ∪
          C.realRelationBlueprint.completedRealVertices B := by
  intro x hxi
  by_cases hxterm : x ∈ C.realRelationBlueprint.terminalSet
  · by_cases hxiterm : x ∈ (C.stage i).terminalSet
    · exact Or.inl (Or.inl ⟨hxterm, hxiterm⟩)
    · have hxrealterm : x ∈ (C.stage i).realPart.terminals := by
        refine ⟨by simpa only [realPart_vertices] using hxi, ?_⟩
        rintro ⟨y, hxy⟩
        have hxyLimit :
            (x, y) ∈ C.realRelationBlueprint.edgeSet := by
          rw [C.realRelationBlueprint_edgeSet]
          exact C.stage_edges_subset_realEdgeLimit i hxy
        exact (mem_familyGraph_terminals_of_mem_terminalSet hxterm).2
          ⟨y, hxyLimit⟩
      obtain ⟨j, hxcompleted⟩ :=
        eventuallyCompleted i x hxrealterm hxiterm
      exact Or.inr <| completedRealVertices_mono
        (C.realPart_extends_realRelationBlueprint j) hxcompleted
  · have hxlimitVertex : x ∈ C.realRelationBlueprint.vertexSet := by
      rw [C.realRelationBlueprint_vertexSet]
      exact C.stage_vertices_subset_realVertexLimit i
        (by simpa only [realPart_vertices] using hxi)
    obtain ⟨y, hxyLimit⟩ :=
      C.realRelationBlueprint
        |>.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
          hxlimitVertex hxterm
    have hxyRealLimit : (x, y) ∈ C.realEdgeLimit := by
      change (x, y) ∈ C.realRelationBlueprint.edgeSet at hxyLimit
      rwa [C.realRelationBlueprint_edgeSet] at hxyLimit
    obtain ⟨j, hxyj⟩ := Set.mem_iUnion.1 hxyRealLimit
    rcases le_total i j with hij | hji
    · rcases (C.realExtends hij).2 hxi with hcommon | hcompleted
      · rcases hcommon with hterm | hedge
        · exact False.elim <|
            (mem_familyGraph_terminals_of_mem_terminalSet hterm.1).2
              ⟨y, hxyj.1⟩
        · rcases hedge with ⟨z, hxzi, hxzj⟩
          have hzy : z = y :=
            Alternating.IsWarp.familyEdges_rightUnique
              (C.stage j).isWarp hxzj hxyj.1
          exact Or.inl (Or.inr ⟨y, hzy ▸ hxzi, hxyLimit⟩)
      · exact Or.inr <| completedRealVertices_mono
          (C.realPart_extends_realRelationBlueprint j) hcompleted
    · exact Or.inl (Or.inr ⟨y, (C.stage_edges_mono hji hxyj).1,
        hxyLimit⟩)

theorem realExtends_realRelationBlueprint_of_eventuallyCompleted
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
      x ∉ (C.stage i).terminalSet →
        ∃ j, x ∈ (C.stage j).completedRealVertices B)
    (i : I) :
    (C.stage i).RealExtends C.realRelationBlueprint B :=
  ⟨C.realPart_extends_realRelationBlueprint i,
    C.accounted_realRelationBlueprint_of_eventuallyCompleted
      eventuallyCompleted i⟩

theorem predecessorRefines_realRelationBlueprint
    (C : IndexedRealExtensionChain I Gamma Y kappa B) (i : I) :
    (C.stage i).PredecessorRefines C.realRelationBlueprint := by
  intro x y hx hyx
  have hyxReal : (y, x) ∈ C.realEdgeLimit := by
    rwa [← C.realRelationBlueprint_edgeSet]
  obtain ⟨j, hyxj⟩ := Set.mem_iUnion.1 hyxReal
  rcases le_total i j with hij | hji
  · rcases C.predecessorRefines hij hx hyxj.1 with hold | href
    · exact Or.inl hold
    · rcases href with ⟨z, p, hzx, hs, hf, hp⟩
      exact Or.inr ⟨z, p, hzx, hs, hf,
        hp.trans (C.realPart_extends_realRelationBlueprint j).2⟩
  · exact Or.inl (C.stage_edges_mono hji hyxj).1

end IndexedRealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599
