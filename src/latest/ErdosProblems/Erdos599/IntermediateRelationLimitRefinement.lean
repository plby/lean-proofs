/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IntermediateRelationLimitCompatibility

/-!
# Predecessor refinement at intermediate limits

Full predecessor preservation is too strong for a weak imaginary-edge
replacement: an old edge `u → x` may be replaced by a finite real path
ending in a new edge `y → x`.  The relation below records precisely this
allowed refinement.  It is reflexive and transitive under ordinary carrier
inclusion and monotonicity of real edges.

For a chain satisfying predecessor refinement, a reverse ray in the
eventual full relation is impossible.  Fix a stage containing its first
vertex and follow that vertex back to the root of its stage path.  At each
old predecessor step, a later incoming edge is either the same old edge or
the end of a finite real path anchored at that old predecessor.  The real
path persists forever, and predecessor uniqueness forces the alleged
reverse ray to traverse it backwards.  Induction along the finite old root
prefix reaches an old root, which cannot acquire an incoming edge.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- `U` refines every incoming edge at an old vertex either by retaining
the old edge or by replacing an old incoming edge with a finite real path
having the same head. -/
def PredecessorRefines
    (W U : LinkageBlueprint Gamma Y kappa) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ W.vertexSet → (y, x) ∈ U.edgeSet →
    (y, x) ∈ W.edgeSet ∨
      ∃ (z : V) (p : DirectedPath.FinitePath Gamma.graph),
        (z, x) ∈ W.edgeSet ∧ p.start = z ∧ p.finish = x ∧
          p.edgeSet ⊆ U.realPart.edges

@[refl] theorem PredecessorRefines.refl
    (W : LinkageBlueprint Gamma Y kappa) : W.PredecessorRefines W := by
  intro x y _ hxy
  exact Or.inl hxy

/-- The legacy full predecessor condition implies refinement by always
taking the retained-edge alternative. -/
theorem NoNewPredecessorsTo.predecessorRefines
    {W U : LinkageBlueprint Gamma Y kappa}
    (h : W.NoNewPredecessorsTo U) : W.PredecessorRefines U := by
  intro x y hx hxy
  exact Or.inl (h hx hxy)

/-- Predecessor refinement composes.  If the second refinement is anchored
at a first-stage-new edge, the first refinement's real path already gives
the required certificate and persists into the third stage. -/
theorem PredecessorRefines.trans
    {W U R : LinkageBlueprint Gamma Y kappa}
    (hWU : W.PredecessorRefines U)
    (hUR : U.PredecessorRefines R)
    (hvertices : W.vertexSet ⊆ U.vertexSet)
    (hreal : U.realPart.edges ⊆ R.realPart.edges) :
    W.PredecessorRefines R := by
  intro x y hxW hyxR
  rcases hUR (hvertices hxW) hyxR with hyxU | hrefUR
  · rcases hWU hxW hyxU with hyxW | hrefWU
    · exact Or.inl hyxW
    · rcases hrefWU with ⟨z, p, hzxW, hpstart, hpfinish, hpU⟩
      exact Or.inr ⟨z, p, hzxW, hpstart, hpfinish, hpU.trans hreal⟩
  · rcases hrefUR with ⟨z, p, hzxU, hpstart, hpfinish, hpR⟩
    rcases hWU hxW hzxU with hzxW | hrefWU
    · exact Or.inr ⟨z, p, hzxW, hpstart, hpfinish, hpR⟩
    · rcases hrefWU with ⟨u, q, huxW, hqstart, hqfinish, hqU⟩
      exact Or.inr ⟨u, q, huxW, hqstart, hqfinish, hqU.trans hreal⟩

namespace RealExtensionChain

variable {T Z persistent B : Set V}
variable {I : Type v} [LinearOrder I] [Nonempty I]

/-- Chainwise predecessor refinement between every two comparable stages. -/
structure PredecessorRefinement
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop where
  of_le : ∀ ⦃i j : I⦄, i ≤ j →
    (C.stage i).PredecessorRefines (C.stage j)

/-- Convert the older stronger chain invariant to predecessor refinement. -/
def PredecessorRefinement.ofNoNewPredecessors
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewPredecessors) : C.PredecessorRefinement where
  of_le := by
    intro i j hij
    exact NoNewPredecessorsTo.predecessorRefines (H.of_le hij)

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

/-- Every point of a finite path or ray has a finite prefix from the path's
initial vertex. -/
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

/-- Every stage vertex is reached from a stage initial vertex through the
stage edge relation. -/
private theorem exists_initial_reflTransGen
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
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

/-- A finite real path ending at a reverse-ray vertex must coincide with a
finite reverse-ray segment when traversed backwards. -/
private theorem walk_start_eq_eventual_reverseRay
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
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
      have hreverse := hR (n + q.length)
      obtain ⟨i, hi⟩ := (WarpLimits.mem_setLiminf _ _).1 hreverse
      obtain ⟨k, hjk, hik⟩ := exists_ge_ge j i
      have hacj : (a, c) ∈ (C.stage j).realPart.edges := by
        apply hp
        simp [DirectedPath.Walk.edgeSet_cons]
      have hack : (a, c) ∈ (C.stage k).edgeSet :=
        (C.stage_edges_mono hjk hacj).1
      have hrk :
          (R.vertex (n + q.length + 1), R.vertex (n + q.length)) ∈
            (C.stage k).edgeSet := by
        simpa only [Nat.add_assoc] using hi k hik
      change (a, c) ∈
        Alternating.familyEdges
          (Γ := imaginaryWeb Gamma Y kappa) (C.stage k).paths at hack
      change (R.vertex (n + q.length + 1),
        R.vertex (n + q.length)) ∈
          Alternating.familyEdges
            (Γ := imaginaryWeb Gamma Y kappa) (C.stage k).paths at hrk
      have ha : a = R.vertex (n + q.length + 1) := by
        apply Alternating.IsWarp.familyEdges_leftUnique
          (C.stage k).isWarp hack
        simpa only [hc] using hrk
      simpa only [DirectedPath.Walk.length, Nat.add_assoc] using ha

/-- Real predecessor refinement rules out a reverse ray in the eventual
full-edge relation, without forbidding finite subdivision of old imaginary
edges. -/
theorem eventualEdgeLimit_not_containsReverseDirectedRay_of_refinement
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.PredecessorRefinement) :
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
    no_incoming_edge_of_mem_initialSet (C.stage i) haInitial
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
        have hr := hR n
        obtain ⟨j₀, hj₀⟩ := (WarpLimits.mem_setLiminf _ _).1 hr
        obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
        have hrj : (R.vertex (n + 1), a) ∈ (C.stage j).edgeSet := by
          simpa only [han] using hj₀ j hj₀j
        rcases H.of_le hij hrootVertex hrj with hold | href
        · exact hrootNoIncoming ⟨R.vertex (n + 1), hold⟩
        · rcases href with ⟨z, p, hza, _hpstart, _hpfinish, _hpreal⟩
          exact hrootNoIncoming ⟨z, hza⟩
    | @tail u x hau hux ih =>
        intro n hxn
        have hr := hR n
        obtain ⟨j₀, hj₀⟩ := (WarpLimits.mem_setLiminf _ _).1 hr
        obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
        have hrj : (R.vertex (n + 1), x) ∈ (C.stage j).edgeSet := by
          simpa only [hxn] using hj₀ j hj₀j
        have hxVertex : x ∈ (C.stage i).vertexSet :=
          (Alternating.familyEdges_subset_vertexSet_prod
            (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hux).2
        rcases H.of_le hij hxVertex hrj with hold | href
        · have hyu : R.vertex (n + 1) = u :=
            Alternating.IsWarp.familyEdges_leftUnique
              (C.stage i).isWarp hold hux
          exact ih (n + 1) hyu.symm
        · rcases href with
            ⟨z, p, hzx, hpstart, hpfinish, hpReal⟩
          have hzu : z = u :=
            Alternating.IsWarp.familyEdges_leftUnique
              (C.stage i).isWarp hzx hux
          have hpfinishR : p.finish = R.vertex n := hpfinish.trans hxn
          have hpstartR : p.start =
              R.vertex (n + p.walk.length) :=
            C.walk_start_eq_eventual_reverseRay p.walk j R hR n
              hpfinishR hpReal
          have hpstartU : p.start = u := hpstart.trans hzu
          exact ih (n + p.walk.length)
            (hpstartU.symm.trans hpstartR)
  exact himpossible hreach 0 rfl

/-- The real-edge union is a subrelation of the eventual full relation, so
the same refinement invariant excludes its reverse rays. -/
theorem realEdgeLimit_not_containsReverseDirectedRay_of_refinement
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.PredecessorRefinement) :
    ¬ Alternating.ContainsReverseDirectedRay C.realEdgeLimit := by
  rintro ⟨R, hR⟩
  exact C.eventualEdgeLimit_not_containsReverseDirectedRay_of_refinement H
    ⟨R, fun n ↦ C.realEdgeLimit_subset_eventualEdgeLimit (hR n)⟩

/-- Predecessor refinement supplies the exact direct compatibility record
used by the source-faithful proper-limit compiler. -/
def EventualRelationLimitCompatibility.ofPredecessorRefinement
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.PredecessorRefinement) :
    C.EventualRelationLimitCompatibility where
  no_reverse_ray :=
    C.eventualEdgeLimit_not_containsReverseDirectedRay_of_refinement H

/-- It also supplies the honest final all-real relation core. -/
def relationLimitCore_of_predecessorRefinement
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.PredecessorRefinement) : C.RelationLimitCore where
  no_directed_cycle := C.realEdgeLimit_not_containsDirectedCycle
  no_reverse_ray :=
    C.realEdgeLimit_not_containsReverseDirectedRay_of_refinement H

/-- Refinement from every old stage passes to the compatible proper limit.
This is the recursion-closing replacement for propagating the false full
predecessor-preservation property. -/
theorem predecessorRefines_compatibleEventualRelationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.PredecessorRefinement)
    (K : C.EventualRelationLimitCompatibility) (i : I) :
    (C.stage i).PredecessorRefines
      (C.compatibleEventualRelationLimit K) := by
  intro x y hx hyx
  have hyxEventual : (y, x) ∈ C.eventualEdgeLimit := by
    rwa [← C.compatibleEventualRelationLimit_edgeSet K]
  obtain ⟨j₀, hj₀⟩ :=
    (WarpLimits.mem_setLiminf _ _).1 hyxEventual
  obtain ⟨j, hij, hj₀j⟩ := exists_ge_ge i j₀
  rcases H.of_le hij hx (hj₀ j hj₀j) with hold | href
  · exact Or.inl hold
  · rcases href with ⟨z, p, hzx, hpstart, hpfinish, hpReal⟩
    exact Or.inr ⟨z, p, hzx, hpstart, hpfinish,
      hpReal.trans
        (C.realPart_extends_compatibleEventualRelationLimit K j).2⟩

end RealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599
