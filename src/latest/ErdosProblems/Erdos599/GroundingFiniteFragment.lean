/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.RelationComponents
import ErdosProblems.Erdos599.SafeSwitching

/-!
# Deleted-edge fragments of a finite ladder path

For a finite ladder path, deleting an arbitrary set of represented edges
leaves finite weak components.  The residual edge relation is locally
functional because it is a subrelation of one simple directed path.  The
canonical finite component path from `RelationComponents` therefore gives
the maximal deleted-edge fragment through any prescribed support vertex.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFiniteFragment

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

namespace RC

open Alternating.RelationComponents

/-- The endpoints of a finite walk lie in one weak component of every edge
relation containing all of the walk's directed edges. -/
theorem walk_reflTransGen_weakRel_of_edges_subset
    {D : Digraph V} {E : Set (V × V)} {a b : V}
    (w : Walk D a b) (hw : w.edgeSet ⊆ E) :
    Relation.ReflTransGen (WeakRel E) a b := by
  induction w with
  | nil => exact .refl
  | @cons a c b h w ih =>
      have htail : w.edgeSet ⊆ E := by
        intro e he
        apply hw
        exact Set.mem_union_right _ he
      exact (ih htail).head (Or.inl (hw (by simp [Walk.edgeSet])))

end RC

open Alternating.RelationComponents

/-- Every vertex of a finite parent path lies in a canonical maximal
surviving fragment after the represented cut edges are deleted. -/
theorem exists_deletedFragment_through_finite
    (L : Input Gamma I) (C : Set (LV L))
    (p : FinitePath Gamma.graph)
    (hp : (Sum.inl p : Gamma.DPath) ∈ L.ladder.paths)
    {x : V} (hx : x ∈ p.support) :
    ∃ P : L.Fragment,
      P.parent = Sum.inl p ∧
        P ∈ GroundingCut.fragments L C ∧
          x ∈ P.path.support := by
  classical
  let E : Set (V × V) := p.edgeSet \ GroundingCut.CE L C
  let c : Component E := componentMk E x
  have hEparent : E ⊆ p.edgeSet := by
    intro e he
    exact he.1
  have hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
    hEparent.trans p.edgeSet_subset_adj
  have hright : ∀ {a b d : V}, (a, b) ∈ E → (a, d) ∈ E → b = d := by
    intro a b d hab had
    exact (Alternating.FinitePath.edgeSet_biUnique p).2
      (hEparent hab) (hEparent had)
  have hleft : ∀ {a b d : V}, (a, d) ∈ E → (b, d) ∈ E → a = b := by
    intro a b d had hbd
    exact (Alternating.FinitePath.edgeSet_biUnique p).1
      (hEparent had) (hEparent hbd)
  have hc_subset : componentSupport E c ⊆ p.support := by
    rw [show c = componentMk E x from rfl,
      componentSupport_componentMk]
    intro y hxy
    induction hxy with
    | refl => exact hx
    | @tail y z hxy hyz ih =>
        rcases hyz with hyz | hzy
        · exact p.edgeSet_subset_support_prod (hEparent hyz) |>.2
        · exact p.edgeSet_subset_support_prod (hEparent hzy) |>.1
  have hc_finite : (componentSupport E c).Finite :=
    p.support_finite.subset hc_subset
  let q : FinitePath Gamma.graph :=
    componentPath (D := Gamma.graph) E c hc_finite
  have hq_spec : IsComponentPath E c q :=
    (componentPath_spec (D := Gamma.graph) E c hc_finite).1
  have hq_support : q.support = componentSupport E c := by
    exact componentPath_support_eq E hEadj hright hleft c hc_finite
  have hq_parent_support : q.support ⊆ p.support := by
    rw [hq_support]
    exact hc_subset
  have hq_parent_edges : q.edgeSet ⊆ p.edgeSet :=
    hq_spec.1.trans hEparent
  have hq_disjoint : Disjoint q.edgeSet (GroundingCut.CE L C) := by
    rw [Set.disjoint_left]
    intro e heq heC
    exact (hq_spec.1 heq).2 heC
  let P : L.Fragment :=
    { path := Sum.inl q
      parent := Sum.inl p
      parent_mem := hp
      support_subset := hq_parent_support
      edges_subset := hq_parent_edges }
  have hxq : x ∈ q.support := by
    rw [hq_support]
    exact componentMk_mem E x
  refine ⟨P, rfl, ?_, hxq⟩
  refine ⟨hq_disjoint, ?_⟩
  change q.support =
    {y | y ∈ p.support ∧
      GroundingCut.SurvivingConnected L C (Sum.inl p) q.start y}
  ext y
  constructor
  · intro hyq
    have hmeet : q.walk.Meets ({y} : Set V) :=
      ⟨y, hyq, Set.mem_singleton y⟩
    let r : FinitePath Gamma.graph := q.firstHit {y} hmeet
    have hrfinish : r.finish = y := by
      have := q.firstHit_finish_mem ({y} : Set V) hmeet
      simpa only [Set.mem_singleton_iff] using this
    refine ⟨hq_parent_support hyq, r, Or.inl ⟨rfl, hrfinish⟩, ?_, ?_, ?_⟩
    · exact (q.firstHit_support_subset {y} hmeet).trans hq_parent_support
    · exact (q.firstHit_edgeSet_subset {y} hmeet).trans hq_parent_edges
    · rw [Set.disjoint_left]
      intro e her heC
      have heq : e ∈ q.edgeSet := q.firstHit_edgeSet_subset {y} hmeet her
      exact (hq_spec.1 heq).2 heC
  · rintro ⟨hyp, r, hends, hrsupp, hredges, hrdis⟩
    have hrE : r.edgeSet ⊆ E := by
      intro e her
      refine ⟨hredges her, ?_⟩
      exact fun heC ↦ Set.disjoint_left.1 hrdis her heC
    have hreach : Relation.ReflTransGen (WeakRel E) r.start r.finish :=
      RC.walk_reflTransGen_weakRel_of_edges_subset r.walk hrE
    have hcompEnds : componentMk E r.start = componentMk E r.finish :=
      Quotient.sound hreach
    have hqstart : q.start ∈ componentSupport E c := by
      rw [← hq_support]
      exact q.start_mem_support
    have hqc : componentMk E q.start = c := hqstart
    have hyc : componentMk E y = c := by
      rcases hends with hends | hends
      · rcases hends with ⟨hs, ht⟩
        rw [hs, ht] at hcompEnds
        exact hcompEnds.symm.trans hqc
      · rcases hends with ⟨hs, ht⟩
        rw [hs, ht] at hcompEnds
        exact hcompEnds.trans hqc
    rw [hq_support]
    exact hyc

end GroundingFiniteFragment
end Erdos599
