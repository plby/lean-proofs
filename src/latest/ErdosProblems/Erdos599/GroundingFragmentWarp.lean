/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutDecoder

/-!
# The deleted-predecessor splice in Assertion 8.20

If `P` is a component of a ladder path after the represented edges in `C`
have been deleted, and `s` is a deleted parent edge whose head is the initial
vertex of `P`, then every vertex `x` of `P` has a literal auxiliary route to
the edge gadget for `s`.  The route first traverses the surviving interval
from the initial vertex of `P` to `x` backwards, using edge gadgets, and then
stops at `s`.

This is the path-level construction in source Assertion 8.20.  The global
stationary thinning is kept separate: distinct members of an in-fan can meet
the same fragment, so one cannot put all of their splices into one warp
without first selecting distinct deleted predecessors.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFragmentWarp

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- Every vertex of a directed finite path or ray occurs weakly after its
initial vertex. -/
theorem initial_beforeEq_of_mem
    {P : Gamma.DPath} {x : V} (hx : x ∈ P.support) :
    GroundingCut.BeforeEq P P.initial x := by
  cases P with
  | inl p =>
      obtain ⟨n, hn⟩ :=
        (GroundingCut.mem_support_iff_exists_occursAt (.inl p) x).1 hx
      refine ⟨0, n, ?_, hn, Nat.zero_le _⟩
      exact ⟨p.support_length_pos, p.support_getElem_zero⟩
  | inr r =>
      obtain ⟨n, hn⟩ :=
        (GroundingCut.mem_support_iff_exists_occursAt (.inr r) x).1 hx
      exact ⟨0, n, rfl, hn, Nat.zero_le _⟩

/-- The deleted predecessor itself is not an edge of its surviving
fragment. -/
theorem predecessor_not_mem_fragment_edges
    (L : Input Gamma I) (C : Set (LV L))
    {P : L.Fragment} (hP : P ∈ GroundingCut.fragments L C)
    {s : V × V} (hsC : s ∈ GroundingCut.CE L C) :
    s ∉ P.path.edgeSet := by
  intro hsP
  exact Set.disjoint_left.1 hP.1 hsP hsC

/-- The raw edge-gadget walk from a contact `x` back to the deleted edge
`s` immediately preceding the fragment.

The output is a walk rather than a path because this form is convenient for
later splicing.  Loop erasure is performed by
`exists_path_to_cutPredecessor` below. -/
theorem exists_walk_to_cutPredecessor
    (L : Input Gamma I) (C : Set (LV L))
    {P : L.Fragment} (hP : P ∈ GroundingCut.fragments L C)
    {s : V × V}
    (hsC : s ∈ GroundingCut.CE L C)
    (hsParent : s ∈ P.parent.edgeSet)
    (hsHead : s.2 = P.path.initial)
    {x : V} (hx : x ∈ P.path.support) :
    ∃ w : Walk L.lambda.graph (.old x) (.edge s.1 s.2),
      ∀ z, z ∈ w.support → z ∈
        (({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L)) ∪
          (fun e : V × V ↦
            PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2) ''
            (insert s P.path.edgeSet)) := by
  have hsAdj : Gamma.graph.Adj s.1 s.2 :=
    P.parent.edgeSet_subset_adj hsParent
  have hsFamily : s ∈ L.familyEdges := ⟨P.parent, P.parent_mem, hsParent⟩
  have hbeforeEq : GroundingCut.BeforeEq P.path P.path.initial x :=
    initial_beforeEq_of_mem hx
  by_cases hxi : x = P.path.initial
  · have hxs : x = s.2 := hxi.trans hsHead.symm
    rw [hxs]
    let w : Walk L.lambda.graph (.old s.2) (.edge s.1 s.2) :=
      .cons ((L.lambda_adj_old_edge s.2 s.1 s.2).2
        ⟨hsFamily, Or.inl rfl⟩) .nil
    refine ⟨w, ?_⟩
    intro z hz
    simp only [w, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hz
    rcases hz with rfl | hz
    · exact Or.inl (Set.mem_singleton _)
    · rcases hz with rfl | hz
      · exact Or.inr ⟨s, Set.mem_insert s P.path.edgeSet,
          by simp⟩
      · simp at hz
  · have hbefore : GroundingCut.Before P.path P.path.initial x :=
      ⟨hbeforeEq, fun h ↦ hxi h.symm⟩
    obtain ⟨q, hqStart, hqFinish, hqEdges⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before hbefore
    subst x
    have hqParent : q.edgeSet ⊆ P.parent.edgeSet :=
      hqEdges.trans P.edges_subset
    have hqFamily : q.edgeSet ⊆ L.familyEdges := by
      intro e he
      exact ⟨P.parent, P.parent_mem, hqParent he⟩
    change q.walk.edgeSet ⊆ L.familyEdges at hqFamily
    have hsStart : q.start = s.2 := hqStart.trans hsHead.symm
    let qwalk : Walk Gamma.graph s.2 q.finish :=
      RelationalRoof.castStart Gamma.graph.Adj hsStart q.walk
    have hqwalkFamily : qwalk.edgeSet ⊆ L.familyEdges := by
      simpa only [qwalk, Walk.edgeSet_castStart] using hqFamily
    let w : Walk L.lambda.graph (.old q.finish) (.edge s.1 s.2) :=
      GroundingCutDecoder.reverseGadgetCore L hsAdj qwalk hsFamily
        hqwalkFamily
    refine ⟨w, ?_⟩
    intro z hz
    rcases GroundingCutDecoder.mem_reverseGadgetCore_support
        L hsAdj qwalk hsFamily hqwalkFamily hz with hzOld | ⟨e, he, hze⟩
    · exact Or.inl (by simpa [hzOld])
    · apply Or.inr
      refine ⟨e, ?_, hze.symm⟩
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      rcases he with he | he
      · exact Set.mem_insert_iff.2 (Or.inl he)
      · apply Set.mem_insert_iff.2
        apply Or.inr
        have he' : e ∈ q.walk.edgeSet := by
          simpa only [qwalk, Walk.edgeSet_castStart] using he
        change q.walk.edgeSet ⊆ P.path.edgeSet at hqEdges
        exact hqEdges he'

/-- Loop-erasing the raw splice gives a finite auxiliary path with the same
endpoints.  Its internal gadget support is still confined to the chosen
fragment and its deleted predecessor. -/
theorem exists_path_to_cutPredecessor
    (L : Input Gamma I) (C : Set (LV L))
    {P : L.Fragment} (hP : P ∈ GroundingCut.fragments L C)
    {s : V × V}
    (hsC : s ∈ GroundingCut.CE L C)
    (hsParent : s ∈ P.parent.edgeSet)
    (hsHead : s.2 = P.path.initial)
    {x : V} (hx : x ∈ P.path.support) :
    ∃ q : FinitePath L.lambda.graph,
      q.start = .old x ∧ q.finish = .edge s.1 s.2 ∧
        q.support ⊆
          (({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L)) ∪
            (fun e : V × V ↦
              PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2) ''
              (insert s P.path.edgeSet)) := by
  obtain ⟨w, hwSupport⟩ :=
    exists_walk_to_cutPredecessor L C hP hsC hsParent hsHead hx
  obtain ⟨r, hrSupport⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := L.lambda.graph.Adj) w
  let q : FinitePath L.lambda.graph :=
    { start := .old x
      finish := .edge s.1 s.2
      walk := r.1
      isPath := r.2 }
  refine ⟨q, rfl, rfl, ?_⟩
  intro z hz
  exact hwSupport z (hrSupport hz)

/-- Starting at any edge gadget of a surviving fragment, one can travel
backwards through edge gadgets to a deleted parent edge immediately preceding
the fragment.  In particular, no old vertex is retained in the resulting
simple path. -/
theorem exists_edge_path_to_cutPredecessor
    (L : Input Gamma I) (C : Set (LV L))
    {P : L.Fragment} (hP : P ∈ GroundingCut.fragments L C)
    {s e : V × V}
    (hsC : s ∈ GroundingCut.CE L C)
    (hsParent : s ∈ P.parent.edgeSet)
    (hsHead : s.2 = P.path.initial)
    (heP : e ∈ P.path.edgeSet) :
    ∃ q : FinitePath L.lambda.graph,
      q.start = .edge e.1 e.2 ∧ q.finish = .edge s.1 s.2 ∧
        q.support ⊆
          (fun f : V × V ↦
            PopularAuxiliary.Input.LambdaVertex.edge f.1 f.2) ''
            (insert s P.path.edgeSet) := by
  have heSupport : e.1 ∈ P.path.support :=
    (P.path.edgeSet_subset_support_prod heP).1
  obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
    exists_path_to_cutPredecessor L C hP hsC hsParent hsHead heSupport
  have heFamily : e ∈ L.familyEdges :=
    ⟨P.parent, P.parent_mem, P.edges_subset heP⟩
  have hstartFinish : q.start ≠ q.finish := by
    intro h
    rw [hqStart, hqFinish] at h
    cases h
  obtain ⟨b, hab, tail, hwalk⟩ :=
    RelationalRoof.exists_cons_of_start_ne_finish
      L.lambda.graph.Adj q.walk hstartFinish
  have holdb : L.lambda.graph.Adj
      (PopularAuxiliary.Input.LambdaVertex.old e.1) b := by
    simpa only [hqStart] using hab
  have hedgeB : L.lambda.graph.Adj
      (PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2) b :=
    GroundingCutDecoder.lambda_adj_edge_of_old L heFamily holdb
  let w : Walk L.lambda.graph (.edge e.1 e.2) q.finish :=
    .cons hedgeB tail
  have hwSupport : ∀ z, z ∈ w.support →
      z ∈ (fun f : V × V ↦
        PopularAuxiliary.Input.LambdaVertex.edge f.1 f.2) ''
        (insert s P.path.edgeSet) := by
    intro z hz
    simp only [w, Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hztail
    · exact ⟨e, Set.mem_insert_iff.2 (Or.inr heP), rfl⟩
    · have hzq : z ∈ q.support := by
        change z ∈ q.walk.support
        rw [hwalk]
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr hztail
      rcases hqSupport hzq with hzOld | hzEdge
      · have hzeq : z =
            PopularAuxiliary.Input.LambdaVertex.old e.1 := by
          simpa only [Set.mem_singleton_iff] using hzOld
        have hbadOld :
            PopularAuxiliary.Input.LambdaVertex.old e.1 ∈
              q.walk.support.tail := by
          rw [hwalk]
          simpa only [Walk.support_cons, List.tail_cons, hzeq] using hztail
        have hnotOld :
            PopularAuxiliary.Input.LambdaVertex.old e.1 ∉
              q.walk.support.tail := by
          simpa only [hqStart] using
            q.walk.start_not_mem_support_tail q.isPath
        exact False.elim
          (hnotOld hbadOld)
      · exact hzEdge
  obtain ⟨r, hrSupport⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := L.lambda.graph.Adj) w
  let p : FinitePath L.lambda.graph :=
    { start := .edge e.1 e.2
      finish := q.finish
      walk := r.1
      isPath := r.2 }
  refine ⟨p, rfl, hqFinish, ?_⟩
  intro z hz
  exact hwSupport z (hrSupport hz)

/-- The endpoint of the predecessor splice is literally a vertex of the
auxiliary cut. -/
theorem path_to_cutPredecessor_finish_mem_cut
    (L : Input Gamma I) (C : Set (LV L))
    {P : L.Fragment} (hP : P ∈ GroundingCut.fragments L C)
    {s : V × V}
    (hsC : s ∈ GroundingCut.CE L C)
    (hsParent : s ∈ P.parent.edgeSet)
    (hsHead : s.2 = P.path.initial)
    {x : V} (hx : x ∈ P.path.support) :
    ∃ q : FinitePath L.lambda.graph,
      q.start = .old x ∧ q.finish ∈ C := by
  obtain ⟨q, hqStart, hqFinish, _⟩ :=
    exists_path_to_cutPredecessor L C hP hsC hsParent hsHead hx
  refine ⟨q, hqStart, ?_⟩
  rw [hqFinish]
  exact hsC.1

end GroundingFragmentWarp
end Erdos599
