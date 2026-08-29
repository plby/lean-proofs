/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutDecoder

/-!
# Start-relaxed escapes in Assertion 8.18

The recursive step in the proof of Aharoni--Berger Assertion 8.18 starts a
forward link at a vertex which already lies on the reference warp.  This is
not, by itself, a path in `Lambda`: an old ladder vertex is not an ordinary
forward source.  The route becomes a genuine `Lambda` path only after a
nonempty piece of the contacted ladder fragment has been traversed backwards.

This file records that source-faithful boundary convention explicitly.  A
`RelaxedEscape` either is an ordinary avoiding `Lambda` route from `old x`, or
has one virtual first forward connector out of `x`.  The main theorem splices
the latter connector directly to the last edge gadget of a nonempty backwards
fragment traversal.  No source-encoding assumption is used.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingRelaxedEscape

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

abbrev RelaxedForwardStep (L : Input Gamma I) (x : V) : LV L → Prop :=
  L.RelaxedForwardStep x

abbrev RelaxedEscape
    (L : Input Gamma I) (C : Set (LV L)) (x : V) :=
  L.RelaxedEscape C x

/-- Ordinary `Lambda` reachability is a special case of relaxed reachability. -/
def RelaxedEscape.ofOrdinary
    (L : Input Gamma I) (C : Set (LV L)) {x : V}
    (h : L.lambda.CanReachTargetAvoiding C (.old x)) :
    RelaxedEscape L C x := by
  let q := Classical.choose h
  have hq := (Classical.choose_spec h).1
  have hqavoid := (Classical.choose_spec h).2
  refine {
    route := q
    start_eq := Or.inl hq.1
    target := hq.2
    avoids := hqavoid
    old_not_mem := ?_ }
  intro hxC
  exact Set.disjoint_left.1 hqavoid q.start_mem_support (hq.1 ▸ hxC)

/-- A virtual first forward step can be entered from the gadget for a ladder
edge whose tail is the relaxed starting vertex. -/
theorem lambda_adj_edge_of_relaxedForwardStep
    (L : Input Gamma I) {x z : V} {a : LV L}
    (hxz : (x, z) ∈ L.familyEdges)
    (ha : RelaxedForwardStep L x a) :
    L.lambda.graph.Adj (.edge x z) a := by
  cases a with
  | old y =>
      exact (L.lambda_adj_edge_old x z y).2
        ⟨hxz, Or.inr ha⟩
  | edge u y =>
      exact (L.lambda_adj_edge_edge x z u y).2
        ⟨hxz, ha.1, Or.inr ha.2⟩
  | proxy i => exact False.elim ha

/-- Every vertex of the raw backwards core avoids the cut, provided the
displayed old endpoint avoids it and the traversed fragment survives deletion
of `CE`. -/
private theorem reverseCore_avoids
    (L : Input Gamma I) (C : Set (LV L))
    {P : L.Fragment} (hP : P ∈ GroundingCut.fragments L C)
    {a c b : V} (hac : Gamma.graph.Adj a c)
    (q : Walk Gamma.graph c b)
    (hsegment : (Walk.cons hac q).edgeSet ⊆ P.path.edgeSet)
    (hacFamily : (a, c) ∈ L.familyEdges)
    (hqFamily : q.edgeSet ⊆ L.familyEdges)
    (hb : (PopularAuxiliary.Input.LambdaVertex.old b : LV L) ∉ C) :
    Disjoint
      ({w | w ∈
        (GroundingCutDecoder.reverseGadgetCore L hac q hacFamily hqFamily).support} :
        Set (LV L)) C := by
  rw [Set.disjoint_left]
  intro w hw hCw
  rcases GroundingCutDecoder.mem_reverseGadgetCore_support
      L hac q hacFamily hqFamily hw with rfl | ⟨e, he, rfl⟩
  · exact hb hCw
  · have heFragment : e ∈ P.path.edgeSet := hsegment he
    have heNotCE : e ∉ GroundingCut.CE L C :=
      Set.disjoint_left.1 hP.1 heFragment
    have heFamily : e ∈ L.familyEdges :=
      ⟨P.parent, P.parent_mem, P.edges_subset heFragment⟩
    exact GroundingCutDecoder.edge_not_mem_cut_of_not_mem_CE
      L C heFamily heNotCE hCw

/-- A strict backwards traversal from `x` to a relaxed escaping point `b`
absorbs the virtual first connector and yields an ordinary avoiding path from
`old x` to the auxiliary target.  This is the literal splice used at every
iteration of Assertion 8.18. -/
theorem exists_avoiding_reverse_to_relaxedEscape
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {b x : V} (hbx : GroundingCut.Before P.path b x)
    (hxNotC : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ C)
    (E : RelaxedEscape L C b) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .old x ∧ r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r C := by
  rcases E.start_eq with hordinary | hrelaxed
  · obtain ⟨p, hpStart, hpFinish, hpAvoid⟩ :=
      GroundingCutDecoder.backwardDecode L C P hP
        E.old_not_mem hxNotC hbx
    obtain ⟨r, hrStart, hrFinish, hrAvoid⟩ :=
      PopularSwitching.exists_avoiding_path_of_avoiding_paths
        p E.route (hpFinish.trans hordinary.symm) hpAvoid E.avoids
    exact ⟨r, hrStart.trans hpStart, hrFinish ▸ E.target, hrAvoid⟩
  · obtain ⟨p, hpStart, hpFinish, hpEdges⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before hbx
    have hpNe : p.start ≠ p.finish := by
      intro h
      exact hbx.2 (hpStart.symm.trans (h.trans hpFinish))
    obtain ⟨c, hac, tail, hpWalk⟩ :=
      RelationalRoof.exists_cons_of_start_ne_finish
        Gamma.graph.Adj p.walk hpNe
    have hacEdge : (p.start, c) ∈ p.edgeSet := by
      change (p.start, c) ∈ p.walk.edgeSet
      rw [hpWalk]
      simp
    have hacFragment : (p.start, c) ∈ P.path.edgeSet := hpEdges hacEdge
    have hacFamily : (p.start, c) ∈ L.familyEdges :=
      ⟨P.parent, P.parent_mem, P.edges_subset hacFragment⟩
    have htailFamily : tail.edgeSet ⊆ L.familyEdges := by
      intro e he
      have hep : e ∈ p.edgeSet := by
        change e ∈ p.walk.edgeSet
        rw [hpWalk]
        exact Set.mem_union_right _ he
      have heFragment := hpEdges hep
      exact ⟨P.parent, P.parent_mem, P.edges_subset heFragment⟩
    have hwholeFragment : (Walk.cons hac tail).edgeSet ⊆ P.path.edgeSet := by
      intro e he
      apply hpEdges
      change e ∈ p.walk.edgeSet
      simpa only [hpWalk] using he
    let core : Walk L.lambda.graph
        (.old p.finish) (.edge p.start c) :=
      GroundingCutDecoder.reverseGadgetCore L hac tail
        hacFamily htailFamily
    have hcoreAvoid : Disjoint
        ({w | w ∈ core.support} : Set (LV L)) C := by
      apply reverseCore_avoids L C hP hac tail hwholeFragment
        hacFamily htailFamily
      simpa only [hpFinish] using hxNotC
    have hjoin : L.lambda.graph.Adj (.edge p.start c) E.route.start := by
      apply lambda_adj_edge_of_relaxedForwardStep L hacFamily
      simpa only [hpStart] using hrelaxed
    let suffix : Walk L.lambda.graph (.edge p.start c) E.route.finish :=
      .cons hjoin E.route.walk
    let raw : Walk L.lambda.graph (.old p.finish) E.route.finish :=
      core.append suffix
    obtain ⟨q, hqSupport⟩ :=
      RelationalRoof.exists_pathTo_support_subset
        (R := L.lambda.graph.Adj) raw
    let r : FinitePath L.lambda.graph :=
      { start := .old p.finish
        finish := E.route.finish
        walk := q.1
        isPath := q.2 }
    refine ⟨r, by simpa only [r, hpFinish], E.target, ?_⟩
    change Disjoint r.support C
    rw [Set.disjoint_left]
    intro w hwr hwC
    have hwRaw : w ∈ raw.support := hqSupport hwr
    have hwAppend : w ∈ core.support ++ suffix.support.tail := by
      simpa only [raw, Walk.support_append] using hwRaw
    rcases List.mem_append.mp hwAppend with hwCore | hwSuffix
    · exact Set.disjoint_left.1 hcoreAvoid hwCore hwC
    · have hwRoute : w ∈ E.route.support := by
        change w ∈ E.route.walk.support
        simpa only [suffix, Walk.support_cons, List.tail_cons] using hwSuffix
      exact Set.disjoint_left.1 E.avoids hwRoute hwC

end GroundingRelaxedEscape
end Erdos599
