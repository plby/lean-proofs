/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutDecoder

/-!
# Assertion 8.21 at an edge-gadget endpoint

The usual pointwise form of Assertion 8.21 takes an avoiding auxiliary path
ending at `old x`.  A request whose apex is the cut vertex `old x` cannot use
that form.  Immediately before its apex, however, the route ends at a
surviving edge gadget `edge x y`.  This file proves the corresponding order
statement directly.

The proof removes only `old x` from the cut while constructing the reverse
escape.  Removing an old vertex does not change `CE`, hence does not change
the fragment decomposition.  The temporary reverse path may start at
`old x`; replacing that first vertex by `edge x y` removes the only possible
contact with the original cut.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingCutEndpointOrder

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- Removing one old auxiliary vertex does not change the represented edge
part of a cut. -/
theorem CE_diff_singleton_old
    (L : Input Gamma I) (C : Set (LV L)) (x : V) :
    GroundingCut.CE L
        (C \ {(PopularAuxiliary.Input.LambdaVertex.old x : LV L)}) =
      GroundingCut.CE L C := by
  ext e
  simp only [GroundingCut.mem_CE, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    refine ⟨⟨h.1, ?_⟩, h.2⟩
    intro heq
    cases heq

/-- The fragment family is unchanged after removing one old auxiliary
vertex, since its definition depends on the cut only through `CE`. -/
theorem fragments_diff_singleton_old
    (L : Input Gamma I) (C : Set (LV L)) (x : V) :
    GroundingCut.fragments L
        (C \ {(PopularAuxiliary.Input.LambdaVertex.old x : LV L)}) =
      GroundingCut.fragments L C := by
  have hCE := CE_diff_singleton_old L C x
  ext P
  simp only [GroundingCut.fragments, GroundingCut.IsDeletedFragment,
    Set.mem_setOf_eq]
  rw [hCE]
  simp only [GroundingCut.SurvivingConnected, hCE]

/-- Replace the first `old x` of an avoiding path by the surviving edge
gadget `edge x y`.  Besides avoidance, retain the fact that the removed old
vertex does not occur on the new path. -/
theorem exists_avoiding_path_from_edge_of_old_start_no_old
    (L : Input Gamma I) (C : Set (LV L)) {x y : V}
    (hxy : (x, y) ∈ L.familyEdges)
    (hnotCE : (x, y) ∉ GroundingCut.CE L C)
    (q : FinitePath L.lambda.graph)
    (hqstart : q.start = .old x)
    (hxnotTarget :
      (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ L.lambda.target)
    (hqfinish : q.finish ∈ L.lambda.target)
    (hqavoid : L.lambda.Avoids q C) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .edge x y ∧ r.finish = q.finish ∧
        L.lambda.Avoids r C ∧
        (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ r.support := by
  have hxNotFinish :
      (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ≠ q.finish := by
    intro hx
    exact hxnotTarget (hx ▸ hqfinish)
  have hstartFinish : q.start ≠ q.finish := by
    intro heq
    exact hxNotFinish (hqstart ▸ heq)
  obtain ⟨b, hab, tail, hwalk⟩ :=
    RelationalRoof.exists_cons_of_start_ne_finish
      L.lambda.graph.Adj q.walk hstartFinish
  have holdb : L.lambda.graph.Adj
      (PopularAuxiliary.Input.LambdaVertex.old x) b := by
    simpa only [hqstart] using hab
  have hedgeB : L.lambda.graph.Adj
      (PopularAuxiliary.Input.LambdaVertex.edge x y) b :=
    GroundingCutDecoder.lambda_adj_edge_of_old L hxy holdb
  let w : Walk L.lambda.graph
      (PopularAuxiliary.Input.LambdaVertex.edge x y) q.finish :=
    .cons hedgeB tail
  obtain ⟨p, hpSupport⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := L.lambda.graph.Adj) w
  let r : FinitePath L.lambda.graph :=
    { start := .edge x y
      finish := q.finish
      walk := p.1
      isPath := p.2 }
  have hOldNotTail :
      (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉
        q.walk.support.tail := by
    simpa only [hqstart] using q.walk.start_not_mem_support_tail q.isPath
  refine ⟨r, rfl, rfl, ?_, ?_⟩
  · change Disjoint r.support C
    rw [Set.disjoint_left]
    intro z hzr hzC
    have hzw : z ∈ w.support := hpSupport hzr
    simp only [w, Walk.support_cons, List.mem_cons] at hzw
    rcases hzw with hze | hztail
    · subst z
      exact GroundingCutDecoder.edge_not_mem_cut_of_not_mem_CE
        L C hxy hnotCE hzC
    · have hzq : z ∈ q.support := by
        change z ∈ q.walk.support
        rw [hwalk]
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr hztail
      exact Set.disjoint_left.1 hqavoid hzq hzC
  · intro hxOld
    have hxw : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈
        w.support := hpSupport hxOld
    simp only [w, Walk.support_cons, List.mem_cons] at hxw
    rcases hxw with hedge | htail
    · cases hedge
    · apply hOldNotTail
      rw [hwalk]
      simpa only [Walk.support_cons, List.tail_cons] using htail

/-- If a cut-avoiding source path reaches the gadget for a represented
edge whose tail is already a Lambda target, then the old copy of that tail
must belong to the separating cut.  Otherwise the path can be extended by
the canonical zero-length gadget exit `edge x y -> old x`, loop-erased, and
would contradict separation. -/
theorem oldTail_mem_cut_of_edgeContact_of_target
    (L : Input Gamma I) (C : Set (LV L))
    (hC : Popular.IsSeparator L.lambda C)
    (q : FinitePath L.lambda.graph)
    (hqstart : q.start ∈ L.lambda.source)
    (hqavoid : L.lambda.Avoids q C) {x y : V}
    (hqfinish : q.finish = .edge x y)
    (hxy : (x, y) ∈ L.familyEdges)
    (hxTarget :
      (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈
        L.lambda.target) :
    (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈ C := by
  by_contra hxCut
  have hedgeOld : L.lambda.graph.Adj
      (PopularAuxiliary.Input.LambdaVertex.edge x y)
      (PopularAuxiliary.Input.LambdaVertex.old x) :=
    GroundingCutDecoder.lambda_adj_edge_to_old_tail L hxy
  let w : Walk L.lambda.graph q.start
      (PopularAuxiliary.Input.LambdaVertex.old x) :=
    q.walk.concat (hqfinish.symm ▸ hedgeOld)
  obtain ⟨p, hpSupport⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := L.lambda.graph.Adj) w
  let r : FinitePath L.lambda.graph :=
    { start := q.start
      finish := .old x
      walk := p.1
      isPath := p.2 }
  have hravoid : L.lambda.Avoids r C := by
    change Disjoint r.support C
    rw [Set.disjoint_left]
    intro z hzr hzC
    have hzw : z ∈ w.support := hpSupport hzr
    simp only [w, Walk.support_concat, List.mem_append,
      List.mem_singleton] at hzw
    rcases hzw with hzq | rfl
    · exact Set.disjoint_left.1 hqavoid hzq hzC
    · exact hxCut hzC
  exact PopularAuxiliary.Input.no_avoiding_source_target_path
    L.lambda C hC r hqstart hxTarget hravoid

/-- Assertion 8.21 when the avoiding source prefix ends at a surviving edge
gadget whose tail lies in the fragment.  The represented edge need not
itself have been retained in the concrete fragment path; family membership
and absence from `CE` are the exact gadget hypotheses used by the splice.
The tail lies no later than the fragment blocking point. -/
theorem assertion8_21_edgeTail
    (L : Input Gamma I) (C : Set (LV L))
    (hC : Popular.IsSeparator L.lambda C)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L C)
    (hblockable : GroundingCut.IsBlockable L C P)
    (q : FinitePath L.lambda.graph)
    (hqstart : q.start ∈ L.lambda.source)
    (hqavoid : L.lambda.Avoids q C) {x y : V}
    (hqfinish : q.finish = .edge x y)
    (hxP : x ∈ P.path.support)
    (hxyFamily : (x, y) ∈ L.familyEdges)
    (hxyNotCE : (x, y) ∉ GroundingCut.CE L C)
    (hxnotTarget :
      (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ L.lambda.target) :
    GroundingCut.BeforeEq P.path x
      (GroundingCut.blockingPoint L C P) := by
  have hbP : GroundingCut.blockingPoint L C P ∈ P.path.support :=
    GroundingCut.blockingPoint_mem_support L C P hblockable
  rcases GroundingCut.beforeEq_total hxP hbP with hxb | hbx
  · exact hxb
  · by_cases heq : GroundingCut.blockingPoint L C P = x
    · simpa [heq] using GroundingCut.beforeEq_refl hxP
    · have hbefore : GroundingCut.Before P.path
        (GroundingCut.blockingPoint L C P) x := ⟨hbx, heq⟩
      have hescape :
          PopularAuxiliary.Input.Fragment.MeetsEscape L C P := by
        by_contra hno
        have hfinite : P.path.IsFinite := hblockable.resolve_left hno
        obtain ⟨t, ht⟩ := hfinite
        have hbEq : GroundingCut.blockingPoint L C P = t :=
          GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
            L C P hno ht
        have hterminal : GroundingCut.BeforeEq P.path x t :=
          GroundingCut.beforeEq_terminal ht hxP
        apply heq
        apply GroundingCutDecoder.beforeEq_antisymm hbx
        simpa only [hbEq] using hterminal
      obtain ⟨E⟩ :=
        GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
          L C P hescape
      let C' : Set (LV L) :=
        C \ {(PopularAuxiliary.Input.LambdaVertex.old x : LV L)}
      have hP' : P ∈ GroundingCut.fragments L C' := by
        rw [fragments_diff_singleton_old L C x]
        exact hP.1
      let E' : L.RelaxedEscape C' (GroundingCut.blockingPoint L C P) :=
        { route := E.route
          start_eq := E.start_eq
          target := E.target
          avoids := Set.disjoint_of_subset_right Set.diff_subset E.avoids
          old_not_mem := fun h => E.old_not_mem h.1 }
      have hxNotC' :
          (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ C' := by
        simp [C']
      obtain ⟨s, hsstart, hsfinish, hsavoid⟩ :=
        GroundingCutDecoder.exists_avoiding_reverse_to_relaxedEscape
          L C' P hP' hbefore hxNotC' E'
      have hxyNotCE' : (x, y) ∉ GroundingCut.CE L C' := by
        rw [CE_diff_singleton_old L C x]
        exact hxyNotCE
      obtain ⟨r, hrstart, hrfinish, hravoidC', hxNotR⟩ :=
        exists_avoiding_path_from_edge_of_old_start_no_old
          L C' hxyFamily hxyNotCE' s hsstart hxnotTarget hsfinish hsavoid
      have hravoid : L.lambda.Avoids r C := by
        change Disjoint r.support C
        rw [Set.disjoint_left]
        intro z hzr hzC
        by_cases hzx : z =
            (PopularAuxiliary.Input.LambdaVertex.old x : LV L)
        · exact hxNotR (hzx ▸ hzr)
        · exact Set.disjoint_left.1 hravoidC' hzr ⟨hzC, hzx⟩
      obtain ⟨t, htstart, htfinish, htavoid⟩ :=
        PopularSwitching.exists_avoiding_path_of_avoiding_paths
          q r (hqfinish.trans hrstart.symm) hqavoid hravoid
      exact False.elim <|
        PopularAuxiliary.Input.no_avoiding_source_target_path
          L.lambda C hC t (htstart ▸ hqstart)
            (htfinish ▸ (hrfinish ▸ hsfinish)) htavoid

/-- Target-complete endpoint form.  Without assuming that `old x` is not a
Lambda target, the exact conclusion is that the edge tail is ordered before
the blocking point or its old copy belongs to the separator. -/
theorem assertion8_21_edgeTail_or_old_mem_cut
    (L : Input Gamma I) (C : Set (LV L))
    (hC : Popular.IsSeparator L.lambda C)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L C)
    (hblockable : GroundingCut.IsBlockable L C P)
    (q : FinitePath L.lambda.graph)
    (hqstart : q.start ∈ L.lambda.source)
    (hqavoid : L.lambda.Avoids q C) {x y : V}
    (hqfinish : q.finish = .edge x y)
    (hxP : x ∈ P.path.support)
    (hxyFamily : (x, y) ∈ L.familyEdges)
    (hxyNotCE : (x, y) ∉ GroundingCut.CE L C) :
    GroundingCut.BeforeEq P.path x
        (GroundingCut.blockingPoint L C P) ∨
      (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈ C := by
  by_cases hxTarget :
      (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈
        L.lambda.target
  · exact Or.inr <| oldTail_mem_cut_of_edgeContact_of_target
      L C hC q hqstart hqavoid hqfinish hxyFamily hxTarget
  · exact Or.inl <| assertion8_21_edgeTail
      L C hC P hP hblockable q hqstart hqavoid hqfinish
        hxP hxyFamily hxyNotCE hxTarget

end GroundingCutEndpointOrder
end Erdos599
