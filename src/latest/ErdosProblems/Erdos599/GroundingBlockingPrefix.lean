/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFragmentUniqueness
import ErdosProblems.Erdos599.GroundingFragmentWarp
import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# Residual prefixes to fragment blocking points

Every retained deleted-edge fragment has a finite directed prefix from its
initial vertex to its blocking point.  All edges of this prefix survive the
represented-edge deletion, and fragment uniqueness says that its only `BL`
vertex is its terminal blocking point.

This is deliberately a statement about `BL`, not all of `BB = CV ∪ BL`:
the source fragment family deletes only `CE`, so a retained fragment can
contain old cut vertices.  The simultaneous switch must account for those
`CV` contacts separately.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingBlockingPrefix

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- The exact fragment-level prefix used by the final `BB` geometry. -/
structure Data (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) where
  path : FinitePath Gamma.graph
  start_eq : path.start = P.path.initial
  finish_eq : path.finish = GroundingCut.blockingPoint L C P
  support_subset : path.support ⊆ P.path.support
  edgeSet_subset_residual :
    path.edgeSet ⊆ L.familyEdges \ GroundingCut.CE L C
  support_inter_BL_eq :
    path.support ∩ GroundingCut.BL L C =
      {GroundingCut.blockingPoint L C P}

/-- The degenerate prefix when the blocking point is the fragment initial. -/
private def initialData
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.blockableG0 L C)
    (heq : P.path.initial = GroundingCut.blockingPoint L C P) :
    Data L C P where
  path := FinitePath.trivial Gamma.graph P.path.initial
  start_eq := rfl
  finish_eq := heq
  support_subset := by
    intro x hx
    have hxEq : x = P.path.initial := by
      simpa [FinitePath.trivial, FinitePath.support] using hx
    exact hxEq ▸ P.path.initial_mem_support
  edgeSet_subset_residual := by
    intro e he
    simpa [FinitePath.trivial, FinitePath.edgeSet, Walk.edgeSet] using he
  support_inter_BL_eq := by
    ext x
    constructor
    · rintro ⟨hx, _hxBL⟩
      have hxEq : x = P.path.initial := by
        simpa [FinitePath.trivial, FinitePath.support] using hx
      exact Set.mem_singleton_iff.mpr (hxEq.trans heq)
    · intro hx
      have hxEq : x = GroundingCut.blockingPoint L C P :=
        Set.mem_singleton_iff.mp hx
      subst x
      constructor
      · have : GroundingCut.blockingPoint L C P = P.path.initial := heq.symm
        simpa [FinitePath.trivial, FinitePath.support, this]
      · exact ⟨P, hP, rfl⟩

/-- The nontrivial directed segment from the fragment initial to its
blocking point. -/
private def nontrivialData
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.blockableG0 L C)
    (hne : P.path.initial ≠ GroundingCut.blockingPoint L C P) :
    Data L C P := by
  have hbSupport : GroundingCut.blockingPoint L C P ∈ P.path.support :=
    GroundingCut.blockingPoint_mem_support L C P
  have hbeforeEq : GroundingCut.BeforeEq P.path P.path.initial
      (GroundingCut.blockingPoint L C P) :=
    GroundingFragmentWarp.initial_beforeEq_of_mem hbSupport
  let hex := GroundingCutDecoder.exists_forward_segment_of_before
      ⟨hbeforeEq, hne⟩
  let q := Classical.choose hex
  have hqStart : q.start = P.path.initial := (Classical.choose_spec hex).1
  have hqFinish : q.finish = GroundingCut.blockingPoint L C P :=
    (Classical.choose_spec hex).2.1
  have hqEdges : q.edgeSet ⊆ P.path.edgeSet :=
    (Classical.choose_spec hex).2.2
  have hqSupport : q.support ⊆ P.path.support := by
    intro x hx
    by_cases hxFinish : x = q.finish
    · rw [hxFinish, hqFinish]
      exact hbSupport
    · obtain ⟨y, hxy⟩ :=
        q.walk.exists_outgoing_edge_of_mem_of_ne_finish hx hxFinish
      exact (P.path.edgeSet_subset_support_prod (hqEdges hxy)).1
  refine {
    path := q
    start_eq := hqStart
    finish_eq := hqFinish
    support_subset := hqSupport
    edgeSet_subset_residual := ?_
    support_inter_BL_eq := ?_ }
  · intro e he
    have heP : e ∈ P.path.edgeSet := hqEdges he
    exact ⟨⟨P.parent, P.parent_mem, P.edges_subset heP⟩,
      fun heC ↦ Set.disjoint_left.1 hP.1.1.1 heP heC⟩
  · apply Set.Subset.antisymm
    · intro x hx
      exact GroundingFragmentUniqueness.support_inter_BL_subset_blockingPoint
        hP.1.1 ⟨hqSupport hx.1, hx.2⟩
    · intro x hx
      have hxEq : x = GroundingCut.blockingPoint L C P :=
        Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨hqFinish ▸ q.finish_mem_support, ⟨P, hP, rfl⟩⟩

/-- Every blockable retained fragment supplies a finite residual prefix ending
at its blocking point and meeting `BL` exactly there. -/
noncomputable def data
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.blockableG0 L C) :
    Data L C P := by
  by_cases heq : P.path.initial = GroundingCut.blockingPoint L C P
  · exact initialData L C P hP heq
  · exact nontrivialData L C P hP heq

/-! ## Conversion to the literal switched relation -/

/-- If the concrete prefix avoids the old-vertex part of the cut, its only
`BB = CV ∪ BL` vertex is its terminal blocking point. -/
theorem Data.support_inter_BB_eq
    {L : Input Gamma I} {C : Set (LV L)} {P : L.Fragment}
    (D : Data L C P)
    (hCV : Disjoint D.path.support (GroundingCut.CV L C)) :
    D.path.support ∩ GroundingCut.BB L C =
      {GroundingCut.blockingPoint L C P} := by
  rw [GroundingCut.BB, Set.inter_union_distrib_left,
    Set.disjoint_iff_inter_eq_empty.mp hCV, D.support_inter_BL_eq,
    Set.empty_union]

/-- A residual prefix becomes a path in the literal simultaneous switched
relation as soon as none of its edges is deleted by the toggle.  Forward
re-addition is not needed for this sufficient form. -/
theorem Data.edgeSet_subset_switched_of_disjoint_toggle
    {J : Type u} {kappa : Cardinal.{u}}
    {L : Input Gamma J}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    {P : L.Fragment} (D : Data L S.cut P)
    (hToggle : Disjoint D.path.edgeSet
      (GroundingErasedDecode.erasedSelectedToggleEdges U S K)) :
    D.path.edgeSet ⊆
      GroundingErasedDecode.erasedSelectedSwitchedEdges U S K := by
  intro e he
  exact Or.inl ⟨D.edgeSet_subset_residual he,
    Set.disjoint_left.1 hToggle he⟩

end GroundingBlockingPrefix
end Erdos599
