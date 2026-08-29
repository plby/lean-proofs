/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingConcreteControls
import ErdosProblems.Erdos599.GroundingFragmentUniqueness
import ErdosProblems.Erdos599.GroundingFragmentWarp
import ErdosProblems.Erdos599.GroundingPointwiseSwitch

/-!
# The cut predecessor of a nonfirst surviving fragment

Deleting the represented ladder edges partitions each directed ladder path
into maximal intervals.  A surviving interval either contains the initial
vertex of its parent, in which case it starts there, or the parent edge which
immediately enters its initial vertex is one of the deleted edges.  The
second alternative is exactly `GroundingConcreteControls.hasCutPredecessor`.

The proof below uses the maximality equation in `IsDeletedFragment`, rather
than assuming this elementary interval fact as extra control data.  If the
entering edge were not deleted, its one-edge path would put its tail in the
same surviving component.  The fragment would then traverse that tail after
its own initial vertex, whereas the parent traverses it immediately before
that vertex, contradicting simplicity and edge containment.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFragmentPredecessor

open DirectedPath

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type u) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- The endpoints of an edge of a directed simple finite path or ray are
distinct. -/
private theorem edge_endpoints_ne
    {P : Gamma.DPath} {x y : V} (hxy : (x, y) ∈ P.edgeSet) : x ≠ y := by
  cases P with
  | inl p =>
      obtain ⟨n, hn, hnx, hny⟩ :=
        DirectedPath.Walk.exists_adjacent_getElem_of_mem_edgeSet p.walk hxy
      intro hxyEq
      have hn0 : n < p.walk.support.length := by omega
      have hget :
          p.walk.support[n]'hn0 = p.walk.support[n + 1]'hn := by
        exact hnx.trans (hxyEq.trans hny.symm)
      have hindex : (⟨n, hn0⟩ : Fin p.walk.support.length) =
          ⟨n + 1, hn⟩ := p.isPath.get_inj_iff.mp hget
      have hval := congrArg Fin.val hindex
      exact Nat.ne_of_lt (Nat.lt_succ_self n) hval
  | inr r =>
      obtain ⟨n, hn⟩ := hxy
      intro hxyEq
      have hvalue : r n = r (n + 1) :=
        (congrArg Prod.fst hn).symm.trans
          (hxyEq.trans (congrArg Prod.snd hn))
      have hindex := r.injective hvalue
      omega

/-- An edge of a directed simple finite path or ray records the corresponding
strict order of its endpoints. -/
private theorem beforeEq_of_mem_edge
    {P : Gamma.DPath} {x y : V} (hxy : (x, y) ∈ P.edgeSet) :
    GroundingCut.BeforeEq P x y := by
  cases P with
  | inl p =>
      obtain ⟨n, hn, hnx, hny⟩ :=
        DirectedPath.Walk.exists_adjacent_getElem_of_mem_edgeSet p.walk hxy
      exact ⟨n, n + 1, ⟨by omega, hnx⟩, ⟨hn, hny⟩, by omega⟩
  | inr r =>
      obtain ⟨n, hn⟩ := hxy
      exact ⟨n, n + 1, (congrArg Prod.fst hn).symm,
        (congrArg Prod.snd hn).symm, by omega⟩

/-- A nonloop edge, viewed as a one-edge finite path. -/
private def oneEdgePath {x y : V} (hxy : Gamma.graph.Adj x y)
    (hne : x ≠ y) : FinitePath Gamma.graph where
  start := x
  finish := y
  walk := .cons hxy .nil
  isPath := by
    simp only [Walk.IsPath, Walk.support_cons, Walk.support_nil]
    simp [hne]

@[simp] private theorem oneEdgePath_support {x y : V}
    (hxy : Gamma.graph.Adj x y) (hne : x ≠ y) :
    (oneEdgePath hxy hne).support = {x, y} := by
  ext z
  simp [oneEdgePath, FinitePath.support]

@[simp] private theorem oneEdgePath_edgeSet {x y : V}
    (hxy : Gamma.graph.Adj x y) (hne : x ≠ y) :
    (oneEdgePath hxy hne).edgeSet = {(x, y)} := by
  ext e
  simp [oneEdgePath, FinitePath.edgeSet, Walk.edgeSet]

/-- If the edge entering the initial vertex of a maximal fragment survived
the cut, its tail would belong to the same fragment. -/
private theorem predecessor_tail_mem_of_not_mem_CE
    (L : Input Gamma I) (C : Set (LV L))
    {P : L.Fragment} (hP : P ∈ GroundingCut.fragments L C)
    {y : V} (hy : (y, P.path.initial) ∈ P.parent.edgeSet)
    (hyC : (y, P.path.initial) ∉ GroundingCut.CE L C) :
    y ∈ P.path.support := by
  have hyNe : y ≠ P.path.initial := edge_endpoints_ne hy
  have hyAdj : Gamma.graph.Adj y P.path.initial :=
    P.parent.edgeSet_subset_adj hy
  let q : FinitePath Gamma.graph := oneEdgePath hyAdj hyNe
  have hqSupport : q.support ⊆ P.parent.support := by
    intro z hz
    rw [oneEdgePath_support] at hz
    rcases hz with rfl | rfl
    · exact (P.parent.edgeSet_subset_support_prod hy).1
    · exact P.support_subset P.path.initial_mem_support
  have hqEdges : q.edgeSet ⊆ P.parent.edgeSet := by
    intro e he
    rw [oneEdgePath_edgeSet] at he
    simpa only [Set.mem_singleton_iff] using he ▸ hy
  have hqDisjoint : Disjoint q.edgeSet (GroundingCut.CE L C) := by
    rw [Set.disjoint_left]
    intro e heq heC
    rw [oneEdgePath_edgeSet] at heq
    exact hyC (Set.mem_singleton_iff.mp heq ▸ heC)
  have hconnected : GroundingCut.SurvivingConnected L C P.parent
      P.path.initial y := by
    refine ⟨q, Or.inr ⟨rfl, rfl⟩, hqSupport, hqEdges, hqDisjoint⟩
  rw [hP.2]
  exact ⟨(P.parent.edgeSet_subset_support_prod hy).1, hconnected⟩

/-- Exact interval classification for a maximal surviving fragment. -/
theorem initial_eq_parent_initial_or_hasCutPredecessor
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C) :
    P.path.initial = P.parent.initial ∨
      GroundingConcreteControls.hasCutPredecessor L C P := by
  by_cases hfirst : P.path.initial = P.parent.initial
  · exact Or.inl hfirst
  · right
    have hiParent : P.path.initial ∈ P.parent.support :=
      P.support_subset P.path.initial_mem_support
    obtain ⟨y, hy⟩ : ∃ y, (y, P.path.initial) ∈ P.parent.edgeSet := by
      cases hparent : P.parent with
      | inl p =>
          have hi : P.path.initial ∈ p.support := by
            simpa only [hparent, Path.support] using hiParent
          have hne : P.path.initial ≠ p.start := by
            simpa only [hparent, Path.initial] using hfirst
          obtain ⟨y, hy⟩ :=
            _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
              p hi hne
          exact ⟨y, by simpa only [hparent, Path.edgeSet] using hy⟩
      | inr r =>
          have hi : P.path.initial ∈ r.support := by
            simpa only [hparent, Path.support] using hiParent
          have hne : P.path.initial ≠ r.initial := by
            simpa only [hparent, Path.initial] using hfirst
          obtain ⟨y, hy⟩ :=
            _root_.Erdos599.Alternating.Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial
              r hi hne
          exact ⟨y, by simpa only [hparent, Path.edgeSet] using hy⟩
    refine ⟨(y, P.path.initial), ?_, hy, rfl⟩
    by_contra hyC
    have hyPath : y ∈ P.path.support :=
      predecessor_tail_mem_of_not_mem_CE L C hP hy hyC
    have hInitialY : GroundingCut.BeforeEq P.path P.path.initial y :=
      GroundingFragmentWarp.initial_beforeEq_of_mem hyPath
    have hInitialYParent :
        GroundingCut.BeforeEq P.parent P.path.initial y :=
      GroundingFragmentUniqueness.beforeEq_parent P hInitialY
    have hYInitialParent :
        GroundingCut.BeforeEq P.parent y P.path.initial :=
      beforeEq_of_mem_edge hy
    have hyEq : y = P.path.initial :=
      GroundingCutDecoder.beforeEq_antisymm
        hYInitialParent hInitialYParent
    exact edge_endpoints_ne hy hyEq

/-- A fragment without a represented cut predecessor is the first surviving
fragment of its parent. -/
theorem initial_eq_parent_initial_of_not_hasCutPredecessor
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    (hno : ¬ GroundingConcreteControls.hasCutPredecessor L C P) :
    P.path.initial = P.parent.initial := by
  rcases initial_eq_parent_initial_or_hasCutPredecessor L C P hP with h | h
  · exact h
  · exact False.elim (hno h)

end GroundingFragmentPredecessor
end Erdos599
