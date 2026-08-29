/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteDescentCounterexample

/-!
# A blocking point need not be a sink

The escaping branch in the definition of `GroundingCut.blockingPoint` can
choose an interior (indeed initial) vertex of a surviving fragment.  The
edge leaving that point is not deleted merely by Assertion 8.21.  This file
records the smallest example already present in the grounding development:
the one-edge ladder path `a -> b` with empty represented cut.  Its blocking
point is `a`, while the unchanged ladder relation has the outgoing edge
`a -> b`.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingBBSinkCounterexample

open DirectedPath Alternating
open GroundingFiniteDescentCounterexample
open GroundingFiniteDescentCounterexample.Vertex

/-- The whole one-edge ladder path, regarded as its own surviving fragment. -/
def wholeFragment : input.Fragment where
  path := Sum.inl ab
  parent := Sum.inl ab
  parent_mem := Set.mem_singleton _
  support_subset := Subset.rfl
  edges_subset := Subset.rfl

@[simp] theorem wholeFragment_path :
    wholeFragment.path = (Sum.inl ab : web.DPath) := rfl

theorem wholeFragment_mem_fragments :
    wholeFragment ∈ GroundingCut.fragments input (∅ : Set LV) := by
  constructor
  · rw [input_CE_empty]
    exact Set.disjoint_empty _
  · ext x
    constructor
    · intro hx
      refine ⟨hx, ?_⟩
      have hx' : x = a ∨ x = b := by
        change x ∈ ab.support at hx
        simpa [ab_support] using hx
      rcases hx' with rfl | rfl
      · refine ⟨FinitePath.trivial web.graph a, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
        · intro y hy
          have hya : y = a := by
            rw [FinitePath.support_trivial] at hy
            simpa using hy
          subst y
          change a ∈ ab.support
          simp
        · intro e he
          simp [FinitePath.edgeSet, FinitePath.trivial] at he
        · rw [input_CE_empty]
          exact Set.disjoint_empty _
      · refine ⟨ab, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
        · exact Subset.rfl
        · exact Subset.rfl
        · rw [input_CE_empty]
          exact Set.disjoint_empty _
    · exact fun hx => hx.1

theorem wholeFragment_mem_G0 :
    wholeFragment ∈ GroundingCut.G0 input (∅ : Set LV) := by
  apply GroundingCut.fragment_mem_G0_of_parent_not_groundedRecord
    input (∅ : Set LV) wholeFragment wholeFragment_mem_fragments
  change (Sum.inl ab : web.DPath) ∉ (∅ : Set web.DPath)
  simp

/-- The first escaping vertex `a` belongs to the grounding set `BB`. -/
theorem a_mem_BB :
    a ∈ GroundingCut.BB input (∅ : Set LV) := by
  apply GroundingCut.BL_subset_BB input (∅ : Set LV)
  have hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      input (∅ : Set LV) wholeFragment := by
    refine ⟨a, ?_,
      GroundingFiniteDescentCounterexample.a_mem_escapeRegion⟩
    change a ∈ DirectedPath.Path.support (Sum.inl ab : web.DPath)
    change a ∈ ab.support
    exact ab.start_mem_support
  exact ⟨wholeFragment, ⟨wholeFragment_mem_G0, Or.inl hescape⟩,
    GroundingFiniteDescentCounterexample.blockingPoint_eq_a
      wholeFragment wholeFragment_mem_G0⟩

theorem ab_mem_familyEdges :
    (a, b) ∈ familyEdges input.ladder.paths := by
  rw [input_ladder_paths]
  simp only [familyEdges, Set.mem_iUnion]
  refine ⟨(Sum.inl ab : web.DPath), Set.mem_singleton _, ?_⟩
  change (a, b) ∈ ab.walk.edgeSet
  rw [ab_edgeSet]
  simp

/-- Even with no switching-route edges at all, `a ∈ BB` has an outgoing
edge.  Thus `BB`-membership and Assertion 8.21's order conclusion cannot
imply the proposed sink statement. -/
theorem blockingPoint_has_outgoing_unchanged_relation :
    a ∈ GroundingCut.BB input (∅ : Set LV) ∧
      ∃ y, (a, y) ∈
        edgeSymmDiff (familyEdges input.ladder.paths) ∅ := by
  refine ⟨a_mem_BB, b, ?_⟩
  simp only [edgeSymmDiff_empty]
  exact ab_mem_familyEdges

/-- The order conclusion exported by Assertion 8.21 is compatible with the
same blocking point having an outgoing edge: taking its contact to be the
blocking point itself gives reflexive `BeforeEq`. -/
theorem assertion8_21_order_does_not_force_sink :
    GroundingCut.BeforeEq wholeFragment.path a
        (GroundingCut.blockingPoint input (∅ : Set LV) wholeFragment) ∧
      ∃ y, (a, y) ∈
        edgeSymmDiff (familyEdges input.ladder.paths) ∅ := by
  have haSupport : a ∈ wholeFragment.path.support := by
    change a ∈ ab.support
    simp
  constructor
  · rw [GroundingFiniteDescentCounterexample.blockingPoint_eq_a
      wholeFragment wholeFragment_mem_G0]
    exact GroundingCut.beforeEq_refl haSupport
  · exact blockingPoint_has_outgoing_unchanged_relation.2

theorem not_every_BB_vertex_is_a_sink :
    ¬ ∀ x ∈ GroundingCut.BB input (∅ : Set LV), ∀ y,
      (x, y) ∉ edgeSymmDiff (familyEdges input.ladder.paths) ∅ := by
  intro h
  apply h a a_mem_BB b
  simp only [edgeSymmDiff_empty]
  exact ab_mem_familyEdges

end GroundingBBSinkCounterexample
end Erdos599
