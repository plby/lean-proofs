/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCVFragmentAudit
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# The residual ladder alone does not make `BB` an antichain

Deleting represented edge gadgets does not delete old cut vertices from the
ladder relation.  Consequently a retained fragment can contain an old cut
vertex strictly before its blocking point.  The one-edge example below has
both endpoints in `BB` and retains the edge between them.

Thus Assertion 8.21's off-apex contact order is not, by itself, enough for
the final reachability-antichain theorem.  The switched proof additionally
needs an endpoint lemma saying that the selected route at such an old
request deletes the residual continuation, or an equivalent global
one-hit invariant.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingBBAntichainCounterexample

open DirectedPath
open GroundingCVFragmentAudit.Concrete
open GroundingCVFragmentAudit.Concrete.Vertex
open GroundingRootedReachabilityWarp

/-- The full one-edge ladder path is the surviving fragment, since the old
cut contains no represented edge gadget. -/
def wholeFragment : input.Fragment where
  path := Sum.inl ab
  parent := Sum.inl ab
  parent_mem := Set.mem_singleton _
  support_subset := Subset.rfl
  edges_subset := Subset.rfl

@[simp] theorem wholeFragment_path :
    wholeFragment.path = (Sum.inl ab : web.DPath) := rfl

theorem wholeFragment_mem_fragments :
    wholeFragment ∈ GroundingCut.fragments input oldInitialCut := by
  constructor
  · rw [oldInitialCut_CE_empty]
    exact Set.disjoint_empty _
  · ext x
    constructor
    · intro hx
      refine ⟨hx, ?_⟩
      have hx' : x = a ∨ x = b := by
        change x ∈ ab.support at hx
        simpa [ab_support] using hx
      rcases hx' with rfl | rfl
      · refine ⟨FinitePath.trivial web.graph a, Or.inl ⟨rfl, rfl⟩,
          ?_, ?_, ?_⟩
        · intro y hy
          have hya : y = a := by
            rw [FinitePath.support_trivial] at hy
            simpa using hy
          subst y
          change a ∈ ab.support
          simp
        · intro e he
          simp [FinitePath.edgeSet, FinitePath.trivial] at he
        · rw [oldInitialCut_CE_empty]
          exact Set.disjoint_empty _
      · refine ⟨ab, Or.inl ⟨rfl, rfl⟩, Subset.rfl, Subset.rfl, ?_⟩
        rw [oldInitialCut_CE_empty]
        exact Set.disjoint_empty _
    · exact fun hx ↦ hx.1

theorem wholeFragment_mem_G0 :
    wholeFragment ∈ GroundingCut.G0 input oldInitialCut := by
  apply GroundingCut.fragment_mem_G0_of_parent_not_groundedRecord
    input oldInitialCut wholeFragment wholeFragment_mem_fragments
  change (Sum.inl ab : web.DPath) ∉ (∅ : Set web.DPath)
  simp

/-- With no auxiliary target marker, the concrete escape region is empty. -/
@[simp] theorem escapeRegion_empty :
    input.escapeRegion oldInitialCut = ∅ := by
  ext x
  constructor
  · rintro ⟨E⟩
    have : E.route.finish ∈ input.lambda.target := E.target
    simpa [PopularAuxiliary.Input.lambda,
      PopularAuxiliary.Input.targetMarkers, input] using this
  · simp

theorem wholeFragment_blockingPoint_eq_b :
    GroundingCut.blockingPoint input oldInitialCut wholeFragment = b := by
  apply GroundingCut.blockingPoint_eq_terminal_of_not_meetsEscape
  · rintro ⟨x, _hx, hxEscape⟩
    simpa using hxEscape
  · rfl

theorem a_mem_BB : a ∈ GroundingCut.BB input oldInitialCut :=
  GroundingCut.CV_subset_BB input oldInitialCut a_mem_oldInitialCut_CV

theorem b_mem_BB : b ∈ GroundingCut.BB input oldInitialCut := by
  apply GroundingCut.BL_subset_BB input oldInitialCut
  exact ⟨wholeFragment,
    ⟨wholeFragment_mem_G0, Or.inr ⟨b, rfl⟩⟩,
    wholeFragment_blockingPoint_eq_b⟩

/-- The edge from the old cut point to the distinct blocking point survives
represented-edge deletion. -/
theorem ab_mem_residualEdges :
    (a, b) ∈ input.familyEdges \ GroundingCut.CE input oldInitialCut := by
  constructor
  · change (a, b) ∈ {e | ∃ p ∈ input.ladder.paths, e ∈ p.edgeSet}
    refine ⟨(Sum.inl ab : web.DPath), Set.mem_singleton _, ?_⟩
    change (a, b) ∈ ab.walk.edgeSet
    simp [ab, Walk.edgeSet]
  · rw [oldInitialCut_CE_empty]
    simp

/-- Checked refutation of the residual-base antichain.  This is precisely
the `CV`--then--`BL` case which the off-apex form of Assertion 8.21 does not
address. -/
theorem residualEdges_not_reachabilityAntichain :
    ¬ IsReachabilityAntichain
      (input.familyEdges \ GroundingCut.CE input oldInitialCut)
      (GroundingCut.BB input oldInitialCut) := by
  intro hanti
  have hab : a = b := hanti a_mem_BB b_mem_BB
    (Relation.ReflTransGen.single ab_mem_residualEdges)
  cases hab

end GroundingBBAntichainCounterexample
end Erdos599
