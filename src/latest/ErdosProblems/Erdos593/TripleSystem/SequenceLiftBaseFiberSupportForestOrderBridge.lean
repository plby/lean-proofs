import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportForestOrder
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportOverlapGraph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From acyclic support-overlap graphs to base-fibre running orders

This module transports a finite forest leaf-elimination order of active base
nodes to the tail-degree-one support order used by the base-fibre assembly
theorems.  Its hypothesis is deliberately graph-theoretic: pairwise
linearity alone does not imply support-overlap acyclicity.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A tail-degree-one order in the active support-overlap graph gives the
corresponding tail-degree-one order of the underlying canonical base nodes. -/
theorem baseFiberSupportTailAtMostOneNeighbor_of_overlapGraphTailOrder
    {S : Set (Edge G)} {qs : List (activeBaseNodeIndex S)}
    (hnodup : qs.Nodup)
    (htail : (baseFiberSupportOverlapGraph S).tailAtMostOneNeighbor qs) :
    baseFiberSupportTailAtMostOneNeighbor S (qs.map Subtype.val) := by
  induction qs with
  | nil =>
      trivial
  | cons q qs ih =>
      change (baseFiberSupportOverlapGraph S).tailAtMostOneNeighbor qs ∧ _ at htail
      rcases htail with ⟨htailTail, htailHead⟩
      rw [List.map_cons]
      refine ⟨ih (List.nodup_cons.mp hnodup).2 htailTail, ?_⟩
      intro u hu v hv hqu hqv
      rcases List.mem_map.1 hu with ⟨u', hu', rfl⟩
      rcases List.mem_map.1 hv with ⟨v', hv', rfl⟩
      change baseFiberSupportOverlap S q.1 u'.1 at hqu
      change baseFiberSupportOverlap S q.1 v'.1 at hqv
      have hquNe : q ≠ u' := by
        intro hEq
        apply (List.nodup_cons.mp hnodup).1
        simpa [hEq] using! hu'
      have hqvNe : q ≠ v' := by
        intro hEq
        apply (List.nodup_cons.mp hnodup).1
        simpa [hEq] using! hv'
      have hquAdj : (baseFiberSupportOverlapGraph S).Adj q u' :=
        baseFiberSupportOverlapGraph_adj_iff.mpr ⟨hquNe, hqu⟩
      have hqvAdj : (baseFiberSupportOverlapGraph S).Adj q v' :=
        baseFiberSupportOverlapGraph_adj_iff.mpr ⟨hqvNe, hqv⟩
      exact congrArg Subtype.val (htailHead u' hu' v' hv' hquAdj hqvAdj)

/-- If the finite active base-fibre support-overlap graph is acyclic, then
the selected family admits a noduplicated base-node cover with tail support
degree at most one.  The order is existential; this theorem makes no claim
about the fixed canonical active-base enumeration. -/
theorem exists_baseFiberSupportTailAtMostOneNeighbor_order_of_supportOverlapAcyclic
    {S : Set (Edge G)} (hS : S.Finite)
    (hacyclic : (baseFiberSupportOverlapGraph S).IsAcyclic) :
    ∃ nodes : List (Node G),
      nodes.Nodup ∧
        (∀ e, e ∈ S → baseNode e ∈ nodes) ∧
        baseFiberSupportTailAtMostOneNeighbor S nodes := by
  classical
  letI : Fintype (activeBaseNodeIndex S) := activeBaseNodeIndexFintype hS
  obtain ⟨qs, hnodup, hqs, htail⟩ :=
    hacyclic.exists_tailAtMostOneNeighborOrder
  refine ⟨qs.map Subtype.val, hnodup.map Subtype.val_injective, ?_, ?_⟩
  · intro e he
    let q : activeBaseNodeIndex S := ⟨baseNode e, ⟨e, he, rfl⟩⟩
    have hqmemFinset : q ∈ qs.toFinset := by
      rw [hqs]
      exact Finset.mem_univ q
    have hqmem : q ∈ qs := List.mem_toFinset.mp hqmemFinset
    change q.1 ∈ qs.map Subtype.val
    exact List.mem_map_of_mem hqmem
  · exact baseFiberSupportTailAtMostOneNeighbor_of_overlapGraphTailOrder hnodup htail

end SequenceLift

end Erdos593
