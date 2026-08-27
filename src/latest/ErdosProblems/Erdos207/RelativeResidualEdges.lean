/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternal

/-!
# Residual edge families relative to an old packing

At a later master stage the current graph lies in the leave of the old
packing.  Consequently the old packing covers none of the graph edges, and
deleting it from a larger selected family does not change any of the
residual graph-edge families.  These identities let the preliminary/internal
product estimate charge only genuinely new triangles while its scheduled
edges are still computed from the full current packing.
-/

namespace Erdos207

open Finset

noncomputable section

/-- On an edge of `G`, coverage by `Q` is equivalent to coverage by the
genuinely new part `Q \ P` whenever `G` lies in the leave of `P`. -/
lemma mem_graphEdges_coveredGraph_iff_sdiff_of_le_leaveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {P Q : TripleSystemOn V} {e : Sym2 V}
    (hGleave : G ≤ leaveGraph P) (heG : e ∈ graphEdges G) :
    e ∈ graphEdges (coveredGraph Q) ↔
      e ∈ graphEdges (coveredGraph (Q \ P)) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hG : G.Adj u v := mem_graphEdges_iff.mp heG
      constructor
      · intro hcovered
        obtain ⟨T, hTQ, huT, hvT, huv⟩ :=
          coveredGraph_adj.mp (mem_graphEdges_iff.mp hcovered)
        have hTP : T ∉ P := by
          intro hTP
          exact (leaveGraph_adj.mp (hGleave hG)).2
            ⟨T, hTP, huT, hvT, huv⟩
        exact mem_graphEdges_iff.mpr <| coveredGraph_adj.mpr
          ⟨T, mem_sdiff.mpr ⟨hTQ, hTP⟩, huT, hvT, huv⟩
      · intro hcovered
        obtain ⟨T, hT, huT, hvT, huv⟩ :=
          coveredGraph_adj.mp (mem_graphEdges_iff.mp hcovered)
        exact mem_graphEdges_iff.mpr <| coveredGraph_adj.mpr
          ⟨T, (mem_sdiff.mp hT).1, huT, hvT, huv⟩

/-- Removing an old packing from the selected family does not change the
residual outer edges of its leave graph. -/
lemma preliminaryResidualOuterEdges_sdiff_eq_of_le_leaveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P Q : TripleSystemOn V}
    (hGleave : G ≤ leaveGraph P) :
    preliminaryResidualOuterEdges G U Q =
      preliminaryResidualOuterEdges G U (Q \ P) := by
  ext e
  simp only [preliminaryResidualOuterEdges, mem_sdiff]
  by_cases he : e ∈ outerGraphEdges G U
  · have heG : e ∈ graphEdges G := (mem_outerGraphEdges_iff.mp he).1
    simp only [he, true_and]
    exact not_congr
      (mem_graphEdges_coveredGraph_iff_sdiff_of_le_leaveGraph hGleave heG)
  · simp only [he, false_and]

/-- The same relative identity for the residual internal schedule. -/
lemma preliminaryResidualInternalEdges_sdiff_eq_of_le_leaveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P Q : TripleSystemOn V}
    (hGleave : G ≤ leaveGraph P) :
    preliminaryResidualInternalEdges G U Q =
      preliminaryResidualInternalEdges G U (Q \ P) := by
  unfold preliminaryResidualInternalEdges
  rw [preliminaryResidualOuterEdges_sdiff_eq_of_le_leaveGraph hGleave]

/-- In particular, a disjoint new family may replace the difference. -/
lemma preliminaryResidualOuterEdges_union_eq_of_le_leaveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P M : TripleSystemOn V}
    (hGleave : G ≤ leaveGraph P) (hdisjoint : Disjoint P M) :
    preliminaryResidualOuterEdges G U (P ∪ M) =
      preliminaryResidualOuterEdges G U M := by
  rw [preliminaryResidualOuterEdges_sdiff_eq_of_le_leaveGraph hGleave]
  rw [union_sdiff_cancel_left hdisjoint]

lemma preliminaryResidualInternalEdges_union_eq_of_le_leaveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {P M : TripleSystemOn V}
    (hGleave : G ≤ leaveGraph P) (hdisjoint : Disjoint P M) :
    preliminaryResidualInternalEdges G U (P ∪ M) =
      preliminaryResidualInternalEdges G U M := by
  unfold preliminaryResidualInternalEdges
  rw [preliminaryResidualOuterEdges_union_eq_of_le_leaveGraph
    hGleave hdisjoint]

/-- The augmented crossing reserve can likewise be computed from only the
new part of a disjoint extension. -/
lemma preliminaryAugmentedReserve_union_eq_of_le_leaveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {sampled : Finset (Sym2 V)}
    {P M : TripleSystemOn V}
    (hGleave : G ≤ leaveGraph P) (hdisjoint : Disjoint P M) :
    preliminaryAugmentedReserve G U sampled (P ∪ M) =
      preliminaryAugmentedReserve G U sampled M := by
  unfold preliminaryAugmentedReserve
  rw [preliminaryResidualCrossingEdges_sdiff_eq_of_le_leaveGraph hGleave]
  rw [union_sdiff_cancel_left hdisjoint]

end

end Erdos207
