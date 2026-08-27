/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeGreedyCover
import ErdosProblems.Erdos207.SelectedUncoveredJointInclusion
import ErdosProblems.Erdos207.StoppedGreedyJointInclusion

/-!
# Selected triangles and uncovered edges in the stopped greedy process

This is the concrete bridge from the abstract mixed recurrence to the
preliminary KSSS process.  The chosen family grows monotonically, so the set
of prescribed ambient graph edges not covered by it shrinks monotonically.
The only quantitative input left to a preliminary-process application is the
one-step survival estimate for a prescribed set of currently uncovered
edges.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Edges from a fixed ambient family which have not yet been covered by the
chosen triples of a greedy state. -/
def greedyUncoveredEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (S : GreedyStateOn V) : Finset (Sym2 V) :=
  E \ graphEdges (coveredGraph S.chosen)

lemma graphEdges_coveredGraph_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {P Q : TripleSystemOn V} (hPQ : P ⊆ Q) :
    graphEdges (coveredGraph P) ⊆ graphEdges (coveredGraph Q) := by
  intro e he
  rw [mem_graphEdges_iff] at he ⊢
  exact SimpleGraph.edgeSet_mono (coveredGraph_mono hPQ) he

lemma greedyUncoveredEdges_antitone
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) {S S' : GreedyStateOn V}
    (hSS' : S.chosen ⊆ S'.chosen) :
    greedyUncoveredEdges E S' ⊆ greedyUncoveredEdges E S := by
  intro e he
  rw [greedyUncoveredEdges, mem_sdiff] at he ⊢
  exact ⟨he.1, fun heOld ↦ he.2
    (graphEdges_coveredGraph_mono hSS' heOld)⟩

/-- The threshold-stopped greedy kernel can only remove edges from the
uncovered set. -/
theorem stoppedGreedyKernel_antitone_uncovered
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) (E : Finset (Sym2 V)) :
    IsAntitoneSetKernel (stoppedGreedyKernel F D)
      (greedyUncoveredEdges E) := by
  intro S S' hmass
  exact greedyUncoveredEdges_antitone E
    ((stoppedGreedyKernel_monotone_singleInsertion F D S) S' hmass).1

/-- A one-point insertion bound also bounds the simultaneous event that the
point is inserted and a prescribed edge family survives. -/
theorem stoppedGreedyKernel_probability_new_and_uncovered_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) (hD : 0 < D)
    (E : Finset (Sym2 V)) (S : GreedyStateOn V) (T : TripleOn V)
    (hTnot : T ∉ S.chosen) (B : Finset (Sym2 V)) :
    (stoppedGreedyKernel F D S).probability (fun S' ↦
        T ∈ S'.chosen ∧ B ⊆ greedyUncoveredEdges E S') ≤
      (D : ℝ≥0)⁻¹ := by
  exact ((stoppedGreedyKernel F D S).probability_mono
    (fun _ h ↦ h.1)).trans
      (stoppedGreedyKernel_probability_new_triangle_le
        F D hD S T hTnot)

/-- Mixed selected/uncovered estimate for the concrete stopped constrained
greedy law.  The survival premise is exactly the local estimate proved from
the regularized preliminary hypergraph in the KSSS application. -/
theorem stoppedGreedyProcess_probability_selectedUncovered_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel : ℕ) (hD : 0 < D)
    (theta : ℝ≥0) (E : Finset (Sym2 V)) (S₀ : GreedyStateOn V)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V))
    (hQ : Disjoint Q S₀.chosen)
    (hB : B ⊆ greedyUncoveredEdges E S₀)
    (hsurvive : ∀ S B, B ⊆ greedyUncoveredEdges E S →
      (stoppedGreedyKernel F D S).probability
          (fun S' ↦ B ⊆ greedyUncoveredEdges E S') ≤
        theta ^ B.card) :
    (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        Q ⊆ S.chosen ∧ B ⊆ greedyUncoveredEdges E S) ≤
      selectedUncoveredEnvelope (D : ℝ≥0)⁻¹ theta B.card fuel Q.card := by
  exact iterateKernel_probability_selectedUncovered_le
    (stoppedGreedyKernel F D)
    (fun S : GreedyStateOn V ↦ S.chosen)
    (greedyUncoveredEdges E)
    (D : ℝ≥0)⁻¹ theta
    (stoppedGreedyKernel_monotone_singleInsertion F D)
    (stoppedGreedyKernel_antitone_uncovered F D E)
    hsurvive
    (fun S T hT B _hB ↦
      stoppedGreedyKernel_probability_new_and_uncovered_le
        F D hD E S T hT B)
    S₀ Q B hQ hB fuel

/-- Product-form specialization matching the two multiplicative factors in
KSSS (8.7). -/
theorem stoppedGreedyProcess_probability_selectedUncovered_le_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel : ℕ) (hD : 0 < D)
    (theta alpha eta : ℝ≥0)
    (E : Finset (Sym2 V)) (S₀ : GreedyStateOn V)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V))
    (hQ : Disjoint Q S₀.chosen)
    (hB : B ⊆ greedyUncoveredEdges E S₀)
    (hsurvive : ∀ S B, B ⊆ greedyUncoveredEdges E S →
      (stoppedGreedyKernel F D S).probability
          (fun S' ↦ B ⊆ greedyUncoveredEdges E S') ≤
        theta ^ B.card)
    (hselected : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : theta ^ (fuel - Q.card) ≤ eta) :
    (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        Q ⊆ S.chosen ∧ B ⊆ greedyUncoveredEdges E S) ≤
      alpha ^ Q.card * eta ^ B.card := by
  exact (stoppedGreedyProcess_probability_selectedUncovered_le
    F D fuel hD theta E S₀ Q B hQ hB hsurvive).trans
      (selectedUncoveredEnvelope_le_product
        (D : ℝ≥0)⁻¹ theta alpha eta B.card fuel Q.card
        hselected hsurvived)

end

end Erdos207
