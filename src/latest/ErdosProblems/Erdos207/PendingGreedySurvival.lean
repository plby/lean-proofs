/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyTransferStructure
import ErdosProblems.Erdos207.SelectedAvailableUncoveredTransfer

/-!
# Pending triangles and uncovered edges in one greedy transition

For a prescribed packing `Q`, every still-pending triangle contributes its
three graph edges to the survival condition.  If `B` is disjoint from those
edges, the combined set has exactly `3 * |Q| + |B|` members.  Remaining
available after a greedy transition forces the selected choice to avoid all
three edges of every pending triangle, while survival of `B` forces it to
avoid `B`.  The sharp pair-star estimate can therefore be fed directly into
the selected/available/uncovered transfer recurrence.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Graph edges which must survive while `Q` is pending and `B` is required
to remain uncovered. -/
def pendingSurvivalEdges
    {V : Type*} [DecidableEq V]
    (Q : TripleSystemOn V) (B : Finset (Sym2 V)) : Finset (Sym2 V) :=
  Q.biUnion tripleEdgeFinset ∪ B

lemma not_isDiag_of_mem_tripleEdgeFinset
    {V : Type*} [DecidableEq V] {T : TripleOn V} {e : Sym2 V}
    (he : e ∈ tripleEdgeFinset T) : ¬ e.IsDiag := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [mk_mem_tripleEdgeFinset_iff] at he
      rw [Sym2.mk_isDiag_iff]
      exact he.2.2

/-- A packing has three distinct graph edges per triangle. -/
lemma card_biUnion_tripleEdgeFinset_of_isPackingOn
    {V : Type*} [Fintype V] [DecidableEq V]
    {Q : TripleSystemOn V} (hQ : IsPackingOn Q) :
    (Q.biUnion tripleEdgeFinset).card = 3 * Q.card := by
  rw [card_biUnion
    hQ.isTriangleDecomposition.pairwiseDisjoint_tripleEdgeFinset]
  simp [card_tripleEdgeFinset, mul_comm]

/-- The combined pending/residual edge set has the exponent used in the
transfer envelope. -/
lemma card_pendingSurvivalEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {Q : TripleSystemOn V} {B : Finset (Sym2 V)}
    (hQ : IsPackingOn Q)
    (hdisjoint : Disjoint (Q.biUnion tripleEdgeFinset) B) :
    (pendingSurvivalEdges Q B).card = 3 * Q.card + B.card := by
  rw [pendingSurvivalEdges, card_union_of_disjoint hdisjoint,
    card_biUnion_tripleEdgeFinset_of_isPackingOn hQ]

lemma pendingSurvivalEdges_offdiag
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : TripleSystemOn V) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, ¬ e.IsDiag) :
    ∀ e ∈ pendingSurvivalEdges Q B, ¬ e.IsDiag := by
  intro e he
  rw [pendingSurvivalEdges, mem_union] at he
  rcases he with heQ | heB
  · obtain ⟨T, _hTQ, heT⟩ := mem_biUnion.mp heQ
    exact not_isDiag_of_mem_tripleEdgeFinset heT
  · exact hB e heB

/-- If a prescribed triangle is still available after selecting `T`, then
its edge set is disjoint from the edge set of `T`. -/
lemma disjoint_tripleEdgeFinset_of_mem_greedyStep_available
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (T U : TripleOn V)
    (hU : U ∈ (greedyStep F S T).available) :
    Disjoint (tripleEdgeFinset U) (tripleEdgeFinset T) := by
  have hlegal : IsLegalExtension F (insert T S.chosen) U :=
    (mem_legalAvailable_iff.mp hU).2
  have hpacking : IsPackingOn (insert U (insert T S.chosen)) :=
    hlegal.2.1
  have hUneT : U ≠ T := by
    intro hUT
    subst U
    exact hlegal.1 (mem_insert_self T S.chosen)
  exact hpacking.isTriangleDecomposition.pairwiseDisjoint_tripleEdgeFinset
    (mem_insert_self U _) (mem_insert_of_mem (mem_insert_self T _)) hUneT

/-- Pending availability together with residual-edge survival forces the
chosen triangle to avoid their combined edge set. -/
lemma disjoint_pendingSurvivalEdges_of_step_event
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S : GreedyStateOn V) (T : TripleOn V)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V))
    (hB : B ⊆ greedyUncoveredEdges E S)
    (hevent : Q ⊆ (greedyStep F S T).available ∧
      B ⊆ greedyUncoveredEdges E (greedyStep F S T)) :
    Disjoint (pendingSurvivalEdges Q B) (tripleEdgeFinset T) := by
  have hBdisjoint : Disjoint B (tripleEdgeFinset T) :=
    (subset_greedyUncoveredEdges_step_iff_disjoint F E S T B hB).mp
      hevent.2
  rw [disjoint_left]
  intro e he eT
  rw [pendingSurvivalEdges, mem_union] at he
  rcases he with heQ | heB
  · obtain ⟨U, hUQ, heU⟩ := mem_biUnion.mp heQ
    exact disjoint_left.mp
      (disjoint_tripleEdgeFinset_of_mem_greedyStep_available
        F S T U (hevent.1 hUQ)) heU eT
  · exact disjoint_left.mp hBdisjoint heB eT

/-- Sharp one-step survival for pending prescribed triangles and residual
graph edges. -/
theorem greedyKernel_probability_pending_available_uncovered_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S : GreedyStateOn V) (Q : TripleSystemOn V)
    (B : Finset (Sym2 V)) (d : ℕ) (theta : ℝ≥0)
    (hA : S.available.Nonempty)
    (hQ : IsPackingOn Q)
    (hQB : Disjoint (Q.biUnion tripleEdgeFinset) B)
    (hBoffdiag : ∀ e ∈ B, ¬ e.IsDiag)
    (hB : B ⊆ greedyUncoveredEdges E S)
    (hsupply : ∀ e ∈ pendingSurvivalEdges Q B,
      d ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar :
      ((S.available.card -
          ((3 * Q.card + B.card) * d -
            (3 * Q.card + B.card).choose 2) : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤
        theta ^ (3 * Q.card + B.card)) :
    (greedyKernel F S).probability (fun S' ↦
        Q ⊆ S'.available ∧ B ⊆ greedyUncoveredEdges E S') ≤
      theta ^ (3 * Q.card + B.card) := by
  let C := pendingSurvivalEdges Q B
  have hcard : C.card = 3 * Q.card + B.card :=
    card_pendingSurvivalEdges hQ hQB
  have hraw := greedyKernel_probability_le_of_sharp_supply
    F S C (fun S' ↦
      Q ⊆ S'.available ∧ B ⊆ greedyUncoveredEdges E S')
    hA (fun T h ↦
      disjoint_pendingSurvivalEdges_of_step_event F E S T.1 Q B hB h)
    d (pendingSurvivalEdges_offdiag Q B hBoffdiag) hsupply theta
    (by simpa only [hcard] using hscalar)
  simpa only [hcard] using hraw

/-- The ordinary greedy kernel satisfies one complete transfer recurrence
at a state with nonempty availability, under the sharp local supply and
scalar hypotheses for the current pending family. -/
theorem greedyKernel_probability_selectedAvailableUncovered_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S₀ : GreedyStateOn V) (Q S : TripleSystemOn V)
    (B : Finset (Sym2 V)) (d : ℕ) (theta : ℝ≥0)
    (hSQ : S ⊆ Q)
    (hA : S₀.available.Nonempty)
    (hQ : IsPackingOn Q)
    (hQB : Disjoint (Q.biUnion tripleEdgeFinset) B)
    (hBoffdiag : ∀ e ∈ B, ¬ e.IsDiag)
    (hsupply : ∀ e ∈ pendingSurvivalEdges (Q \ S) B,
      d ≤ (greedyChoicesCoveringEdge S₀ e).card)
    (hscalar :
      ((S₀.available.card -
          ((3 * (Q \ S).card + B.card) * d -
            (3 * (Q \ S).card + B.card).choose 2) : ℕ) : ℝ≥0) *
          (S₀.available.card : ℝ≥0)⁻¹ ≤
        theta ^ (3 * (Q \ S).card + B.card)) :
    (greedyKernel F S₀).probability
        (SelectedAvailableUncoveredEvent
          (fun R : GreedyStateOn V ↦ R.chosen)
          (fun R ↦ R.available) (greedyUncoveredEdges E)
          Q S B) ≤
      theta ^ (3 * (Q \ S).card + B.card) *
          nnrealIndicator
            (SelectedAvailableUncoveredEvent
              (fun R : GreedyStateOn V ↦ R.chosen)
              (fun R ↦ R.available) (greedyUncoveredEdges E)
              Q S B S₀) +
        ∑ x ∈ S, nnrealIndicatorMul
          (SelectedAvailableUncoveredEvent
            (fun R : GreedyStateOn V ↦ R.chosen)
            (fun R ↦ R.available) (greedyUncoveredEdges E)
            Q (S.erase x) B S₀)
          (S₀.available.card : ℝ≥0)⁻¹ := by
  apply kernel_probability_selectedAvailableUncovered_le
    (greedyKernel F)
    (fun R : GreedyStateOn V ↦ R.chosen)
    (fun R ↦ R.available) (greedyUncoveredEdges E)
    (S₀.available.card : ℝ≥0)⁻¹ theta S₀
    (greedyKernel_monotone_singleInsertion F S₀)
    (greedyKernel_antitone_available F S₀)
    (fun R hmass ↦ greedyUncoveredEdges_antitone E
      ((greedyKernel_monotone_singleInsertion F S₀ R hmass).1))
    (greedyKernel_newChosen_subset_available F S₀)
    Q S hSQ B
  · intro hevent
    have hPendingPacking : IsPackingOn (Q \ S) :=
      hQ.mono (sdiff_subset.trans Subset.rfl)
    have hEdgeSubset :
        (Q \ S).biUnion tripleEdgeFinset ⊆
          Q.biUnion tripleEdgeFinset := by
      intro e he
      obtain ⟨T, hT, heT⟩ := mem_biUnion.mp he
      exact mem_biUnion.mpr ⟨T, (mem_sdiff.mp hT).1, heT⟩
    have hPendingB :
        Disjoint ((Q \ S).biUnion tripleEdgeFinset) B :=
      hQB.mono_left hEdgeSubset
    exact greedyKernel_probability_pending_available_uncovered_le
      F E S₀ (Q \ S) B d theta hA hPendingPacking hPendingB
      hBoffdiag hevent.2.2.2.2 hsupply hscalar
  · intro x hxS _hevent hxnot
    exact ((greedyKernel F S₀).probability_mono
      (fun _ h ↦ h.1)).trans
        (greedyKernel_probability_new_triangle_le F S₀ x
          S₀.available.card (card_pos.mpr hA) le_rfl hxnot)

end

end Erdos207
