/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ExclusiveAbsorbers
import ErdosProblems.Erdos207.GreedySelectedUncovered

/-!
# Uncovered-edge survival in the threshold-stopped greedy process

The preliminary KSSS estimate applies its multiplicative survival estimate
only while the scheduled availability floor is valid. Accordingly the
tracked residual set is the genuine uncovered set at active states and the
empty set after stopping. This makes stopping an explicit failure event and
keeps the mixed recurrence valid without an impossible contraction claim at
a frozen state.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

lemma graphEdges_eq_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    graphEdges G = G.edgeFinset := by
  ext e
  simp only [mem_graphEdges_iff, SimpleGraph.mem_edgeFinset]

/-- Inserting one triangle preserves a currently uncovered prescribed edge
set exactly when the triangle contains none of those edges. -/
lemma subset_greedyUncoveredEdges_step_iff_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S : GreedyStateOn V) (T : TripleOn V) (B : Finset (Sym2 V))
    (hB : B ⊆ greedyUncoveredEdges E S) :
    B ⊆ greedyUncoveredEdges E (greedyStep F S T) ↔
      Disjoint B (tripleEdgeFinset T) := by
  constructor
  · intro hsurvive
    apply disjoint_left.mpr
    intro e heB heT
    have heUncovered := hsurvive heB
    have heCovered : e ∈ graphEdges
        (coveredGraph (greedyStep F S T).chosen) := by
      rw [graphEdges_eq_edgeFinset,
        coveredGraph_edgeFinset_eq_biUnion]
      simp only [greedyStep, mem_biUnion, mem_insert]
      exact ⟨T, Or.inl rfl, heT⟩
    exact (mem_sdiff.mp heUncovered).2 heCovered
  · intro hdisjoint e heB
    have heOld := hB heB
    rw [greedyUncoveredEdges, mem_sdiff] at heOld ⊢
    refine ⟨heOld.1, ?_⟩
    intro heCovered
    rw [graphEdges_eq_edgeFinset,
      coveredGraph_edgeFinset_eq_biUnion] at heCovered
    simp only [greedyStep, mem_biUnion, mem_insert] at heCovered
    obtain ⟨Q, hQ, heQ⟩ := heCovered
    rcases hQ with rfl | hQS
    · exact disjoint_left.mp hdisjoint heB heQ
    · exact heOld.2 (by
        rw [graphEdges_eq_edgeFinset,
          coveredGraph_edgeFinset_eq_biUnion]
        exact mem_biUnion.mpr ⟨Q, hQS, heQ⟩)

/-- Exact finite set of active choices which leave `B` uncovered. -/
def greedySurvivalChoices
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S : GreedyStateOn V) (B : Finset (Sym2 V)) :
    Finset S.available := by
  classical
  exact Finset.univ.filter fun T ↦
    B ⊆ greedyUncoveredEdges E (greedyStep F S T.1)

/-- Exact uniform probability of retaining a prescribed set of uncovered
edges during one active ordinary greedy step. -/
theorem greedyKernel_probability_uncovered_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S : GreedyStateOn V) (B : Finset (Sym2 V))
    (hA : S.available.Nonempty) :
    (greedyKernel F S).probability
        (fun S' ↦ B ⊆ greedyUncoveredEdges E S') =
      ((greedySurvivalChoices F E S B).card : ℝ≥0) *
        (S.available.card : ℝ≥0)⁻¹ := by
  classical
  letI : Nonempty S.available :=
    ⟨⟨hA.choose, hA.choose_spec⟩⟩
  let next : S.available → GreedyStateOn V :=
    fun T ↦ greedyStep F S T.1
  simp only [greedyKernel, hA]
  change (FiniteLaw.map next
    (FiniteLaw.uniform : FiniteLaw S.available)).probability
      (fun S' ↦ B ⊆ greedyUncoveredEdges E S') = _
  rw [FiniteLaw.probability_map,
    FiniteLaw.uniform_probability_eq_card_filter]
  change ((Finset.univ.filter fun T : S.available ↦
      B ⊆ greedyUncoveredEdges E (greedyStep F S T.1)).card : ℝ≥0) *
      (Fintype.card S.available : ℝ≥0)⁻¹ = _
  simp only [greedySurvivalChoices, Fintype.card_coe]

/-- Available choices which cover at least one edge of `B`. -/
def greedyCoveringChoices
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (B : Finset (Sym2 V)) :
    Finset S.available := by
  classical
  exact Finset.univ.filter fun T ↦
    ¬ Disjoint B (tripleEdgeFinset T.1)

lemma greedySurvivalChoices_eq_filter_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S : GreedyStateOn V) (B : Finset (Sym2 V))
    (hB : B ⊆ greedyUncoveredEdges E S) :
    greedySurvivalChoices F E S B =
      Finset.univ.filter fun T : S.available ↦
        Disjoint B (tripleEdgeFinset T.1) := by
  ext T
  simp only [greedySurvivalChoices, mem_filter, mem_univ, true_and]
  exact subset_greedyUncoveredEdges_step_iff_disjoint
    F E S T.1 B hB

/-- Safe and covering choices partition the current availability. -/
lemma card_greedySurvivalChoices_add_coveringChoices
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S : GreedyStateOn V) (B : Finset (Sym2 V))
    (hB : B ⊆ greedyUncoveredEdges E S) :
    (greedySurvivalChoices F E S B).card +
        (greedyCoveringChoices S B).card = S.available.card := by
  rw [greedySurvivalChoices_eq_filter_disjoint F E S B hB]
  change (Finset.univ.filter fun T : S.available ↦
      Disjoint B (tripleEdgeFinset T.1)).card +
    (Finset.univ.filter fun T : S.available ↦
      ¬ Disjoint B (tripleEdgeFinset T.1)).card = _
  rw [Finset.card_filter_add_card_filter_not]
  exact Fintype.card_coe S.available

/-- A lower bound on choices covering `B`, together with the corresponding
scalar inequality, gives the active survival estimate. -/
theorem greedySurvivalChoices_ratio_le_of_covering
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (E : Finset (Sym2 V))
    (S : GreedyStateOn V) (B : Finset (Sym2 V))
    (hB : B ⊆ greedyUncoveredEdges E S)
    (loss : ℕ) (hloss : loss ≤ (greedyCoveringChoices S B).card)
    (theta : ℝ≥0)
    (hscalar : ((S.available.card - loss : ℕ) : ℝ≥0) *
        (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card) :
    ((greedySurvivalChoices F E S B).card : ℝ≥0) *
        (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card := by
  have hpartition :=
    card_greedySurvivalChoices_add_coveringChoices F E S B hB
  have hcard : (greedySurvivalChoices F E S B).card ≤
      S.available.card - loss := by omega
  have hcast : ((greedySurvivalChoices F E S B).card : ℝ≥0) ≤
      (S.available.card - loss : ℕ) := by
    exact_mod_cast hcard
  have hmul := mul_le_mul_left hcast
    (S.available.card : ℝ≥0)⁻¹
  have hmul' : ((greedySurvivalChoices F E S B).card : ℝ≥0) *
      (S.available.card : ℝ≥0)⁻¹ ≤
        (S.available.card - loss : ℕ) *
          (S.available.card : ℝ≥0)⁻¹ := by
    simpa only [mul_comm] using hmul
  exact hmul'.trans hscalar

/-- Residual edges are tracked only above the stopping threshold. -/
def stoppedGreedyTrackedUncoveredEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : ℕ) (E : Finset (Sym2 V)) (S : GreedyStateOn V) :
    Finset (Sym2 V) :=
  if D ≤ S.available.card then greedyUncoveredEdges E S else ∅

/-- The activity-gated residual set is antitone along every stopped greedy
transition, including the transition at which the floor is lost. -/
theorem stoppedGreedyKernel_antitone_trackedUncovered
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) (E : Finset (Sym2 V)) :
    IsAntitoneSetKernel (stoppedGreedyKernel F D)
      (stoppedGreedyTrackedUncoveredEdges D E) := by
  classical
  intro S
  by_cases hactive : D ≤ S.available.card
  · unfold stoppedGreedyKernel
    rw [if_pos hactive]
    intro S' hmass
    by_cases hnext : D ≤ S'.available.card
    · simp only [stoppedGreedyTrackedUncoveredEdges,
        if_pos hactive, if_pos hnext]
      exact greedyUncoveredEdges_antitone E
        ((greedyKernel_monotone_singleInsertion F S) S' hmass).1
    · simp [stoppedGreedyTrackedUncoveredEdges, hnext]
  · unfold stoppedGreedyKernel
    rw [if_neg hactive]
    intro S' hmass
    have hS' : S' = S := by
      have hpos : 0 < (FiniteLaw.pure S).mass S' := hmass
      simp only [FiniteLaw.pure_mass] at hpos
      by_cases heq : S' = S
      · exact heq
      · simp [heq] at hpos
    subst S'
    exact Subset.rfl

/-- A cardinal bound on the active safe-choice set supplies the uniform
one-step survival factor for the activity-gated stopped process. -/
theorem stoppedGreedyKernel_probability_trackedUncovered_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) (hD : 0 < D)
    (E : Finset (Sym2 V)) (theta : ℝ≥0)
    (hchoices : ∀ S B,
      D ≤ S.available.card → B ⊆ greedyUncoveredEdges E S →
      ((greedySurvivalChoices F E S B).card : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (S : GreedyStateOn V) (B : Finset (Sym2 V))
    (hB : B ⊆ stoppedGreedyTrackedUncoveredEdges D E S) :
    (stoppedGreedyKernel F D S).probability (fun S' ↦
        B ⊆ stoppedGreedyTrackedUncoveredEdges D E S') ≤
      theta ^ B.card := by
  classical
  by_cases hactive : D ≤ S.available.card
  · have hA : S.available.Nonempty := card_pos.mp (lt_of_lt_of_le hD hactive)
    have hBactual : B ⊆ greedyUncoveredEdges E S := by
      simpa [stoppedGreedyTrackedUncoveredEdges, hactive] using hB
    unfold stoppedGreedyKernel
    rw [if_pos hactive]
    calc
      (greedyKernel F S).probability (fun S' ↦
          B ⊆ stoppedGreedyTrackedUncoveredEdges D E S') ≤
          (greedyKernel F S).probability (fun S' ↦
            B ⊆ greedyUncoveredEdges E S') := by
        apply (greedyKernel F S).probability_mono
        intro S' htracked
        by_cases hnext : D ≤ S'.available.card
        · simpa [stoppedGreedyTrackedUncoveredEdges, hnext] using htracked
        · have hBempty : B = ∅ := by
            have : B ⊆ (∅ : Finset (Sym2 V)) := by
              simpa [stoppedGreedyTrackedUncoveredEdges, hnext] using htracked
            exact subset_empty.mp this
          simp [hBempty]
      _ = ((greedySurvivalChoices F E S B).card : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ :=
        greedyKernel_probability_uncovered_eq F E S B hA
      _ ≤ theta ^ B.card := hchoices S B hactive hBactual
  · have hBempty : B = ∅ := by
      have : B ⊆ (∅ : Finset (Sym2 V)) := by
        simpa [stoppedGreedyTrackedUncoveredEdges, hactive] using hB
      exact subset_empty.mp this
    subst B
    simp [FiniteLaw.probability_true]

/-- Complete product estimate for the stopped preliminary trajectory, with
the threshold-loss trajectories removed from the tracked residual event. -/
theorem stoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel : ℕ) (hD : 0 < D)
    (theta alpha eta : ℝ≥0) (E : Finset (Sym2 V))
    (S₀ : GreedyStateOn V) (Q : TripleSystemOn V)
    (B : Finset (Sym2 V))
    (hactive₀ : D ≤ S₀.available.card)
    (hQ : Disjoint Q S₀.chosen)
    (hB : B ⊆ greedyUncoveredEdges E S₀)
    (hchoices : ∀ S B,
      D ≤ S.available.card → B ⊆ greedyUncoveredEdges E S →
      ((greedySurvivalChoices F E S B).card : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (hselected : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : theta ^ (fuel - Q.card) ≤ eta) :
    (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        Q ⊆ S.chosen ∧
          B ⊆ stoppedGreedyTrackedUncoveredEdges D E S) ≤
      alpha ^ Q.card * eta ^ B.card := by
  have hBtracked :
      B ⊆ stoppedGreedyTrackedUncoveredEdges D E S₀ := by
    simpa [stoppedGreedyTrackedUncoveredEdges, hactive₀] using hB
  have hraw := iterateKernel_probability_selectedUncovered_le
    (stoppedGreedyKernel F D)
    (fun S : GreedyStateOn V ↦ S.chosen)
    (stoppedGreedyTrackedUncoveredEdges D E)
    (D : ℝ≥0)⁻¹ theta
    (stoppedGreedyKernel_monotone_singleInsertion F D)
    (stoppedGreedyKernel_antitone_trackedUncovered F D E)
    (stoppedGreedyKernel_probability_trackedUncovered_le
      F D hD E theta hchoices)
    (fun S T hT B _hB ↦ by
      refine ((stoppedGreedyKernel F D S).probability_mono
        (fun S' h ↦ ⟨h.1, ?_⟩)).trans
          (stoppedGreedyKernel_probability_new_and_uncovered_le
            F D hD E S T hT B)
      by_cases hnext : D ≤ S'.available.card
      · simpa [stoppedGreedyTrackedUncoveredEdges, hnext] using h.2
      · have hBempty : B = ∅ := by
          have : B ⊆ (∅ : Finset (Sym2 V)) := by
            simpa [stoppedGreedyTrackedUncoveredEdges, hnext] using h.2
          exact subset_empty.mp this
        simp [hBempty])
    S₀ Q B hQ hBtracked fuel
  exact hraw.trans (selectedUncoveredEnvelope_le_product
    (D : ℝ≥0)⁻¹ theta alpha eta B.card fuel Q.card
    hselected hsurvived)

/-- A genuine residual-edge event is contained in the union of the
activity-gated residual event and terminal threshold failure.  This is the
precise finite-probability form of the additive stopping-error split in
KSSS (8.7). -/
theorem stoppedGreedyProcess_probability_selectedUncovered_le_tracked_add_inactive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel : ℕ)
    (E : Finset (Sym2 V)) (S₀ : GreedyStateOn V)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V)) :
    (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        Q ⊆ S.chosen ∧ B ⊆ greedyUncoveredEdges E S) ≤
      (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
          Q ⊆ S.chosen ∧
            B ⊆ stoppedGreedyTrackedUncoveredEdges D E S) +
        (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
          ¬ D ≤ S.available.card) := by
  let L := stoppedGreedyProcessLaw F D fuel S₀
  calc
    L.probability (fun S ↦
        Q ⊆ S.chosen ∧ B ⊆ greedyUncoveredEdges E S) ≤
        L.probability (fun S ↦
          (Q ⊆ S.chosen ∧
            B ⊆ stoppedGreedyTrackedUncoveredEdges D E S) ∨
          ¬ D ≤ S.available.card) := by
      apply L.probability_mono
      intro S h
      by_cases hactive : D ≤ S.available.card
      · left
        exact ⟨h.1, by
          simpa [stoppedGreedyTrackedUncoveredEdges, hactive] using h.2⟩
      · exact Or.inr hactive
    _ ≤ L.probability (fun S ↦
          Q ⊆ S.chosen ∧
            B ⊆ stoppedGreedyTrackedUncoveredEdges D E S) +
        L.probability (fun S ↦ ¬ D ≤ S.available.card) :=
      L.probability_or_le _ _

/-- Product estimate for the genuine residual set, with premature stopping
kept as a separate additive error. -/
theorem stoppedGreedyProcess_probability_selectedUncovered_le_product_add_inactive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel : ℕ) (hD : 0 < D)
    (theta alpha eta epsilon : ℝ≥0) (E : Finset (Sym2 V))
    (S₀ : GreedyStateOn V) (Q : TripleSystemOn V)
    (B : Finset (Sym2 V))
    (hactive₀ : D ≤ S₀.available.card)
    (hQ : Disjoint Q S₀.chosen)
    (hB : B ⊆ greedyUncoveredEdges E S₀)
    (hchoices : ∀ S B,
      D ≤ S.available.card → B ⊆ greedyUncoveredEdges E S →
      ((greedySurvivalChoices F E S B).card : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (hselected : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : theta ^ (fuel - Q.card) ≤ eta)
    (hinactive :
      (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        ¬ D ≤ S.available.card) ≤ epsilon) :
    (stoppedGreedyProcessLaw F D fuel S₀).probability (fun S ↦
        Q ⊆ S.chosen ∧ B ⊆ greedyUncoveredEdges E S) ≤
      alpha ^ Q.card * eta ^ B.card + epsilon := by
  exact (stoppedGreedyProcess_probability_selectedUncovered_le_tracked_add_inactive
    F D fuel E S₀ Q B).trans <| add_le_add
      (stoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
        F D fuel hD theta alpha eta E S₀ Q B hactive₀ hQ hB
          hchoices hselected hsurvived)
      hinactive

end

end Erdos207
