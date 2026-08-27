/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportRestrictedSelectedUncovered
import ErdosProblems.Erdos207.TimedStoppedJointInclusion
import ErdosProblems.Erdos207.GreedyCoveringChoiceCount

/-!
# Mixed selection and residual survival for a timed active greedy law

This module connects the support-restricted abstract recurrence to the
clocked stopping process used by the KSSS preliminary phase.  An auxiliary
invariant may carry the local extension-supply facts which hold only on
reachable states.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Uncovered ambient edges are tracked only while the clocked process is
active.  On a stopped state the tracked set is empty, so failure of an
active condition can later be charged as an additive exceptional event. -/
def timedActiveTrackedUncoveredEdges
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (active : ℕ → GreedyStateOn V → Prop)
    (E : Finset (Sym2 V))
    (z : FiniteLaw.TimedState (GreedyStateOn V) n) : Finset (Sym2 V) := by
  classical
  exact if active z.1.1 z.2 then greedyUncoveredEdges E z.2 else ∅

/-- Reachable timed states stay below the external evolution clock and
retain the chosen auxiliary invariant. -/
def TimedGreedyReachable
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (Inv : GreedyStateOn V → Prop) (i : ℕ)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n) : Prop :=
  z.1.1 ≤ i ∧ Inv z.2

theorem timedStoppedGreedyKernel_supported_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (Inv : GreedyStateOn V → Prop)
    (hInv : ∀ j, j < n → ∀ S, Inv S → active j S →
      (greedyKernel F S).SupportedOn Inv)
    (i : ℕ) (hi : i < n)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n)
    (hz : TimedGreedyReachable Inv i z) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).SupportedOn
      (TimedGreedyReachable Inv (i + 1)) := by
  classical
  change z.1.1 ≤ i ∧ Inv z.2 at hz
  unfold FiniteLaw.timedStoppedKernel
  split_ifs with hrun
  · exact (hInv z.1.1 hrun.1 z.2 hz.2 hrun.2).map
      (fun S' ↦ (FiniteLaw.advanceTime z.1 hrun.1, S'))
      (fun S' hS' ↦ ⟨by
        simp only [FiniteLaw.advanceTime_val]
        omega, hS'⟩)
  · exact FiniteLaw.supportedOn_pure _ ⟨hz.1.trans (by omega), hz.2⟩

theorem timedStoppedGreedyKernel_antitone_activeTracked_of_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (E : Finset (Sym2 V)) (Inv : GreedyStateOn V → Prop)
    (i : ℕ) (hi : i < n)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n)
    (hz : TimedGreedyReachable Inv i z) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).SupportedOn
      (fun z' ↦ timedActiveTrackedUncoveredEdges active E z' ⊆
        timedActiveTrackedUncoveredEdges active E z) := by
  classical
  have hzlt : z.1.1 < n := lt_of_le_of_lt hz.1 hi
  by_cases hactive : active z.1.1 z.2
  · unfold FiniteLaw.timedStoppedKernel
    rw [dif_pos ⟨hzlt, hactive⟩]
    intro z' hmass
    -- Unpack the mapped support directly via its mass witness.
    rw [FiniteLaw.map] at hmass
    change 0 < ∑ S',
      if (FiniteLaw.advanceTime z.1 hzlt, S') = z' then
        (greedyKernel F z.2).mass S' else 0 at hmass
    obtain ⟨S', _hmem, hterm⟩ := Finset.sum_pos_iff.mp hmass
    by_cases heq : (FiniteLaw.advanceTime z.1 hzlt, S') = z'
    · rw [if_pos heq] at hterm
      subst z'
      simp only [timedActiveTrackedUncoveredEdges, if_pos hactive]
      by_cases hnext : active (FiniteLaw.advanceTime z.1 hzlt).1 S'
      · rw [if_pos hnext]
        exact greedyUncoveredEdges_antitone E
          ((greedyKernel_monotone_singleInsertion F z.2) S' hterm).1
      · rw [if_neg hnext]
        exact empty_subset _
    · simp [heq] at hterm
  · have hstop : ¬ (z.1.1 < n ∧ active z.1.1 z.2) := fun h ↦ hactive h.2
    unfold FiniteLaw.timedStoppedKernel
    rw [dif_neg hstop]
    exact FiniteLaw.supportedOn_pure _ Subset.rfl

/-- Local edge supply and the scalar deletion estimate imply one-step
survival contraction for the active-gated residual on every reachable
state. -/
theorem timedStoppedGreedyKernel_probability_activeTrackedUncovered_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (E : Finset (Sym2 V)) (Inv : GreedyStateOn V → Prop)
    (d : ℕ) (theta : ℝ≥0)
    (hsupply : ∀ j S, Inv S → active j S →
      ∀ e ∈ greedyUncoveredEdges E S,
        d ≤ (greedyChoicesCoveringEdge S e).card)
    (havailable : ∀ j S, Inv S → active j S → S.available.Nonempty)
    (hscalar : ∀ j S B, Inv S → active j S →
      B ⊆ greedyUncoveredEdges E S →
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (i : ℕ) (hi : i < n)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n)
    (hz : TimedGreedyReachable Inv i z)
    (B : Finset (Sym2 V))
    (hB : B ⊆ timedActiveTrackedUncoveredEdges active E z) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).probability
        (fun z' ↦ B ⊆ timedActiveTrackedUncoveredEdges active E z') ≤
      theta ^ B.card := by
  classical
  have hzlt : z.1.1 < n := lt_of_le_of_lt hz.1 hi
  by_cases hactive : active z.1.1 z.2
  · have hBactual : B ⊆ greedyUncoveredEdges E z.2 := by
      simpa [timedActiveTrackedUncoveredEdges, hactive] using hB
    have hA : z.2.available.Nonempty :=
      havailable z.1.1 z.2 hz.2 hactive
    unfold FiniteLaw.timedStoppedKernel
    rw [dif_pos ⟨hzlt, hactive⟩, FiniteLaw.probability_map]
    calc
      (greedyKernel F z.2).probability (fun S' ↦
          B ⊆ timedActiveTrackedUncoveredEdges active E
            (FiniteLaw.advanceTime z.1 hzlt, S')) ≤
          (greedyKernel F z.2).probability (fun S' ↦
            B ⊆ greedyUncoveredEdges E S') := by
        apply (greedyKernel F z.2).probability_mono
        intro S' htracked
        by_cases hnext : active (z.1.1 + 1) S'
        · simpa [timedActiveTrackedUncoveredEdges, hnext] using htracked
        · have hBempty : B = ∅ := by
            apply subset_empty.mp
            simpa [timedActiveTrackedUncoveredEdges, hnext] using htracked
          simp [hBempty]
      _ = ((greedySurvivalChoices F E z.2 B).card : ℝ≥0) *
          (z.2.available.card : ℝ≥0)⁻¹ :=
        greedyKernel_probability_uncovered_eq F E z.2 B hA
      _ ≤ theta ^ B.card := by
        apply greedySurvivalChoices_ratio_le_of_edgeSupply
          F E z.2 B hBactual d
        · intro e he
          exact hsupply z.1.1 z.2 hz.2 hactive e (hBactual he)
        · exact hscalar z.1.1 z.2 B hz.2 hactive hBactual
  · have hBempty : B = ∅ := by
      apply subset_empty.mp
      simpa [timedActiveTrackedUncoveredEdges, hactive] using hB
    subst B
    simp [FiniteLaw.timedStoppedKernel, hzlt, hactive,
      FiniteLaw.probability_true]

/-- Product mixed law for the terminal clocked stopped process. -/
theorem timedStoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (E : Finset (Sym2 V)) (Inv : GreedyStateOn V → Prop)
    (D d : ℕ) (hD : 0 < D) (theta alpha eta : ℝ≥0)
    (S₀ : GreedyStateOn V)
    (hInv₀ : Inv S₀)
    (hactive₀ : active 0 S₀)
    (hInv : ∀ j, j < n → ∀ S, Inv S → active j S →
      (greedyKernel F S).SupportedOn Inv)
    (hfloor : ∀ j S, active j S → D ≤ S.available.card)
    (hsupply : ∀ j S, Inv S → active j S →
      ∀ e ∈ greedyUncoveredEdges E S,
        d ≤ (greedyChoicesCoveringEdge S e).card)
    (hscalar : ∀ j S B, Inv S → active j S →
      B ⊆ greedyUncoveredEdges E S →
      ((S.available.card - B.card * d / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (Q : TripleSystemOn V) (B : Finset (Sym2 V))
    (hQ : Disjoint Q S₀.chosen)
    (hB : B ⊆ greedyUncoveredEdges E S₀)
    (hsurvived : theta ^ (n - Q.card) ≤ eta) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧
          B ⊆ timedActiveTrackedUncoveredEdges active E z) ≤
      alpha ^ Q.card * eta ^ B.card := by
  let z₀ : FiniteLaw.TimedState (GreedyStateOn V) n :=
    (⟨0, by omega⟩, S₀)
  let Kt : ℕ → FiniteLaw.TimedState (GreedyStateOn V) n →
      FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n) :=
    fun _ z ↦ FiniteLaw.timedStoppedKernel n
      (fun _ ↦ greedyKernel F) active z
  let P : ℕ → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    TimedGreedyReachable Inv
  have hBtracked : B ⊆ timedActiveTrackedUncoveredEdges active E z₀ := by
    simpa [z₀, timedActiveTrackedUncoveredEdges, hactive₀] using hB
  have hraw := evolveKernels_probability_selectedUncovered_le_of_supported
    Kt (fun z ↦ z.2.chosen)
      (timedActiveTrackedUncoveredEdges active E)
      (D : ℝ≥0)⁻¹ theta P n
    (fun i hi z hz ↦
      timedStoppedGreedyKernel_supported_reachable
        n F active Inv hInv i hi z hz)
    (fun _i _hi _z _hz ↦
      timedStoppedGreedyKernel_monotone_singleInsertion n F active _z)
    (fun i hi z hz ↦
      timedStoppedGreedyKernel_antitone_activeTracked_of_reachable
        n F active E Inv i hi z hz)
    (fun i hi z hz B hB ↦
      timedStoppedGreedyKernel_probability_activeTrackedUncovered_le
        n F active E Inv d theta hsupply
          (fun j S _hInv hact ↦ card_pos.mp (lt_of_lt_of_le hD (hfloor j S hact)))
          hscalar i hi z hz B hB)
    (fun i hi z _hz T hT B _hB ↦
      ((FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).probability_mono
        (fun _z' h ↦ h.1)).trans
          (timedStoppedGreedyKernel_probability_new_triangle_le
            n F active D hD hfloor z T hT))
    z₀ (by exact ⟨by simp [z₀], hInv₀⟩) Q B hQ hBtracked n le_rfl
  have hproduct := hraw.trans
    (selectedUncoveredEnvelope_le_product
      (D : ℝ≥0)⁻¹ theta alpha eta B.card n Q.card
        hselected hsurvived)
  change (FiniteLaw.evolveKernels Kt n (FiniteLaw.pure z₀)).probability
      (SelectedUncoveredEvent (fun z ↦ z.2.chosen)
        (timedActiveTrackedUncoveredEdges active E) Q B) ≤
    alpha ^ Q.card * eta ^ B.card
  exact hproduct

end

end Erdos207
