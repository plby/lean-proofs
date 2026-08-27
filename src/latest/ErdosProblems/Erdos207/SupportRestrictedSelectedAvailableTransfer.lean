/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SelectedAvailableUncoveredTransfer

/-!
# Support-restricted selected/available transfer

Trajectory estimates for the long greedy process hold only on its reachable
good-state support.  This is the support-restricted form of the exact
selected/available/uncovered recurrence.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

theorem evolveKernels_probability_selectedAvailableUncovered_le_envelope_of_supported
    {Omega W Z : Type*} [Fintype Omega] [DecidableEq Omega]
    [DecidableEq W] [DecidableEq Z]
    (K : ℕ → Omega → FiniteLaw Omega)
    (selected available : Omega → Finset W)
    (uncovered : Omega → Finset Z)
    (delta theta : ℕ → ℝ≥0)
    (P : ℕ → Omega → Prop) (N : ℕ)
    (hsupport : ∀ i, i < N → ∀ omega, P i omega →
      (K i omega).SupportedOn (P (i + 1)))
    (Q : Finset W) (B : Finset Z)
    (hstep : ∀ i, i < N → ∀ omega, P i omega → ∀ S, S ⊆ Q →
      (K i omega).probability
          (SelectedAvailableUncoveredEvent selected available uncovered
            Q S B) ≤
        theta i ^ (3 * (Q \ S).card + B.card) *
            nnrealIndicator
              (SelectedAvailableUncoveredEvent selected available uncovered
                Q S B omega) +
          ∑ x ∈ S, nnrealIndicatorMul
            (SelectedAvailableUncoveredEvent selected available uncovered
              Q (S.erase x) B omega) (delta i))
    (omega₀ : Omega) (hP₀ : P 0 omega₀)
    (hQselected : Disjoint Q (selected omega₀))
    (hQavailable : Q ⊆ available omega₀)
    (hB : B ⊆ uncovered omega₀)
    (S : Finset W) (hSQ : S ⊆ Q) (t : ℕ) (htN : t ≤ N) :
    (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega₀)).probability
        (SelectedAvailableUncoveredEvent selected available uncovered
          Q S B) ≤
      selectedAvailableUncoveredEnvelope delta theta Q B.card t S := by
  classical
  have hP (n : ℕ) (hnN : n ≤ N) :
      (FiniteLaw.evolveKernels K n (FiniteLaw.pure omega₀)).SupportedOn
        (P n) := by
    induction n with
    | zero => exact FiniteLaw.supportedOn_pure _ hP₀
    | succ n ih =>
        exact (ih (by omega)).bind (K n) fun omega homega ↦
          hsupport n (by omega) omega homega
  induction t generalizing S with
  | zero =>
      simp only [FiniteLaw.evolveKernels_zero, FiniteLaw.probability_pure,
        selectedAvailableUncoveredEnvelope_zero]
      by_cases hS : S = ∅
      · subst S
        simp [SelectedAvailableUncoveredEvent,
          hQselected, hQavailable, hB]
      · have hnot : ¬ S ⊆ selected omega₀ := by
          intro hsub
          obtain ⟨x, hxS⟩ := nonempty_iff_ne_empty.mpr hS
          exact disjoint_left.mp hQselected (hSQ hxS) (hsub hxS)
        simp [SelectedAvailableUncoveredEvent, hnot, hS]
  | succ t ih =>
      rw [FiniteLaw.evolveKernels_succ, FiniteLaw.probability_bind]
      let L := FiniteLaw.evolveKernels K t (FiniteLaw.pure omega₀)
      let Event : Finset W → Omega → Prop := fun T ↦
        SelectedAvailableUncoveredEvent selected available uncovered Q T B
      have ht : t < N := by omega
      have hconditional (omega : Omega) (homega : P t omega) :
          (K t omega).probability (Event S) ≤
            theta t ^ (3 * (Q \ S).card + B.card) *
                nnrealIndicator (Event S omega) +
              ∑ x ∈ S, nnrealIndicatorMul
                (Event (S.erase x) omega) (delta t) := by
        simpa only [Event] using hstep t ht omega homega S hSQ
      have hmain : L.probability (Event S) ≤
          selectedAvailableUncoveredEnvelope delta theta Q B.card t S := by
        simpa only [L, Event] using ih S hSQ (by omega)
      have herase : ∀ x ∈ S,
          L.probability (Event (S.erase x)) ≤
            selectedAvailableUncoveredEnvelope delta theta Q B.card t
              (S.erase x) := by
        intro x hx
        have heraseQ : S.erase x ⊆ Q := (erase_subset x S).trans hSQ
        simpa only [L, Event] using ih (S.erase x) heraseQ (by omega)
      have hLP : L.SupportedOn (P t) := by
        simpa only [L] using hP t (by omega)
      calc
        (∑ omega, L.mass omega * (K t omega).probability (Event S)) ≤
            ∑ omega, L.mass omega *
              (theta t ^ (3 * (Q \ S).card + B.card) *
                  nnrealIndicator (Event S omega) +
                ∑ x ∈ S, nnrealIndicatorMul
                  (Event (S.erase x) omega) (delta t)) := by
          apply sum_le_sum
          intro omega homega
          by_cases hmass : 0 < L.mass omega
          · gcongr
            exact hconditional omega (hLP omega hmass)
          · have hzero : L.mass omega = 0 :=
              le_antisymm (not_lt.mp hmass) zero_le
            simp [hzero]
        _ = theta t ^ (3 * (Q \ S).card + B.card) *
              L.probability (Event S) +
            ∑ x ∈ S, delta t * L.probability (Event (S.erase x)) := by
          simp only [mul_add, sum_add_distrib]
          congr 1
          · unfold FiniteLaw.probability
            rw [mul_sum]
            apply sum_congr rfl
            intro omega homega
            by_cases hevent : Event S omega <;>
              simp [nnrealIndicator, hevent, mul_comm]
          · rw [show (∑ omega, L.mass omega *
                  ∑ x ∈ S, nnrealIndicatorMul
                    (Event (S.erase x) omega) (delta t)) =
                ∑ omega, ∑ x ∈ S, L.mass omega *
                  nnrealIndicatorMul
                    (Event (S.erase x) omega) (delta t) by
                apply sum_congr rfl
                intro omega homega
                rw [mul_sum]]
            rw [sum_comm]
            apply sum_congr rfl
            intro x hx
            unfold FiniteLaw.probability
            rw [mul_sum]
            apply sum_congr rfl
            intro omega homega
            by_cases hevent : Event (S.erase x) omega <;>
              simp [nnrealIndicatorMul, hevent, mul_comm]
        _ ≤ theta t ^ (3 * (Q \ S).card + B.card) *
              selectedAvailableUncoveredEnvelope delta theta Q B.card t S +
            ∑ x ∈ S, delta t *
              selectedAvailableUncoveredEnvelope delta theta Q B.card t
                (S.erase x) := by
          apply add_le_add
          · gcongr
          · apply sum_le_sum
            intro x hx
            gcongr
            exact herase x hx
        _ = selectedAvailableUncoveredEnvelope delta theta Q B.card
              (t + 1) S := rfl

end

end Erdos207
