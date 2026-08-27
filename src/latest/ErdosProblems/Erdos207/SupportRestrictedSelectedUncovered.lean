/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InhomogeneousSelectedUncovered

/-!
# Support-restricted selected/uncovered estimates

Clocked stopped processes have unreachable states on which a useful
one-step contraction need not hold (for example, a terminal clock state
which the kernel freezes).  This file proves the inhomogeneous mixed
selection/survival recurrence with every transition hypothesis restricted
to the positive-mass support at the relevant time.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The one-state version of the mixed selected/surviving-set recurrence.
Only the four hypotheses at the specified state are needed. -/
theorem kernel_probability_selectedUncovered_le_of_state
    {Omega W Z : Type*} [Fintype Omega]
    [DecidableEq W] [DecidableEq Z]
    (K : Omega → FiniteLaw Omega)
    (R : Omega → Finset W) (U : Omega → Finset Z)
    (delta theta : ℝ≥0) (omega : Omega)
    (hsingle : (K omega).SupportedOn fun omega' ↦
      R omega ⊆ R omega' ∧ (R omega' \ R omega).card ≤ 1)
    (hantitone : (K omega).SupportedOn fun omega' ↦ U omega' ⊆ U omega)
    (hsurvive : ∀ B, B ⊆ U omega →
      (K omega).probability (fun omega' ↦ B ⊆ U omega') ≤
        theta ^ B.card)
    (hpoint : ∀ x, x ∉ R omega → ∀ B, B ⊆ U omega →
      (K omega).probability (fun omega' ↦
        x ∈ R omega' ∧ B ⊆ U omega') ≤ delta)
    (Q : Finset W) (B : Finset Z) :
    (K omega).probability (SelectedUncoveredEvent R U Q B) ≤
      theta ^ B.card * nnrealIndicator
          (SelectedUncoveredEvent R U Q B omega) +
        ∑ x ∈ Q,
          nnrealIndicatorMul
            (SelectedUncoveredEvent R U (Q.erase x) B omega) delta := by
  classical
  by_cases hBU : B ⊆ U omega
  · by_cases hQR : Q ⊆ R omega
    · calc
        (K omega).probability (SelectedUncoveredEvent R U Q B) ≤
            (K omega).probability (fun omega' ↦ B ⊆ U omega') := by
          apply FiniteLaw.probability_mono
          intro omega' h
          exact h.2
        _ ≤ theta ^ B.card := hsurvive B hBU
        _ ≤ theta ^ B.card *
              nnrealIndicator (SelectedUncoveredEvent R U Q B omega) +
            ∑ x ∈ Q,
              nnrealIndicatorMul
                (SelectedUncoveredEvent R U (Q.erase x) B omega) delta := by
          simp only [SelectedUncoveredEvent, hQR, hBU, and_self,
            nnrealIndicator, if_true, mul_one]
          exact le_add_of_nonneg_right zero_le
    · have himp : ∀ omega',
          (R omega ⊆ R omega' ∧ (R omega' \ R omega).card ≤ 1) →
          SelectedUncoveredEvent R U Q B omega' →
          ∃ x ∈ Q, SelectedUncoveredEvent R U (Q.erase x) B omega ∧
            x ∈ R omega' ∧ B ⊆ U omega' := by
        intro omega' homega' htarget
        obtain ⟨x, hxQ, _hxnot, herase⟩ :=
          exists_erase_subset_of_sdiff_card_le_one
            htarget.1 homega'.2 hQR
        exact ⟨x, hxQ, ⟨herase, hBU⟩, htarget.1 hxQ, htarget.2⟩
      have hmono : (K omega).probability
          (SelectedUncoveredEvent R U Q B) ≤
          (K omega).probability (fun omega' ↦
            ∃ x ∈ Q, SelectedUncoveredEvent R U (Q.erase x) B omega ∧
              x ∈ R omega' ∧ B ⊆ U omega') :=
        (K omega).probability_mono_of_supported hsingle himp
      have hunion := (K omega).probability_exists_le Q (fun x omega' ↦
        SelectedUncoveredEvent R U (Q.erase x) B omega ∧
          x ∈ R omega' ∧ B ⊆ U omega')
      calc
        (K omega).probability (SelectedUncoveredEvent R U Q B) ≤
            (K omega).probability (fun omega' ↦
              ∃ x ∈ Q,
                SelectedUncoveredEvent R U (Q.erase x) B omega ∧
                  x ∈ R omega' ∧ B ⊆ U omega') := hmono
        _ ≤ ∑ x ∈ Q, (K omega).probability (fun omega' ↦
              SelectedUncoveredEvent R U (Q.erase x) B omega ∧
                x ∈ R omega' ∧ B ⊆ U omega') := hunion
        _ ≤ ∑ x ∈ Q,
              nnrealIndicatorMul
                (SelectedUncoveredEvent R U (Q.erase x) B omega) delta := by
          apply sum_le_sum
          intro x hxQ
          by_cases hxold :
              SelectedUncoveredEvent R U (Q.erase x) B omega
          · simp only [nnrealIndicatorMul, if_pos hxold]
            have hxnotR : x ∉ R omega := by
              intro hxR
              apply hQR
              intro y hyQ
              by_cases hyx : y = x
              · simpa [hyx] using hxR
              · exact hxold.1 (mem_erase.mpr ⟨hyx, hyQ⟩)
            exact ((K omega).probability_mono fun omega' h ↦ h.2).trans
              (hpoint x hxnotR B hBU)
          · have hfalse : (fun omega' ↦
                SelectedUncoveredEvent R U (Q.erase x) B omega ∧
                  x ∈ R omega' ∧ B ⊆ U omega') =
                (fun _ : Omega ↦ False) := by
              funext omega'
              exact propext ⟨fun h ↦ hxold h.1, False.elim⟩
            rw [hfalse, FiniteLaw.probability_false]
            simp [nnrealIndicatorMul, hxold]
        _ = theta ^ B.card *
              nnrealIndicator (SelectedUncoveredEvent R U Q B omega) +
            ∑ x ∈ Q,
              nnrealIndicatorMul
                (SelectedUncoveredEvent R U (Q.erase x) B omega) delta := by
          simp [SelectedUncoveredEvent, nnrealIndicator,
            nnrealIndicatorMul, hQR]
  · have himpossible : ∀ omega',
        U omega' ⊆ U omega →
        ¬ SelectedUncoveredEvent R U Q B omega' := by
      intro omega' hsub htarget
      exact hBU (htarget.2.trans hsub)
    have hzero : (K omega).probability
        (SelectedUncoveredEvent R U Q B) = 0 := by
      apply le_antisymm
      · calc
          (K omega).probability (SelectedUncoveredEvent R U Q B) ≤
              (K omega).probability (fun _ ↦ False) := by
            apply (K omega).probability_mono_of_supported hantitone
            intro omega' hsub htarget
            exact himpossible omega' hsub htarget
          _ = 0 := FiniteLaw.probability_false _
      · exact zero_le
    rw [hzero]
    exact zero_le

/-- Averaging the local recurrence only over the support of the input law. -/
theorem bind_probability_selectedUncovered_le_of_supported
    {Omega W Z : Type*} [Fintype Omega]
    [DecidableEq W] [DecidableEq Z]
    (K : Omega → FiniteLaw Omega)
    (R : Omega → Finset W) (U : Omega → Finset Z)
    (delta theta : ℝ≥0) (P : Omega → Prop)
    (L : FiniteLaw Omega) (hL : L.SupportedOn P)
    (hsingle : ∀ omega, P omega → (K omega).SupportedOn fun omega' ↦
      R omega ⊆ R omega' ∧ (R omega' \ R omega).card ≤ 1)
    (hantitone : ∀ omega, P omega →
      (K omega).SupportedOn fun omega' ↦ U omega' ⊆ U omega)
    (hsurvive : ∀ omega, P omega → ∀ B, B ⊆ U omega →
      (K omega).probability (fun omega' ↦ B ⊆ U omega') ≤
        theta ^ B.card)
    (hpoint : ∀ omega, P omega → ∀ x, x ∉ R omega →
      ∀ B, B ⊆ U omega →
      (K omega).probability (fun omega' ↦
        x ∈ R omega' ∧ B ⊆ U omega') ≤ delta)
    (Q : Finset W) (B : Finset Z) :
    (FiniteLaw.bind L K).probability (SelectedUncoveredEvent R U Q B) ≤
      theta ^ B.card *
          L.probability (SelectedUncoveredEvent R U Q B) +
        delta * ∑ x ∈ Q,
          L.probability (SelectedUncoveredEvent R U (Q.erase x) B) := by
  classical
  rw [FiniteLaw.probability_bind]
  calc
    (∑ omega, L.mass omega *
        (K omega).probability (SelectedUncoveredEvent R U Q B)) ≤
      ∑ omega, L.mass omega *
        (theta ^ B.card *
            nnrealIndicator (SelectedUncoveredEvent R U Q B omega) +
          ∑ x ∈ Q,
            nnrealIndicatorMul
              (SelectedUncoveredEvent R U (Q.erase x) B omega) delta) := by
      apply sum_le_sum
      intro omega _homega
      by_cases hm : 0 < L.mass omega
      · have hP := hL omega hm
        simpa only [mul_comm] using mul_le_mul_left
          (kernel_probability_selectedUncovered_le_of_state K R U delta theta
            omega (hsingle omega hP) (hantitone omega hP)
            (hsurvive omega hP) (hpoint omega hP) Q B) (L.mass omega)
      · have hm0 : L.mass omega = 0 :=
          le_antisymm (not_lt.mp hm) zero_le
        simp [hm0]
    _ = theta ^ B.card *
          L.probability (SelectedUncoveredEvent R U Q B) +
        delta * ∑ x ∈ Q,
          L.probability (SelectedUncoveredEvent R U (Q.erase x) B) := by
      simp only [mul_add, sum_add_distrib]
      congr 1
      · unfold FiniteLaw.probability
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro omega _homega
        by_cases h : SelectedUncoveredEvent R U Q B omega <;>
          simp [nnrealIndicator, h, mul_comm]
      · rw [show (∑ omega, L.mass omega *
              ∑ x ∈ Q,
                nnrealIndicatorMul
                  (SelectedUncoveredEvent R U (Q.erase x) B omega) delta) =
            ∑ omega, ∑ x ∈ Q, L.mass omega *
              nnrealIndicatorMul
                (SelectedUncoveredEvent R U (Q.erase x) B omega) delta by
            apply sum_congr rfl
            intro omega _homega
            rw [Finset.mul_sum]]
        rw [Finset.sum_comm, Finset.mul_sum]
        apply sum_congr rfl
        intro x _hx
        unfold FiniteLaw.probability
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro omega _homega
        by_cases h : SelectedUncoveredEvent R U (Q.erase x) B omega <;>
          simp [nnrealIndicatorMul, h, mul_comm]

/-- The mixed recurrence for an inhomogeneous process whose transition
hypotheses and time-varying invariant are required only on reachable states. -/
theorem evolveKernels_probability_selectedUncovered_le_of_supported
    {Omega W Z : Type*} [Fintype Omega] [DecidableEq Omega]
    [DecidableEq W] [DecidableEq Z]
    (K : ℕ → Omega → FiniteLaw Omega)
    (R : Omega → Finset W) (U : Omega → Finset Z)
    (delta theta : ℝ≥0) (P : ℕ → Omega → Prop) (N : ℕ)
    (hsupport : ∀ i, i < N → ∀ omega, P i omega →
      (K i omega).SupportedOn (P (i + 1)))
    (hsingle : ∀ i, i < N → ∀ omega, P i omega →
      (K i omega).SupportedOn fun omega' ↦
      R omega ⊆ R omega' ∧ (R omega' \ R omega).card ≤ 1)
    (hantitone : ∀ i, i < N → ∀ omega, P i omega →
      (K i omega).SupportedOn fun omega' ↦ U omega' ⊆ U omega)
    (hsurvive : ∀ i, i < N → ∀ omega, P i omega →
      ∀ B, B ⊆ U omega →
      (K i omega).probability (fun omega' ↦ B ⊆ U omega') ≤
        theta ^ B.card)
    (hpoint : ∀ i, i < N → ∀ omega, P i omega →
      ∀ x, x ∉ R omega →
      ∀ B, B ⊆ U omega →
      (K i omega).probability (fun omega' ↦
        x ∈ R omega' ∧ B ⊆ U omega') ≤ delta)
    (omega0 : Omega) (hP0 : P 0 omega0)
    (Q : Finset W) (B : Finset Z)
    (hdisjoint : Disjoint Q (R omega0)) (hB0 : B ⊆ U omega0)
    (t : ℕ) (htN : t ≤ N) :
    (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)).probability
        (SelectedUncoveredEvent R U Q B) ≤
      selectedUncoveredEnvelope delta theta B.card t Q.card := by
  classical
  have hP (n : ℕ) (hnN : n ≤ N) :
      (FiniteLaw.evolveKernels K n (FiniteLaw.pure omega0)).SupportedOn
        (P n) := by
    induction n with
    | zero => exact FiniteLaw.supportedOn_pure _ hP0
    | succ n ih =>
        exact (ih (by omega)).bind (K n) fun omega homega ↦
          hsupport n (by omega) omega homega
  induction t generalizing Q with
  | zero =>
      simp only [FiniteLaw.evolveKernels_zero, FiniteLaw.probability_pure]
      by_cases hQ : Q = ∅
      · subst Q
        simp [SelectedUncoveredEvent, hB0]
      · have hnot : ¬ Q ⊆ R omega0 := by
          intro hsub
          obtain ⟨x, hxQ⟩ := nonempty_iff_ne_empty.mpr hQ
          exact disjoint_left.mp hdisjoint hxQ (hsub hxQ)
        obtain ⟨q, hq⟩ : ∃ q, Q.card = q + 1 :=
          Nat.exists_eq_succ_of_ne_zero
            (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hQ))
        simp [SelectedUncoveredEvent, hnot, hq]
  | succ t ih =>
      rw [FiniteLaw.evolveKernels_succ]
      have hrec := bind_probability_selectedUncovered_le_of_supported
        (K t) R U delta theta (P t)
          (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0))
          (hP t (by omega))
          (hsingle t (by omega)) (hantitone t (by omega))
          (hsurvive t (by omega)) (hpoint t (by omega)) Q B
      by_cases hQ : Q = ∅
      · subst Q
        have hempty := ih ∅ (by simp) (by omega)
        have hempty' :
            (FiniteLaw.evolveKernels K t
              (FiniteLaw.pure omega0)).probability
                (SelectedUncoveredEvent R U ∅ B) ≤
              selectedUncoveredEnvelope delta theta B.card t 0 := by
          simpa using hempty
        calc
          (FiniteLaw.bind
              (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0))
              (K t)).probability
                (SelectedUncoveredEvent R U ∅ B) ≤
              theta ^ B.card *
                (FiniteLaw.evolveKernels K t
                  (FiniteLaw.pure omega0)).probability
                    (SelectedUncoveredEvent R U ∅ B) := by
            simpa using hrec
          _ ≤ theta ^ B.card *
                selectedUncoveredEnvelope delta theta B.card t 0 := by
            simpa only [mul_comm] using
              mul_le_mul_left hempty' (theta ^ B.card)
          _ = selectedUncoveredEnvelope delta theta B.card (t + 1) 0 := rfl
      · obtain ⟨q, hq⟩ : ∃ q, Q.card = q + 1 :=
          Nat.exists_eq_succ_of_ne_zero
            (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hQ))
        have hQbound := ih Q hdisjoint (by omega)
        have hQbound' :
            (FiniteLaw.evolveKernels K t
              (FiniteLaw.pure omega0)).probability
                (SelectedUncoveredEvent R U Q B) ≤
              selectedUncoveredEnvelope delta theta B.card t (q + 1) := by
          simpa only [hq] using hQbound
        have herase (x : W) (hx : x ∈ Q) :
            (FiniteLaw.evolveKernels K t
              (FiniteLaw.pure omega0)).probability
                (SelectedUncoveredEvent R U (Q.erase x) B) ≤
              selectedUncoveredEnvelope delta theta B.card t q := by
          have hd : Disjoint (Q.erase x) (R omega0) :=
            hdisjoint.mono_left (erase_subset x Q)
          have h := ih (Q.erase x) hd (by omega)
          simpa [card_erase_of_mem hx, hq] using h
        have hsum :
            (∑ x ∈ Q,
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (SelectedUncoveredEvent R U (Q.erase x) B)) ≤
              ∑ _x ∈ Q,
                selectedUncoveredEnvelope delta theta B.card t q := by
          apply sum_le_sum
          intro x hx
          exact herase x hx
        calc
          (FiniteLaw.bind
              (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0))
              (K t)).probability
                (SelectedUncoveredEvent R U Q B) ≤
              theta ^ B.card *
                  (FiniteLaw.evolveKernels K t
                    (FiniteLaw.pure omega0)).probability
                      (SelectedUncoveredEvent R U Q B) +
                delta * ∑ x ∈ Q,
                  (FiniteLaw.evolveKernels K t
                    (FiniteLaw.pure omega0)).probability
                      (SelectedUncoveredEvent R U (Q.erase x) B) := hrec
          _ ≤ theta ^ B.card *
                selectedUncoveredEnvelope delta theta B.card t (q + 1) +
              delta * ∑ _x ∈ Q,
                selectedUncoveredEnvelope delta theta B.card t q := by
            apply add_le_add
            · simpa only [mul_comm] using
                mul_le_mul_left hQbound' (theta ^ B.card)
            · simpa only [mul_comm] using
                mul_le_mul_left hsum delta
          _ = selectedUncoveredEnvelope delta theta B.card
                (t + 1) (q + 1) := by
            simp [hq, mul_assoc, mul_left_comm]
          _ = selectedUncoveredEnvelope delta theta B.card
                (t + 1) Q.card := by rw [hq]

end

end Erdos207
