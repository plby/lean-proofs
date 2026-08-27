/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SelectedUncoveredJointInclusion
import ErdosProblems.Erdos207.FiniteKernelConcentration

/-!
# Selected/uncovered estimates for inhomogeneous kernels

The clocked stopping processes used in the differential-equation argument
are expressed with `evolveKernels`.  This is the inhomogeneous counterpart of
`iterateKernel_probability_selectedUncovered_le`; the scalar contraction and
point-insertion bounds are uniform in the clock.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem evolveKernels_probability_selectedUncovered_le
    {Omega W Z : Type*} [Fintype Omega] [DecidableEq Omega]
    [DecidableEq W] [DecidableEq Z]
    (K : ℕ → Omega → FiniteLaw Omega)
    (R : Omega → Finset W) (U : Omega → Finset Z)
    (delta theta : ℝ≥0)
    (hsingle : ∀ i, IsMonotoneSingleInsertionKernel (K i) R)
    (hantitone : ∀ i, IsAntitoneSetKernel (K i) U)
    (hsurvive : ∀ i omega B, B ⊆ U omega →
      (K i omega).probability (fun omega' ↦ B ⊆ U omega') ≤
        theta ^ B.card)
    (hpoint : ∀ i omega x, x ∉ R omega → ∀ B, B ⊆ U omega →
      (K i omega).probability (fun omega' ↦
        x ∈ R omega' ∧ B ⊆ U omega') ≤ delta)
    (omega0 : Omega) (Q : Finset W) (B : Finset Z)
    (hdisjoint : Disjoint Q (R omega0)) (hB0 : B ⊆ U omega0)
    (t : ℕ) :
    (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)).probability
        (SelectedUncoveredEvent R U Q B) ≤
      selectedUncoveredEnvelope delta theta B.card t Q.card := by
  classical
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
      have hrec := bind_probability_selectedUncovered_le
        (K t) R U delta theta (hsingle t) (hantitone t)
          (hsurvive t) (hpoint t)
          (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)) Q B
      by_cases hQ : Q = ∅
      · subst Q
        have hempty := ih ∅ (by simp)
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
        have hQbound := ih Q hdisjoint
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
          have h := ih (Q.erase x) hd
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
