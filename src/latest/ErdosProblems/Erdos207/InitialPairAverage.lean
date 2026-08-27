/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GlobalPairTrajectory

/-! # Exact initial pair regularity from a common degree interval -/

namespace Erdos207

open Finset

noncomputable section

theorem initial_pair_average_interval
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (Q : Finset (Finset V)) (N loss : ℝ)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQpos : 0 < Q.card)
    (hdegrees : ∀ P ∈ Q, N - loss ≤ ((availableTrianglesContainingPair S P).card : ℝ) ∧
      ((availableTrianglesContainingPair S P).card : ℝ) ≤ N) :
    (N - loss ≤ 3 * (S.available.card : ℝ) / Q.card ∧ 3 * (S.available.card : ℝ) / Q.card ≤ N) ∧
      ∀ P ∈ Q, |((availableTrianglesContainingPair S P).card : ℝ) -
        3 * (S.available.card : ℝ) / Q.card| ≤ loss := by
  have hQposR : (0 : ℝ) < Q.card := by exact_mod_cast hQpos
  have hsum : (∑ P ∈ Q, ((availableTrianglesContainingPair S P).card : ℝ)) =
      3 * (S.available.card : ℝ) := by exact_mod_cast sum_pairSet_card_available S Q hQ hcover
  have hlow : (Q.card : ℝ) * (N - loss) ≤ 3 * (S.available.card : ℝ) := by
    rw [← hsum]
    simpa only [sum_const, nsmul_eq_mul] using
      (sum_le_sum fun P hP ↦ (hdegrees P hP).1)
  have hupp : 3 * (S.available.card : ℝ) ≤ (Q.card : ℝ) * N := by
    rw [← hsum]
    simpa only [sum_const, nsmul_eq_mul] using
      (sum_le_sum fun P hP ↦ (hdegrees P hP).2)
  have hlower : N - loss ≤ 3 * (S.available.card : ℝ) / Q.card := by
    apply (le_div_iff₀ hQposR).mpr
    nlinarith only [hlow]
  have hupper : 3 * (S.available.card : ℝ) / Q.card ≤ N := by
    apply (div_le_iff₀ hQposR).mpr
    nlinarith only [hupp]
  refine ⟨⟨hlower, hupper⟩, fun P hP ↦ ?_⟩
  have hd := hdegrees P hP
  exact abs_le.mpr ⟨by linarith only [hd.1, hupper], by linarith only [hd.2, hlower]⟩

theorem initial_pair_average_ratio_bounds
    (E A N loss : ℝ) (_hN : 0 < N) (hloss : loss ≤ N / 2)
    (hmean : N - loss ≤ 3 * A / E ∧ 3 * A / E ≤ N) :
    N / 6 ≤ A / E ∧ A / E ≤ N / 3 := by
  have hid : 3 * A / E = 3 * (A / E) := by ring
  rw [hid] at hmean
  constructor <;> linarith only [hmean.1, hmean.2, hloss]

theorem initial_pair_relative_error_of_power_loss
    (N t w loss deviation : ℝ) (s : ℕ)
    (_hN : 0 ≤ N) (ht : 0 < t) (hw : N / 2 ≤ w)
    (hloss : loss ≤ N / (2 * t ^ s)) (hdev : |deviation| ≤ loss) :
    |deviation| ≤ (1 / t ^ s) * w := by
  calc
    _ ≤ N / (2 * t ^ s) := hdev.trans hloss
    _ = (1 / t ^ s) * (N / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

end

end Erdos207
