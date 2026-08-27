/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSTrajectories

/-! # Explicit coefficient bounds for the coupled KSSS trajectories -/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

theorem ksssEdgeDensity_le_one {E₀ t : ℝ} (hE : 0 < E₀) (ht : 0 ≤ t) :
    ksssEdgeDensity E₀ t ≤ 1 := by
  unfold ksssEdgeDensity
  rw [div_le_one hE]
  linarith

theorem ksssPoissonExponent_nonneg
    (orders : Finset ℕ) (a : ℕ → ℝ) {t : ℝ}
    (ha : ∀ d ∈ orders, 0 ≤ a d) (ht : 0 ≤ t) :
    0 ≤ ksssPoissonExponent orders a t := by
  exact sum_nonneg fun d hd ↦ mul_nonneg (ha d hd) (pow_nonneg ht d)

theorem ksssPoissonRate_nonneg
    (orders : Finset ℕ) (a : ℕ → ℝ) {t : ℝ}
    (ha : ∀ d ∈ orders, 0 ≤ a d) (ht : 0 ≤ t) :
    0 ≤ ksssPoissonRate orders a t := by
  exact sum_nonneg fun d hd ↦
    mul_nonneg (mul_nonneg (ha d hd) (Nat.cast_nonneg d)) (pow_nonneg ht _)

theorem ksssPoissonExponent_le_sum
    (orders : Finset ℕ) (a b : ℕ → ℝ) {E₀ t : ℝ}
    (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d)
    (ht : 0 ≤ t) (htE : t ≤ E₀) :
    ksssPoissonExponent orders a t ≤ ∑ d ∈ orders, b d := by
  apply sum_le_sum
  intro d hd
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htE d) (ha d hd)).trans
    (hab d hd)

theorem ksssPoissonRate_mul_clock_le_sum
    (orders : Finset ℕ) (a b : ℕ → ℝ) {E₀ t : ℝ}
    (horders : ∀ d ∈ orders, 1 ≤ d)
    (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d)
    (ht : 0 ≤ t) (htE : t ≤ E₀) :
    ksssPoissonRate orders a t * E₀ ≤ ∑ d ∈ orders, (d : ℝ) * b d := by
  have hE : 0 ≤ E₀ := ht.trans htE
  unfold ksssPoissonRate
  rw [sum_mul]
  apply sum_le_sum
  intro d hd
  have hpower : t ^ (d - 1) * E₀ ≤ E₀ ^ d := by
    calc
      t ^ (d - 1) * E₀ ≤ E₀ ^ (d - 1) * E₀ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht htE _) hE
      _ = E₀ ^ d := by rw [← pow_succ, Nat.sub_add_cancel (horders d hd)]
  calc
    a d * d * t ^ (d - 1) * E₀ = (d : ℝ) * (a d * (t ^ (d - 1) * E₀)) := by ring
    _ ≤ (d : ℝ) * (a d * E₀ ^ d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpower (ha d hd))
        (Nat.cast_nonneg d)
    _ ≤ (d : ℝ) * b d := mul_le_mul_of_nonneg_left (hab d hd) (Nat.cast_nonneg d)

theorem ksssAvailableTrajectory_bounds
    (orders : Finset ℕ) (a b : ℕ → ℝ) {E₀ A₀ t : ℝ}
    (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (htclock : 3 * t < E₀) :
    A₀ * ksssEdgeDensity E₀ t ^ 3 * Real.exp (-(∑ d ∈ orders, b d)) ≤
      ksssAvailableTrajectory orders a E₀ A₀ t ∧
    ksssAvailableTrajectory orders a E₀ A₀ t ≤ A₀ * ksssEdgeDensity E₀ t ^ 3 := by
  have htE : t ≤ E₀ := by linarith
  have hp := (ksssEdgeDensity_pos hE htclock).le
  have hscale : 0 ≤ A₀ * ksssEdgeDensity E₀ t ^ 3 := mul_nonneg hA (pow_nonneg hp _)
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg
        (ksssPoissonExponent_le_sum orders a b ha hab ht htE))) hscale
  · unfold ksssAvailableTrajectory
    apply mul_le_of_le_one_right hscale
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
      (ksssPoissonExponent_nonneg orders a ha ht))

theorem ksssThreatTrajectory_bounds
    (orders : Finset ℕ) (a b : ℕ → ℝ) {E₀ A₀ t : ℝ}
    (horders : ∀ d ∈ orders, 1 ≤ d)
    (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d)
    (hE : 0 < E₀) (hA : 0 < A₀) (ht : 0 ≤ t) (htclock : 3 * t < E₀) :
    3 * ksssPairTrajectory orders a E₀ A₀ t ≤
      ksssThreatTrajectory orders a E₀ A₀ t ∧
    ksssThreatTrajectory orders a E₀ A₀ t ≤
      (3 + (∑ d ∈ orders, (d : ℝ) * b d) / 3) *
        ksssPairTrajectory orders a E₀ A₀ t := by
  have hp := ksssEdgeDensity_pos hE htclock
  have hp1 := ksssEdgeDensity_le_one hE ht
  have hAP := ksssAvailableTrajectory_pos orders a hE hA htclock
  have hFP := ksssPairTrajectory_pos orders a hE hA htclock
  have hrho := ksssPoissonRate_nonneg orders a ha ht
  have hrhob := ksssPoissonRate_mul_clock_le_sum orders a b horders ha hab ht
    (show t ≤ E₀ by linarith)
  have hB : 0 ≤ ∑ d ∈ orders, (d : ℝ) * b d :=
    (mul_nonneg hrho hE.le).trans hrhob
  have hscaled : ksssEdgeDensity E₀ t * (ksssPoissonRate orders a t * E₀) ≤
      ∑ d ∈ orders, (d : ℝ) * b d :=
    (mul_le_mul_of_nonneg_left hrhob hp.le).trans
      (mul_le_of_le_one_left hB hp1)
  have hidentity : ksssAvailableTrajectory orders a E₀ A₀ t =
      E₀ * ksssEdgeDensity E₀ t * ksssPairTrajectory orders a E₀ A₀ t / 3 := by
    unfold ksssPairTrajectory
    field_simp
  have hcorrection : ksssAvailableTrajectory orders a E₀ A₀ t *
      ksssPoissonRate orders a t ≤
        ((∑ d ∈ orders, (d : ℝ) * b d) / 3) *
          ksssPairTrajectory orders a E₀ A₀ t := by
    calc
      _ = (ksssPairTrajectory orders a E₀ A₀ t / 3) *
          (ksssEdgeDensity E₀ t * (ksssPoissonRate orders a t * E₀)) := by
            rw [hidentity]
            ring
      _ ≤ (ksssPairTrajectory orders a E₀ A₀ t / 3) *
          (∑ d ∈ orders, (d : ℝ) * b d) :=
            mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = _ := by ring
  rw [ksssThreatTrajectory_eq orders a E₀ A₀ t horders]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hAP.le hrho)
  · nlinarith only [hcorrection]

end

end Erdos207
