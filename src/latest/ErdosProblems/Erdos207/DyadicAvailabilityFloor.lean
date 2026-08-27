/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSDyadicPairBounds
import ErdosProblems.Erdos207.KSSSTrajectoryState

/-! # The stopped availability floor from the coupled pair trajectories -/

namespace Erdos207

theorem residual_clock_power_lower
    (N t E p : ℝ) (b : ℕ) (ht : 0 < t)
    (hE : N ^ 2 / t ^ b ≤ E) (hp : 1 / t ^ b ≤ p) :
    N ^ 2 / t ^ (2 * b) ≤ E * p := by
  have hE0 : 0 ≤ E := (div_nonneg (sq_nonneg N) (pow_nonneg ht.le b)).trans hE
  calc
    _ = (N ^ 2 / t ^ b) * (1 / t ^ b) := by
      rw [Nat.mul_comm 2 b, pow_mul]
      ring
    _ ≤ E * p := mul_le_mul hE hp (by positivity) hE0

theorem availability_power_lower
    (N t L x e M : ℝ) (b : ℕ) (hN : 0 ≤ N) (ht : 0 < t) (hL0 : 0 ≤ L)
    (hL : N ^ 2 / t ^ (2 * b) ≤ L) (hx : N / t ^ (3 * b + 1) ≤ x)
    (he : e ≤ x / 4) (hM : |M - L * x / 3| ≤ L * e / 3) :
    N ^ 3 / (4 * t ^ (5 * b + 1)) ≤ M := by
  have hlower := (abs_le.mp hM).1
  have hsmall := mul_le_mul_of_nonneg_left he hL0
  have hquarter : L * x / 4 ≤ M := by nlinarith only [hlower, hsmall]
  have hprod := mul_le_mul hL hx (by positivity) hL0
  calc
    _ = (N ^ 2 / t ^ (2 * b)) * (N / t ^ (3 * b + 1)) / 4 := by
      have hexp : 5 * b + 1 = 2 * b + (3 * b + 1) := by omega
      rw [hexp, pow_add]
      field_simp
    _ ≤ L * x / 4 := div_le_div_of_nonneg_right hprod (by norm_num)
    _ ≤ M := hquarter

noncomputable section

theorem KSSSOnTrajectories.dyadic_availability_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q : Finset (Finset V)}
    {a coeff : ℕ → ℝ} {E₀ A₀ time N t : ℝ} {s b B : ℕ}
    (h : KSSSOnTrajectories F S q Q a E₀ A₀ (N / t ^ s) B time)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQcard : (Q.card : ℝ) = E₀ * ksssEdgeDensity E₀ time)
    (hE : 0 < E₀) (hA : 0 < A₀) (hTime : 0 ≤ time) (hclock : 3 * time < E₀)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E₀ ^ d ≤ coeff d)
    (hN : 0 ≤ N) (ht : 4 ≤ t)
    (hEfloor : N ^ 2 / t ^ b ≤ E₀)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E₀ time)
    (hratio : N / t ^ b ≤ A₀ / E₀) (hexp : Real.exp (∑ d ∈ ksssOrders q, coeff d) ≤ t)
    (hgap : b * B + 3 * b + 2 ≤ s) :
    N ^ 3 / (4 * t ^ (5 * b + 1)) ≤ (S.available.card : ℝ) := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hpair := ksssPairTrajectory_dyadic_bounds (ksssOrders q) a coeff E₀ A₀ time N t s b B
    hE hA hTime hclock ha hab hN ht hfloor hratio hexp hgap
  have hL := residual_clock_power_lower N t E₀ (ksssEdgeDensity E₀ time) b
    (by linarith) hEfloor hfloor
  have hglobal := h.availability_error hQ hcover
  rw [hQcard] at hglobal
  exact availability_power_lower N t _ _ _ S.available.card b hN (by linarith)
    (mul_nonneg hE.le hp.le) hL hpair.1 hpair.2 hglobal

end

end Erdos207
