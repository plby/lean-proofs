/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSTrajectoryBounds

/-! # Identification with the source's vertex-indexed trajectories -/

namespace Erdos207

open Finset

noncomputable section

/-- `J r` is the number of forbidden families of vertex order `r`. -/
def ksssSourceCoefficient (A₀ : ℝ) (J : ℕ → ℝ) (d : ℕ) : ℝ :=
  (d + 1 : ℕ) * J (d + 3) / A₀ ^ (d + 1)

theorem ksssPairTrajectory_source
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (hE : E₀ ≠ 0) (hp : ksssEdgeDensity E₀ t ≠ 0) :
    ksssPairTrajectory orders a E₀ A₀ t =
      ksssEdgeDensity E₀ t ^ 2 * Real.exp (-ksssPoissonExponent orders a t) *
        (3 * A₀ / E₀) := by
  unfold ksssPairTrajectory ksssAvailableTrajectory
  field_simp

theorem normalized_configuration_monomial
    (A₀ t mu z : ℝ) (hA : A₀ ≠ 0) {d c : ℕ} (hcd : c ≤ d) :
    (z / A₀ ^ (d + 1)) * t ^ c * (A₀ * mu) ^ (d - c) =
      (t / A₀) ^ c * mu ^ (d - c) * (z / A₀) := by
  have hsplit : d + 1 = c + (d - c) + 1 := by omega
  rw [hsplit, pow_add, pow_add, pow_one, mul_pow, div_pow]
  field_simp

theorem ksssConfigurationTrajectory_source
    (orders : Finset ℕ) (J : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (hA : A₀ ≠ 0) {d c : ℕ} (hcd : c ≤ d) :
    ksssConfigurationTrajectory orders (ksssSourceCoefficient A₀ J) E₀ A₀ d c t =
      (d.choose c : ℝ) * (t / A₀) ^ c *
        (ksssEdgeDensity E₀ t ^ 3 *
          Real.exp (-ksssPoissonExponent orders (ksssSourceCoefficient A₀ J) t)) ^
            (d - c) * ((d + 1 : ℕ) * J (d + 3) / A₀) := by
  let mu := ksssEdgeDensity E₀ t ^ 3 *
    Real.exp (-ksssPoissonExponent orders (ksssSourceCoefficient A₀ J) t)
  have hnorm := normalized_configuration_monomial A₀ t mu
    ((d + 1 : ℕ) * J (d + 3)) hA hcd
  unfold ksssConfigurationTrajectory ksssSourceCoefficient ksssAvailableTrajectory
  dsimp only [mu, ksssSourceCoefficient] at hnorm
  unfold ksssSourceCoefficient at hnorm
  linear_combination (d.choose c : ℝ) * hnorm

theorem ksssSourceCoefficient_nonneg
    (A₀ : ℝ) (J : ℕ → ℝ) (hA : 0 ≤ A₀) {d : ℕ} (hJ : 0 ≤ J (d + 3)) :
    0 ≤ ksssSourceCoefficient A₀ J d := by
  unfold ksssSourceCoefficient
  positivity

/-- The source's good-data cardinality bound gives a coefficient bound
independent of the ambient order. -/
theorem ksssSourceCoefficient_mul_clock_pow_le
    (A₀ E₀ C : ℝ) (J : ℕ → ℝ) (hA : 0 < A₀) (hE : 0 < E₀) {d : ℕ}
    (hJ : J (d + 3) ≤ C * A₀ ^ (d + 1) / E₀ ^ d) :
    ksssSourceCoefficient A₀ J d * E₀ ^ d ≤ (d + 1 : ℕ) * C := by
  have hJ' : J (d + 3) * E₀ ^ d ≤ C * A₀ ^ (d + 1) :=
    (le_div_iff₀ (pow_pos hE d)).mp hJ
  unfold ksssSourceCoefficient
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hA (d + 1))]
  nlinarith only [mul_le_mul_of_nonneg_left hJ' (Nat.cast_nonneg (d + 1) :
    (0 : ℝ) ≤ (d + 1 : ℕ))]

end

end Erdos207
