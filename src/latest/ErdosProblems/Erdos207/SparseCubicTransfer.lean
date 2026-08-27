/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CubicSurvivalCancellation
import ErdosProblems.Erdos207.KSSSDyadicPairBounds

/-! # Cubic cancellation normalized by the actual sparse initial availability -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem ksssPairTrajectory_lower_initial_normalization
    (orders : Finset ℕ) (a coeff : ℕ → ℝ) (E A time C : ℝ)
    (hE : 0 < E) (hA : 0 < A) (_hC : 0 < C) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hab : ∀ d ∈ orders, a d * E ^ d ≤ coeff d)
    (hexp : Real.exp (∑ d ∈ orders, coeff d) ≤ C) :
    3 * (A / E) * ksssEdgeDensity E time ^ 2 / C ≤ ksssPairTrajectory orders a E A time := by
  have hp := ksssEdgeDensity_pos hE hclock
  have he := ksssPoisson_exp_neg_ge_inverse_scale orders a coeff E time C ha hab htime (by linarith) hexp
  rw [ksssPairTrajectory_source orders a E A time hE.ne' hp.ne']
  calc
    _ = ksssEdgeDensity E time ^ 2 * (1 / C) * (3 * A / E) := by ring
    _ ≤ ksssEdgeDensity E time ^ 2 * Real.exp (-ksssPoissonExponent orders a time) * (3 * A / E) := by gcongr

theorem sparse_availability_cubic_lower
    (E A C p x D : ℝ) (hE : 0 < E) (hC : 0 < C) (hp : 0 ≤ p)
    (hx : 3 * (A / E) * p ^ 2 / C ≤ x) (hfloor : E * p * x / 8 ≤ D) :
    3 * A * p ^ 3 ≤ 8 * C * D := by
  have hmul := mul_le_mul_of_nonneg_left hx (mul_nonneg hE.le hp)
  have hid : E * p * (3 * (A / E) * p ^ 2 / C) = 3 * A * p ^ 3 / C := by field_simp
  rw [hid] at hmul
  have hbound : 3 * A * p ^ 3 / C ≤ 8 * D := by linarith only [hmul, hfloor]
  have h := (div_le_iff₀ hC).mp hbound
  nlinarith only [h]

theorem sparse_normalized_cubic_bound
    (A C p D survival : ℝ≥0) (hA : 0 < A) (hD : 0 < D)
    (hfloor : 3 * A * p ^ 3 ≤ 8 * C * D) (hsurvival : survival ≤ 2 * p) :
    D⁻¹ * survival ^ 3 ≤ 64 * C / (3 * A) := by
  calc
    _ ≤ D⁻¹ * (2 * p) ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left' hsurvival _) zero_le
    _ = 8 * p ^ 3 / D := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hD (by positivity : 0 < 3 * A)).mpr
      nlinarith only [hfloor]

theorem transferPointWeight_boundedSharp_le_uniform_normalized
    (n K : ℕ) (D M d : ℕ → ℕ) (factor Z : ℝ≥0)
    (hfactor : ∀ i, i < n → (boundedSharpSurvivalTheta (M i) (d i) K ^ K)⁻¹ ≤ factor)
    (hnormalized : ∀ i, i < n → (D i : ℝ≥0)⁻¹ *
      cumulativeSurvival (boundedSharpSurvivalSchedule n M d K) i ^ 3 ≤ Z) :
    transferPointWeight (boundedSharpSurvivalSchedule n M d K)
      (boundedSharpTransferSchedule n D M d K) n ≤ factor * (n : ℝ≥0) * Z := by
  calc
    _ ≤ ∑ _i ∈ range n, factor * Z := by
      apply sum_le_sum
      intro i hi
      have hi' := mem_range.mp hi
      simp only [boundedSharpTransferSchedule, if_pos hi', boundedSharpTransferRho]
      calc
        _ = (boundedSharpSurvivalTheta (M i) (d i) K ^ K)⁻¹ *
            ((D i : ℝ≥0)⁻¹ * cumulativeSurvival (boundedSharpSurvivalSchedule n M d K) i ^ 3) := by ring
        _ ≤ _ := mul_le_mul (hfactor i hi') (hnormalized i hi') zero_le zero_le
    _ = _ := by simp; ring

theorem transferPointWeight_sparse_initial_scale
    (n K : ℕ) (D M d : ℕ → ℕ) (A E C : ℝ≥0) (p : ℕ → ℝ≥0)
    (hA : 0 < A) (hn : (n : ℝ≥0) ≤ E)
    (hD : ∀ i, i < n → 0 < D i)
    (hfactor : ∀ i, i < n → (boundedSharpSurvivalTheta (M i) (d i) K ^ K)⁻¹ ≤ (2 : ℝ≥0))
    (hfloor : ∀ i, i < n → 3 * A * p i ^ 3 ≤ 8 * C * D i)
    (hsurvival : ∀ i, i < n → cumulativeSurvival (boundedSharpSurvivalSchedule n M d K) i ≤ 2 * p i) :
    transferPointWeight (boundedSharpSurvivalSchedule n M d K)
      (boundedSharpTransferSchedule n D M d K) n ≤ 128 * C * E / A := by
  have hnormalized := fun i (hi : i < n) ↦ sparse_normalized_cubic_bound A C (p i) (D i) _
    hA (by exact_mod_cast hD i hi) (hfloor i hi) (hsurvival i hi)
  calc
    _ ≤ 2 * (n : ℝ≥0) * (64 * C / (3 * A)) :=
      transferPointWeight_boundedSharp_le_uniform_normalized n K D M d 2 _ hfactor hnormalized
    _ ≤ 2 * E * (64 * C / (3 * A)) := by gcongr
    _ = (128 * C * E / A) / 3 := by ring
    _ ≤ _ := div_le_self zero_le (by norm_num)

theorem sparse_initial_selection_ratio_le
    (E A p tau N : ℝ≥0) (hE : 0 < E) (hA : 0 < A) (hp : 0 < p) (htau : 0 < tau) (hN : 0 < N)
    (hratio : p ^ 2 * tau * N / 24 ≤ A / E) :
    E / A ≤ 24 / (p ^ 2 * tau * N) := by
  have h := (div_le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 24) hE).mp hratio
  apply (div_le_div_iff₀ hA (by positivity : 0 < p ^ 2 * tau * N)).mpr
  simpa only [mul_comm E, mul_comm A] using h

end

end Erdos207
