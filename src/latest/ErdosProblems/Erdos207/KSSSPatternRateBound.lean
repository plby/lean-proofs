/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternTrajectory
import ErdosProblems.Erdos207.KSSSTrajectoryBounds

/-! # Fixed-coefficient bounds on the pattern hazard target -/

namespace Erdos207

open Finset

noncomputable section

def ksssPatternHazardTrajectory (q : ℕ) (a : ℕ → ℝ) (E A : ℝ)
    (h m : ℕ) (time : ℝ) : ℝ :=
  (h : ℝ) * ksssPairTrajectory (ksssOrders q) a E A time +
    (m : ℝ) * ∑ j ∈ Icc 4 q,
      ksssConfigurationTrajectory (ksssOrders q) a E A (j - 3) (j - 4) time

def ksssPatternHazardCoefficient (q : ℕ) (coeff : ℕ → ℝ) (h m : ℕ) : ℝ :=
  (h : ℝ) + (m : ℝ) * (3 + (∑ d ∈ ksssOrders q, (d : ℝ) * coeff d) / 3)

theorem ksssPatternHazardCoefficient_nonneg
    (q : ℕ) (coeff : ℕ → ℝ) (h m : ℕ) (hb : ∀ d ∈ ksssOrders q, 0 ≤ coeff d) :
    0 ≤ ksssPatternHazardCoefficient q coeff h m := by
  have hsum : 0 ≤ ∑ d ∈ ksssOrders q, (d : ℝ) * coeff d :=
    sum_nonneg fun d hd ↦ mul_nonneg (Nat.cast_nonneg d) (hb d hd)
  unfold ksssPatternHazardCoefficient
  positivity

theorem ksssPatternHazardTrajectory_bounds
    (q : ℕ) (a coeff : ℕ → ℝ) (E A time : ℝ) (h m : ℕ)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d) :
    0 ≤ ksssPatternHazardTrajectory q a E A h m time ∧
      |ksssPatternHazardTrajectory q a E A h m time| ≤
        ksssPatternHazardCoefficient q coeff h m * ksssPairTrajectory (ksssOrders q) a E A time := by
  let x := ksssPairTrajectory (ksssOrders q) a E A time
  let z := ∑ j ∈ Icc 4 q,
    ksssConfigurationTrajectory (ksssOrders q) a E A (j - 3) (j - 4) time
  have hx : 0 < x := ksssPairTrajectory_pos _ _ hE hA hclock
  have hthreat := ksssThreatTrajectory_bounds (ksssOrders q) a coeff
    (fun _ hd ↦ (mem_Icc.mp hd).1) ha hab hE hA htime hclock
  rw [ksssThreatTrajectory_vertexOrders] at hthreat
  change 3 * x ≤ 3 * x + z ∧ 3 * x + z ≤
    (3 + (∑ d ∈ ksssOrders q, (d : ℝ) * coeff d) / 3) * x at hthreat
  have hz : 0 ≤ z := by linarith only [hthreat.1]
  have hupper : z ≤ (3 + (∑ d ∈ ksssOrders q, (d : ℝ) * coeff d) / 3) * x := by
    linarith only [hthreat.2, hx]
  have hnon : 0 ≤ (h : ℝ) * x + (m : ℝ) * z := by positivity
  refine ⟨hnon, ?_⟩
  change |(h : ℝ) * x + (m : ℝ) * z| ≤ _
  rw [abs_of_nonneg hnon]
  calc
    _ ≤ (h : ℝ) * x + (m : ℝ) * ((3 + (∑ d ∈ ksssOrders q, (d : ℝ) * coeff d) / 3) * x) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg m))
    _ = _ := by unfold ksssPatternHazardCoefficient; ring

end

end Erdos207
