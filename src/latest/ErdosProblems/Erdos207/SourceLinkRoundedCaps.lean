/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredHallReferenceParameters
import ErdosProblems.Erdos207.SourceLinkFailureNormalization

/-! # Actual natural forbidden caps and their finite-order budget -/

namespace Erdos207

open Finset
open scoped NNReal

theorem source_link_uniform_cap_budget
    {J : Type*} (orders : Finset J) (epsilon a : ℝ≥0) :
    let cap := ⌊epsilon*a/(orders.card+1 : ℝ≥0)⌋₊
    (∑ _j ∈ orders, (cap : ℝ≥0)) ≤ epsilon*a ∧
      epsilon*a/(orders.card+1 : ℝ≥0) ≤ (cap+1 : ℝ≥0) := by
  dsimp only
  have hfloor := Nat.floor_le (show (0 : ℝ≥0) ≤ epsilon*a/(orders.card+1 : ℝ≥0) from zero_le)
  have hsplit : (orders.card : ℝ≥0)*(epsilon*a/(orders.card+1 : ℝ≥0)) ≤ epsilon*a := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ≥0) < orders.card+1)).mpr
    calc
      _ ≤ ((orders.card : ℝ≥0)+1)*(epsilon*a) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le) zero_le
      _ = _ := mul_comm _ _
  constructor
  · simp only [sum_const, nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_left hfloor zero_le).trans hsplit
  · exact (Nat.lt_floor_add_one (epsilon*a/(orders.card+1 : ℝ≥0))).le

theorem source_link_uniform_cap_power_lower
    {J : Type*} (orders : Finset J) (epsilon A a t : ℝ≥0) (f : ℕ)
    (ha : A*t^f ≤ a) :
    (epsilon*A/(orders.card+1 : ℝ≥0))*t^f ≤
      (⌊epsilon*a/(orders.card+1 : ℝ≥0)⌋₊+1 : ℝ≥0) := by
  calc
    _ = epsilon*(A*t^f)/(orders.card+1 : ℝ≥0) := by ring
    _ ≤ epsilon*a/(orders.card+1 : ℝ≥0) := by gcongr
    _ ≤ _ := (source_link_uniform_cap_budget orders epsilon a).2

end Erdos207
