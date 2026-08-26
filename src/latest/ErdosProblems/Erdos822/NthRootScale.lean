/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-! # Elementary natural nth-root scale bounds -/

namespace Erdos822

open Filter

theorem eventually_nthRoot_ge (k T : ℕ) (hk : k ≠ 0) :
    ∀ᶠ x : ℕ in atTop, T ≤ Nat.nthRoot k x := by
  filter_upwards [Filter.eventually_ge_atTop (T ^ k)] with x hx
  exact (Nat.le_nthRoot_iff hk).2 hx

theorem nthRoot_pow_le {k x : ℕ} (hk : k ≠ 0) :
    Nat.nthRoot k x ^ k ≤ x :=
  (Nat.pow_nthRoot_le_iff).2 (Or.inl hk)

theorem le_two_pow_mul_nthRoot_pow {k x : ℕ}
    (hk : k ≠ 0) (hroot : 1 ≤ Nat.nthRoot k x) :
    x ≤ 2 ^ k * Nat.nthRoot k x ^ k := by
  let N := Nat.nthRoot k x
  have hxlt : x < (N + 1) ^ k := Nat.lt_pow_nthRoot_add_one hk x
  have hN : N + 1 ≤ 2 * N := by
    dsimp [N] at hroot ⊢
    omega
  have hpow : (N + 1) ^ k ≤ (2 * N) ^ k :=
    Nat.pow_le_pow_left hN k
  calc
    x ≤ (N + 1) ^ k := hxlt.le
    _ ≤ (2 * N) ^ k := hpow
    _ = 2 ^ k * N ^ k := by ring

/-- A positive-degree natural root is no larger than its argument. -/
theorem nthRoot_le_self_of_pos {k N : ℕ} (hk : 0 < k) :
    Nat.nthRoot k N ≤ N := by
  let y := Nat.nthRoot k N
  change y ≤ N
  by_cases hy : y = 0
  · rw [hy]
    exact Nat.zero_le _
  · have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy
    have hpow : y ^ k ≤ N :=
      (Nat.pow_nthRoot_le_iff).2 (Or.inl hk.ne')
    exact (le_self_pow hy1 hk.ne').trans hpow

end Erdos822
