/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # A noncircular explicit choice of the coupled concentration exponents -/

namespace Erdos207

def ksssPowerErrorExponent (b B : ℕ) : ℕ := b * B + 3 * b + 2
def ksssPowerMarginExponent (q b B : ℕ) : ℕ := ksssPowerErrorExponent b B + b * q
def ksssPowerDeterministicExponent (b : ℕ) : ℕ := 5 * b + 7
def ksssPowerRawVarianceExponent (b k : ℕ) : ℕ := k + 5 * b + 8
def ksssPowerJumpExponent (b k : ℕ) : ℕ := max (k + 2) (ksssPowerDeterministicExponent b) + 1
def ksssPowerVarianceExponent (b k : ℕ) : ℕ :=
  max (ksssPowerRawVarianceExponent b k) (2 * ksssPowerDeterministicExponent b) + 2
def ksssPowerThetaExponent (q b B k : ℕ) : ℕ :=
  ksssPowerJumpExponent b k + ksssPowerVarianceExponent b k + ksssPowerMarginExponent q b B + 1
def ksssPowerDenominatorExponent (q b B k Rmin : ℕ) : ℕ :=
  ksssPowerThetaExponent q b B k + ksssPowerMarginExponent q b B + ksssPowerErrorExponent b B +
    k + 3 * b * q + 2 * b + Rmin + 5

theorem ksss_power_exponent_hierarchy (q b B k Rmin : ℕ) :
    let s := ksssPowerErrorExponent b B
    let m := ksssPowerMarginExponent q b B
    let j := ksssPowerJumpExponent b k
    let v := ksssPowerVarianceExponent b k
    let H := ksssPowerThetaExponent q b B k
    let R := ksssPowerDenominatorExponent q b B k Rmin
    b * B + 3 * b + 2 ≤ s ∧ j ≤ H ∧ v + m + 1 ≤ H ∧ H + m + 2 ≤ R ∧
      s + k + 3 * b * q + 2 ≤ R ∧ s + 2 * b + 1 ≤ 2 * R ∧
      s + k + 1 ≤ R ∧ 5 * b + 2 ≤ 3 * R ∧ Rmin ≤ R ∧ 0 < R := by
  dsimp only [ksssPowerErrorExponent, ksssPowerMarginExponent, ksssPowerJumpExponent,
    ksssPowerVarianceExponent, ksssPowerThetaExponent, ksssPowerDenominatorExponent,
    ksssPowerDeterministicExponent, ksssPowerRawVarianceExponent]
  omega

theorem ksss_power_gain_exponent_gap (q b B k Rmin z : ℕ) (hz : z + 1 ≤ q) :
    k + ksssPowerErrorExponent b B + 3 * b * (z + 1) + 2 ≤
      ksssPowerDenominatorExponent q b B k Rmin := by
  have h := (ksss_power_exponent_hierarchy q b B k Rmin).2.2.2.2.1
  have hm := Nat.mul_le_mul_left (3 * b) hz
  omega

end Erdos207
