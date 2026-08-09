import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1138

open Nat Set Filter

noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

noncomputable def realPi (t : ℝ) : ℕ := Nat.primeCounting ⌊t⌋₊

noncomputable def maxPrimeGap (x : ℝ) : ℕ :=
  Finset.sup (Finset.range (Nat.primeCounting' ⌈x⌉₊)) primeGap

def AsymptoticA (C : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ X : ℝ, ∀ x ≥ X, ∀ y : ℝ, x / 2 < y → y < x →
    |((realPi (y + C * (maxPrimeGap x : ℝ)) : ℝ) - (realPi y : ℝ)) *
      Real.log y / (C * (maxPrimeGap x : ℝ)) - 1| < ε
end Erdos1138

attribute [local instance] Classical.propDecidable

theorem Erdos1138.erdos1138_corollary :
    Not
      (∀ (C : Real),
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) C →
          Erdos1138.AsymptoticA C)
  := by
  sorry
