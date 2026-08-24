/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Prime
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace Erdos1058

noncomputable abbrev primeAt (k : ℕ) : ℕ := Nat.nth Nat.Prime k

noncomputable def lowerEndpoint : ℕ → ℕ
  | 0 => 1
  | k + 1 => primeAt k

def IsSolution (n : ℕ) : Prop :=
  0 < n ∧ ∃ k,
    lowerEndpoint k ≤ n ∧ n < primeAt k ∧
      ∀ r, r.Prime → r ∣ n.factorial + 1 →
        r = primeAt k ∨ r = primeAt (k + 1)

theorem erdos_1058 (n : ℕ) :
    IsSolution n ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
  sorry

end Erdos1058
