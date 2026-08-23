import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter

namespace Erdos240

def IsSmooth (P : Set ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ q : ℕ, q.Prime → q ∣ n → q ∈ P

def IsPrimeSet (P : Set ℕ) : Prop :=
  ∀ ⦃p : ℕ⦄, p ∈ P → p.Prime

def EnumeratesSmooth (P : Set ℕ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ Set.range a = {n : ℕ | IsSmooth P n}

def HasDivergentGaps (P : Set ℕ) : Prop :=
  ∃ a : ℕ → ℕ, EnumeratesSmooth P a ∧
    Tendsto (fun i : ℕ => a (i + 1) - a i) atTop atTop

def Problem240 : Prop :=
  ∃ P : Set ℕ, P.Infinite ∧ IsPrimeSet P ∧ HasDivergentGaps P

theorem erdos_240 : Problem240 := by
  sorry

end Erdos240
