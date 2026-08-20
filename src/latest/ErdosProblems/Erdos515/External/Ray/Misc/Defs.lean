module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Real.Basic

/-!
## Shared defs, to minimise public imports
-/

open scoped Real
noncomputable section

/-- A `Finset ℕ` with only large elements -/
@[expose] public def Late (N : Finset ℕ) (m : ℕ) :=
  ∀ n, n ∈ N → n ≥ m

/-- Lipschitz coefficient for `pow1p_small_general` -/
@[expose] public def psg (r s : ℝ) : ℝ :=
  rexp (r * s / (1 - r)) / (1 - r)

/-- `max b (log x)` -/
public def maxLog (b x : ℝ) : ℝ :=
  (max b.exp x).log
