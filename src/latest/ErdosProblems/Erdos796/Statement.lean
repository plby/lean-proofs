import ErdosProblems.Erdos796.Core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The statement of Erdős Problem 796

This module formalizes only the corrected problem statement.  It does not
assert a solution.  The expression

`g₃(n) = n log log n / log n + (c + o(1)) n / log n`

is encoded as convergence of the normalized second-order error to `c`.
Values at the finitely many small natural numbers where logarithms vanish do
not affect a limit along `Filter.atTop`.
-/

namespace Erdos796

open Filter Topology

/-- The leading term `n log log n / log n`. -/
noncomputable def leadingTerm (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (Real.log n) / Real.log n

/-- The second-order scale `n / log n`. -/
noncomputable def secondOrderScale (n : ℕ) : ℝ :=
  (n : ℝ) / Real.log n

/-- The assertion that `c` is the second-order constant for `g₃`. -/
def HasSecondOrderConstant (c : ℝ) : Prop :=
  Tendsto
    (fun n : ℕ =>
      ((g3 n : ℝ) - leadingTerm n) / secondOrderScale n)
    atTop (𝓝 c)

/-- The corrected form of Erdős Problem 796: does a finite second-order
constant exist? -/
def ErdosProblem796 : Prop :=
  ∃ c : ℝ, HasSecondOrderConstant c

end Erdos796
