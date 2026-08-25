/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Erdos390

open Set

/--
A labelled configuration of countably many atoms.  The conditioned
scale-invariant Poisson process is almost surely a positive,
summable, simple configuration; keeping the ambient type as a
sequence gives it the standard product measurable structure.
-/
abbrev PoissonDickmanConfiguration := ℕ → ℝ

/--
The support property of the scale-invariant process needed to make
additive configuration scores literal infinite sums: all atoms lie
in `[0,1]`, and their total mass is finite.
-/
def IsPoissonDickmanSummableConfiguration
    (π : PoissonDickmanConfiguration) : Prop :=
  (∀ n, π n ∈ Icc (0 : ℝ) 1) ∧ Summable π

end Erdos390
