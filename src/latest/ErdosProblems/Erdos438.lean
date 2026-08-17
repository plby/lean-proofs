/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos438.Limit
import ErdosProblems.Erdos438.Upper

/-!
# Erdős Problem 438

The largest cardinality of a set `A ⊆ {1, ..., N}` for which `A + A`
contains no square is `(11 / 32 + o(1)) N`.

The predicate `SquareSumFree` quantifies over all ordered pairs from `A`, so
the diagonal case is included.  The lower bound is the eleven-class Massias
construction modulo 32.  The upper bound is the
Khalfalah--Lodha--Szemerédi energy-and-shifting argument, whose modular input
is the sharp Lagarias--Odlyzko--Shearer theorem.
-/

open Filter

namespace Erdos438

/-- Resolution of Erdős Problem 438: the extremal density of finite sets whose
pairwise sumset contains no square is exactly `11 / 32`. -/
theorem erdos_438 :
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop
      (nhds ((11 : ℝ) / 32)) := by
  exact tendsto_extremalSize_density_of_eventually_upper kls_eventuallyUpper

#print axioms Erdos438.erdos_438

end Erdos438
