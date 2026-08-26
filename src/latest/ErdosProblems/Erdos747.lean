/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos747.CriticalAsymptotic

/-!
# Erdős Problem 747: Shamir's problem

The uniform `M`-edge 3-uniform hypergraph on `3 * n` labelled vertices
contains `n` pairwise vertex-disjoint edges with a sharp asymptotic
threshold `n * log n`.

`erdos747` proves the two probability limits at every fixed relative
distance below and above `n * log (3 * n)`.  `erdos747_asymptotic`
states the equivalent leading-order result for the least edge count
at which the matching probability is at least one half.

The proof follows Kahn, *Asymptotics for Shamir's Problem* (2023),
https://arxiv.org/abs/1909.06834.  The full mathematical reconstruction
and Leanization plan are in `tex/747.tex`.  No hitting-time claim is used.
-/

open Filter Real
open scoped Topology

namespace Erdos747

/-- The exact two-sided fixed-edge probability resolution of Problem 747. -/
theorem erdos747 : ShamirThresholdResolution := shamir_threshold_resolution

/-- The median perfect-matching threshold is asymptotic to `n * log n`. -/
theorem erdos747_asymptotic :
    Tendsto (fun n ↦ (critical n : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 1) :=
  critical_div_n_log_n_tendsto_one

/-- The canonical exact two-sided fixed-edge resolution of Erdős problem 747. -/
theorem erdos_747 : ShamirThresholdResolution :=
  erdos747

#print axioms erdos747
#print axioms erdos747_asymptotic

end Erdos747
