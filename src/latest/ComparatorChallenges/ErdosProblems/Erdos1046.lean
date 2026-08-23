/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1046

Pommerenke's theorem that the connected open lemniscate of a monic complex
polynomial is contained in a disk of radius `2`.
-/

open Filter MeasureTheory Metric Polynomial Real Set Topology
open scoped BigOperators ComplexConjugate

namespace Erdos1046

/-- The open unit lemniscate of a complex polynomial. -/
def lemniscate (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ < 1}

/-- The corresponding closed unit lemniscate. -/
def closedLemniscate (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ ≤ 1}

/-- The centroid of the roots, counted with multiplicity. -/
noncomputable def rootCentroid (f : ℂ[X]) : ℂ :=
  f.roots.sum / (f.natDegree : ℂ)

theorem erdos_1046 (f : ℂ[X]) (hf : f.Monic)
    (hE : IsConnected (lemniscate f)) :
    ∃ c : ℂ, lemniscate f ⊆ Metric.ball c 2 := by
  sorry

end Erdos1046
