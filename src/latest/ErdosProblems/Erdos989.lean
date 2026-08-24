/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos989.Core
import ErdosProblems.Erdos989.UpperConstruction
import ErdosProblems.Erdos989.PeriodicReduction

/-!
# Erdős problem 989

The elementary definitions live in `Erdos989.Core`.  The main theorem below
is the unconditional, source-correct fixed-scale construction.  It also
retains a formal counterexample showing that `∀ r, ∃ A` cannot be changed by
logic alone into `∃ A, ∀ r`.

The stronger literal problem-page conjunction is still represented by
`Resolution`, but it is not a premise of the proved source-correct theorem.
See `tex/989.tex` for the source audit.
-/

namespace Erdos989

/-- The unconditional fixed-scale upper half of the established discrepancy
estimate. -/
theorem erdos_989_upper_bound : HasSqrtLogUpperConstruction :=
  FixedRadiusUpper.hasSqrtLogUpperConstruction

/-- Explicit constants furnished by the checked periodic construction. -/
theorem erdos_989_fixed_scale_explicit :
    ∀ r : ℝ, 8 ≤ r → ∃ A : Set Plane, IsAdmissible A ∧
      ∀ x : Plane,
        diskError A x r ≤ 70 * Real.sqrt (r * Real.log r) := by
  intro r hr
  exact FixedRadiusUpper.exists_admissible_fixedRadius_sqrtLog hr

/-- A checked counterexample to the abstract quantifier interchange used in
the overstated global reading. -/
theorem erdos_989_quantifier_counterexample :
    (∃ P : ℕ → ℕ → Prop,
  (∀ scale : ℕ, ∃ witness : ℕ, P witness scale) ∧
    ¬ ∃ witness : ℕ, ∀ scale : ℕ, P witness scale) :=
  hasFixedScaleButNoGlobalWitness

/-- Main source-correct resolution of the fixed-scale construction. -/
theorem erdos_989 : ((∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, ∀ r ≥ R, ∃ A : Set Erdos989.Plane,
  Erdos989.IsAdmissible A ∧ ∀ x : Erdos989.Plane,
    Erdos989.diskError A x r ≤ C * Real.sqrt (r * Real.log r)) ∧ (∃ P : ℕ → ℕ → Prop,
  (∀ scale : ℕ, ∃ witness : ℕ, P witness scale) ∧
    ¬ ∃ witness : ℕ, ∀ scale : ℕ, P witness scale)) :=
  ⟨erdos_989_upper_bound, erdos_989_quantifier_counterexample⟩

/-- The literal resolution contains the unsupported universal square-root
lower component. -/
theorem erdos_989_resolution_implies_universal_sqrt_lower
    (h : Resolution) : HasUniversalSqrtLowerBound :=
  h.1

/-- The literal resolution also contains the stronger global upper
component, whose quantifier order is `∃ A, ∀ r`. -/
theorem erdos_989_resolution_implies_global_sqrt_log_upper
    (h : Resolution) : HasGlobalSqrtLogUpperBound :=
  h.2

/-- A checked consequence explaining the exact remaining obstruction: the
literal problem-page resolution would imply the sharp quarter-radius periodic
disk discrepancy bound. -/
theorem erdos_989_resolution_implies_sharp_periodic_quarter
    (h : Resolution) : PeriodicReduction.HasSharpPeriodicQuarterRadius :=
  PeriodicReduction.sharpPeriodicQuarterRadius_of_universalSqrtLowerBound h.1

end Erdos989

#print axioms Erdos989.erdos_989_upper_bound
#print axioms Erdos989.erdos_989_fixed_scale_explicit
#print axioms Erdos989.erdos_989_quantifier_counterexample
#print axioms Erdos989.erdos_989
#print axioms Erdos989.erdos_989_resolution_implies_universal_sqrt_lower
#print axioms Erdos989.erdos_989_resolution_implies_global_sqrt_log_upper
#print axioms Erdos989.erdos_989_resolution_implies_sharp_periodic_quarter
