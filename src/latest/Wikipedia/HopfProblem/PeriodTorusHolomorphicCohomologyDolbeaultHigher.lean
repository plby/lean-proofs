import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultExact
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultAcyclic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# Genuine holomorphic torus cohomology above degree two

The native length-two resolution and the proved acyclicity of its three
smooth terms imply vanishing above degree two in the original Ext-defined
cohomology of the original holomorphic-function sheaf.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

/-- The actual sheaf cohomology vanishes above the length of the native
acyclic Dolbeault resolution, with no cohomology-vanishing premise. -/
theorem higher_subsingleton (p : PeriodDomain) (n : ℕ) : Subsingleton (H p (n + 3)) :=
  (resolution p).h_subsingleton_above_two (smooth_higher_subsingleton p)
    (pair_higher_subsingleton p) (smooth_higher_subsingleton p) n

/-- Vanishing of each original Ext class in degrees at least three. -/
theorem higher_eq_zero (p : PeriodDomain) (n : ℕ) (a : H p (n + 3)) : a = 0 :=
  (higher_subsingleton p n).elim a 0

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
