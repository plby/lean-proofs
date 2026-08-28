import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultCohomology
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultPuncturedDomain
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOne
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarTwo
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionCohomology

/-!
# Unconditional genuine holomorphic cohomology vanishing on `ℂ × ℂ*`

The constructed punctured-domain primitives solve the literal closed-pair
and top-degree differential equations on the actual open `{q | q.2 ≠ 0}`.
The proved open Dolbeault resolution and its genuine Ext comparisons then
give vanishing in every positive degree for the actual holomorphic function
sheaf. The endpoint has no solvability, Stein, exactness, comparison, or
cohomological-vanishing premise.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault

/-- The actual analytic closed-pair solver proves the required property. -/
theorem punctured_closedOneSolvable : ClosedOneSolvable puncturedOpen := by
  intro f g hf hg hclosed
  exact PuncturedDbarOne.exists_smooth_global_dbar_primitive hf hg hclosed

/-- The actual analytic top-degree solver proves the required property. -/
theorem punctured_topSolvable : TopSolvable puncturedOpen := by
  intro w hw
  exact PuncturedDbarTwo.exists_smooth_top_primitive hw

/-- Every positive Mathlib Ext-defined cohomology group of the actual
holomorphic function sheaf on `ℂ × ℂ*` is zero, unconditionally. -/
theorem punctured_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) puncturedOpen) (n + 1)) :=
  holomorphic_higher_subsingleton_of_solvable puncturedOpen
    punctured_closedOneSolvable punctured_topSolvable n

/-- The unconditional assertion for each actual Ext class. -/
theorem punctured_higher_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) puncturedOpen) (n + 1)) : a = 0 :=
  (punctured_higher_subsingleton n).elim a 0

/-- The same unconditional vanishing in the ambient cohomology presheaf. -/
theorem punctured_open_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ))
        (n + 1) puncturedOpen) := by
  let e := HolomorphicRestriction.cohomologyEquiv 𝓘(ℂ, ℂ × ℂ) puncturedOpen (n + 1)
  exact ⟨fun a b => e.injective ((punctured_higher_subsingleton n).elim (e a) (e b))⟩

theorem punctured_open_higher_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ))
        (n + 1) puncturedOpen) : a = 0 :=
  (punctured_open_higher_subsingleton n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault
