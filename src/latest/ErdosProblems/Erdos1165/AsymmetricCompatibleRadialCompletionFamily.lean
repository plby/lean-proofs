/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricActualFarPairData

/-!
# Asymmetric radial rows over genuine nested renewal-completion atoms

At the separation scanner the admissible `y` return words form a genuine
renewal event, not one synthetic stopped-word cylinder.  That split-level
completion is retained as part of `Γ_x`.  Only the strictly deeper `y`
continuation is charged to the radial row.

This interface is exactly the resulting two-stage statement: measurable,
pairwise retained completion atoms; deeper tail atoms with an exact
conditional mass factorization; source coverage; and a checked row sum.
No equality between a completion event and a synthetic complement cylinder
is asserted.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AsymmetricCompatibleRadialCompletionFamily

open AsymmetricActualFarPairData AsymmetricPairTwoStageMass

noncomputable section

/-- Scanner-compatible split completion followed by a strictly deeper
right-hand radial tail.  `retained_subset` is the pathwise `Γ_x`
reconstruction statement. -/
structure CompatibleRadialCompletionFamily
    (successful retained gammaX : Set StepPath) (radialTail : ℝ) : Type 2 where
  RetainedCode : Type
  retainedCode_countable : Countable RetainedCode
  TailCode : RetainedCode → Type
  tailCode_countable : ∀ r, Countable (TailCode r)
  retainedAtom : RetainedCode → Set StepPath
  tailAtom : ∀ r, TailCode r → Set StepPath
  tailWeight : ∀ r, TailCode r → ℝ≥0∞
  successful_subset : successful ⊆ ⋃ r, ⋃ t, tailAtom r t
  retained_eq : retained = ⋃ r, retainedAtom r
  retained_measurable : ∀ r, MeasurableSet (retainedAtom r)
  retained_pairwise : Pairwise fun r s ↦
    Disjoint (retainedAtom r) (retainedAtom s)
  tail_mass : ∀ r t,
    fairSteps (tailAtom r t) =
      tailWeight r t * fairSteps (retainedAtom r)
  row_le : ∀ r, ∑' t, tailWeight r t ≤ ENNReal.ofReal radialTail
  retained_subset : retained ⊆ gammaX

attribute [instance]
  CompatibleRadialCompletionFamily.retainedCode_countable
attribute [instance]
  CompatibleRadialCompletionFamily.tailCode_countable

/-- The checked nested-completion family gives the exact A.16 two-stage
successful-mass comparison. -/
theorem CompatibleRadialCompletionFamily.successful_le
    {successful retained gammaX : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialCompletionFamily
      successful retained gammaX radialTail)
    (hradial0 : 0 ≤ radialTail) :
    fairSteps.real successful ≤ radialTail * fairSteps.real retained := by
  exact fairSteps_real_le_radialTail_mul_retained_of_atom_weights
    family.TailCode successful retained family.retainedAtom family.tailAtom
    family.tailWeight radialTail hradial0 family.successful_subset
    family.retained_eq family.retained_measurable family.retained_pairwise
    family.tail_mass family.row_le

end

end Erdos1165.AsymmetricCompatibleRadialCompletionFamily
