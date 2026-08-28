import Wikipedia.HopfProblem.PeriodTori
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars

/-!
# Genuine holomorphic sheaf cohomology of a native period torus

The space is the original period-lattice quotient with its unchanged
analytic atlas. Cohomology is Mathlib's actual Ext-defined sheaf
cohomology. Its complex scalar action is induced by multiplication on
the actual holomorphic-function sheaf in every degree.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The actual additive holomorphic-function sheaf on the native quotient torus. -/
abbrev holomorphicSheaf (p : PeriodDomain) :=
  HolomorphicFunctionSheaf.additiveSheaf I₂ p.Torus

/-- The genuine sheaf cohomology, with no choice of a replacement complex. -/
abbrev H (p : PeriodDomain) (q : ℕ) : Type :=
  CategoryTheory.Sheaf.H.{0} (holomorphicSheaf p) q

/-- The complex action is induced by actual scalar endomorphisms of the original sheaf. -/
instance cohomologyModule (p : PeriodDomain) (q : ℕ) : Module ℂ (H p q) :=
  CuspNormalization.SheafCohomology.holomorphicCohomologyModule I₂ p.Torus q

/-- The scalar action has its genuine functorial meaning on the Ext group. -/
theorem cohomology_smul (p : PeriodDomain) (q : ℕ) (c : ℂ) (a : H p q) :
    c • a = CategoryTheory.Sheaf.H.map
      (HolomorphicFunctionSheaf.scalarSheafEnd I₂ p.Torus c) q a := rfl

/-- Literal global holomorphic sections on the top open of the original torus. -/
abbrev GlobalSections (p : PeriodDomain) :=
  HolomorphicFunctionSheaf.GlobalSections I₂ p.Torus

/-- Actual bundled holomorphic functions on that same quotient manifold. -/
abbrev HolomorphicFunction (p : PeriodDomain) := C^ω⟮I₂, p.Torus; ℂ⟯

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology
