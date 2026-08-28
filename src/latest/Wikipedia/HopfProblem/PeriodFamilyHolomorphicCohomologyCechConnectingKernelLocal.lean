import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionRepresentatives
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1LiftingLocal

/-!
# Local primitives as sections of the actual intermediate kernel

The original kernel inclusion is injective on every open set. Thus a
local primitive whose differential is the restriction of a global
kernel section maps to that literal restricted kernel section.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

open HolomorphicFunctionSheaf.SphereH1
open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}
  (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- Equality of differentials identifies the actual local kernel
section with the restriction of the given global kernel section. -/
theorem toK_section_eq_of_differential (k : Section R.K (⊤ : Opens X))
    (V : Opens X) (t : Section R.complex.X₁ V)
    (ht : R.complex.f.hom.app (op V) t =
      res R.complex.X₂ le_top ((kernel.ι R.complex.g).hom.app (op (⊤ : Opens X)) k)) :
    R.toK.hom.app (op V) t = res R.K le_top k := by
  apply section_f_injective R.second_shortExact V
  have htoK := congrArg
    (fun u : R.complex.X₁ ⟶ R.complex.X₂ => u.hom.app (op V) t) R.toK_ι
  exact htoK.trans (ht.trans (res_map (kernel.ι R.complex.g) le_top k))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting
