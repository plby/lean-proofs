import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionGlobalRestrictionBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionGlobalRestrictionNaturality

/-!
# Global and restricted base multipliers agree on the original native neighborhood cohomology

Restricting an original global holomorphic base function to an original
base open gives the same action on its native neighborhood cohomology
as the original ambient cohomology-presheaf map of the global multiplier.
The proof uses the actual coefficient square and genuine open-restriction
naturality in every degree. No Hausdorffness is needed for this comparison.

This concerns global functions and their restriction to one base open.
It does not assert full compatibility between arbitrary nested opens or
any local-ring, local-generation, or higher-direct-image base-change result.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction.GlobalRestriction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- Genuine open restriction takes the original global coefficient
map to the literal restricted-base coefficient map in every degree. -/
theorem openCohomologyEquiv_global_map (P : HolomorphicPeriodMap V B) (U : Opens B)
    (q : ℕ) (g : BaseFunctionAction.BaseFunction V B)
    (x : OpenClasses.neighborhoodCohomology P U q) :
    OpenClasses.openCohomologyEquiv P U q
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) q).map
            (BaseFunctionAction.baseMultiplyEnd P g)).app (op (Zero.basePreimage P U)) x) =
      CategoryTheory.Sheaf.H.map (preimageMultiplyEnd P U (restrictBaseFunction P U g)) q
        (OpenClasses.openCohomologyEquiv P U q x) := by
  let := P.totalChartedSpace
  exact holomorphicRestriction_cohomologyEquiv_naturality IT (Zero.basePreimage P U)
    (BaseFunctionAction.baseMultiplyEnd P g)
    (preimageMultiplyEnd P U (restrictBaseFunction P U g))
    (sheafIso_baseMultiply P U g) q x

/-- The canonical local base action of a restricted global function is
exactly its original ambient coefficient cohomology-presheaf map. -/
theorem neighborhood_smul_restrictBaseFunction (P : HolomorphicPeriodMap V B)
    (U : Opens B) (q : ℕ) (g : BaseFunctionAction.BaseFunction V B)
    (x : OpenClasses.neighborhoodCohomology P U q) :
    letI := neighborhoodCohomologyModule P U q
    restrictBaseFunction P U g • x =
      (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) q).map
          (BaseFunctionAction.baseMultiplyEnd P g)).app (op (Zero.basePreimage P U))) x := by
  let := neighborhoodCohomologyModule P U q
  apply (OpenClasses.openCohomologyEquiv P U q).injective
  exact (openCohomologyEquiv_smul_map P U q (restrictBaseFunction P U g) x).trans
    (openCohomologyEquiv_global_map P U q g x).symm

/-- The two original actions agree as actual endomorphisms of the
native neighborhood group, not merely on chosen classes. -/
theorem neighborhoodBaseEnd_restrictBaseFunction (P : HolomorphicPeriodMap V B)
    (U : Opens B) (q : ℕ) (g : BaseFunctionAction.BaseFunction V B) :
    (neighborhoodBaseEnd P U q (restrictBaseFunction P U g)).asHom =
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) q).map
          (BaseFunctionAction.baseMultiplyEnd P g)).app (op (Zero.basePreimage P U)) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact neighborhood_smul_restrictBaseFunction P U q g x

/-- Restriction of the canonical base-open ring action is the original
global coefficient ring action under the actual ambient-open Ext functor. -/
theorem neighborhoodBaseEnd_comp_restrictBaseFunction
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    (neighborhoodBaseEnd P U q).comp (restrictBaseFunction P U).toRingHom =
      (CuspNormalization.SheafCohomology.mapEndRingHom
        (OpenClasses.openCohomologyFunctor (TopCat.of P.TotalSpace)
          (Zero.basePreimage P U) q) (Zero.totalAdditiveSheaf P)).comp
        (BaseFunctionAction.baseMultiplyRingHom P) := by
  apply RingHom.ext
  intro g
  exact neighborhoodBaseEnd_restrictBaseFunction P U q g

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction.GlobalRestriction
