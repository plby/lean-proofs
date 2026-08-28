import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeDifferentialSheaf
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothMultipliers

/-!
# The original scalar actions on the native Dolbeault sequence

The actions are actual multiplication of the original holomorphic and
smooth functions and actual scalar multiplication of the native closed
covectors.  The original sheaf maps intertwine those actions.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

open CuspNormalization.SheafCohomology
open HolomorphicSheafCohomology

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Actual multiplication of holomorphic and smooth functions commutes
with the original inclusion, on every original open set. -/
theorem inclusion_scalar (c : ℂ) :
    (holomorphicScalarEnd 𝓘(ℂ, E) M c) ≫ Functions.inclusion E M =
      Functions.inclusion E M ≫ (SmoothFunctions.scalarEnd 𝓘(ℝ, E) M c) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact ContMDiffMap.ext fun _ => rfl

/-- The native differential commutes with the actual scalar sheaf maps. -/
theorem closedDifferential_scalar (c : ℂ) :
    (SmoothFunctions.scalarEnd 𝓘(ℝ, E) M c) ≫ closedDifferential E M =
      closedDifferential E M ≫ (ClosedForms.scalarEnd E M c) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change closedSectionLinearMap E M U.unop (c • s) =
    c • closedSectionLinearMap E M U.unop s
  exact map_smul (closedSectionLinearMap E M U.unop) c s

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential
