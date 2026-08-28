import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySmoothness
import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealExponential

/-! # Smoothness of the faithful real orthogonal representation -/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation

open QuaternionicSymmetricMatrices QuaternionicSymmetricMatrices.LocalLogarithm
open RealSymmetricMixing NoExoticSixSphere.CayleyTransform

variable {N : Type*} [Fintype N] [DecidableEq N]

local instance directionSelfChart :
    NormedChartedSpace (DirectionSpace N) (DirectionSpace N) := chartedSpaceSelf _

theorem contDiff_action : ContDiff ℝ ∞ (action (N := N)) :=
  finiteLinearMap_contDiff (representation (N := N)).toLinearMap

theorem contMDiff_specialOrthogonal :
    ContMDiff 𝓘(ℝ, DirectionSpace N) 𝓘(ℝ, SkewOperators (2 * Fintype.card N)) ∞
      (specialOrthogonal (N := N)) := by
  apply NoExoticSixSphere.OrthogonalSmoothness.contMDiff_iff_operator.mpr
  intro B
  rw [contMDiffAt_iff_source]
  have hm : ContDiff ℝ ∞ (fun A : DirectionSpace N ↦ matrix ((atPoint B).symm A)) :=
    (contDiff_const.mul contDiff_exponential_matrix).mul contDiff_const
  have hs : ContDiff ℝ ∞ (fun A : DirectionSpace N ↦ action (matrix ((atPoint B).symm A))) :=
    (contDiff_action (N := N)).comp hm
  change ContMDiffWithinAt 𝓘(ℝ, DirectionSpace N)
    𝓘(ℝ, RealSpace N →L[ℝ] RealSpace N) ∞
      (fun A : DirectionSpace N ↦ action (matrix ((atPoint B).symm A))) (range id) _
  rw [range_id, contMDiffWithinAt_univ]
  simpa only [] using! hs.contMDiff.contMDiffAt

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixRealRepresentation
