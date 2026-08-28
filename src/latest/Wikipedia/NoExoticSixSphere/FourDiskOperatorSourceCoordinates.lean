import Wikipedia.NoExoticSixSphere.ManifoldFourDiskRawFrame
import Wikipedia.NoExoticSixSphere.CollaredBoundaryOperatorCoordinates

/-!
# The actual normal-plus-derivative operator under fixed source coordinates

Precomposition by a fixed continuous linear equivalence changes only the
four derivative columns. The original normal columns are untouched, and
the resulting operator is the exact constant block-coordinate change.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (g : Vector 4 → M) (R : Vector 4 ≃L[ℝ] Vector 4)

theorem fourDiskDerivative_comp_coordinates (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 7) ∞ g (R x)) :
    e.fourDiskDerivative (g ∘ R) x =
      (e.fourDiskDerivative g (R x)).comp R.toContinuousLinearMap := by
  have hD : DifferentiableAt ℝ (e.toFun ∘ g) (R x) :=
    (e.smooth.contMDiffAt.comp (R x) hg).contDiffAt.differentiableAt (by simp)
  exact (hD.hasFDerivAt.comp x R.hasFDerivAt).fderiv

theorem normalFourDiskOperator_comp_coordinates (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 7) ∞ g (R x)) :
    e.normalFourDiskOperator a (g ∘ R) x =
      (e.normalFourDiskOperator a g (R x)).comp
        (CollaredDiskFrame.collarSourceChange
          (ContinuousLinearEquiv.refl ℝ e.NormalModel) R).toContinuousLinearMap := by
  rw [normalFourDiskOperator, normalFourDiskOperator,
    e.fourDiskDerivative_comp_coordinates g R x hg,
    CollaredDiskFrame.operator_comp_collarSourceChange]
  rfl

end NoExoticSixSphere.EuclideanEmbedding
