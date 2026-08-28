import Wikipedia.SmoothSixDPoincare.LinearSphereHomotopy
import Wikipedia.SmoothSixDPoincare.LocalDegreeLinearization
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Normalized linear maps preserve composition and positive boundary radii

These are pointwise identities for the original sphere maps. In particular,
normalizing the derivative on a small sphere gives exactly its unit-sphere
map, independent of the chosen positive radius.
-/

noncomputable section

open Set Metric ContinuousMap Function

namespace Wikipedia.SmoothSixDPoincare.LinearSphereAction

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem sphereMap_comp (A : E →L[ℝ] F) (B : F →L[ℝ] G)
    (hA : Injective A) (hB : Injective B) :
    (sphereMap B hB).comp (sphereMap A hA) = sphereMap (B.comp A) (hB.comp hA) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (B (‖A x.val‖⁻¹ • A x.val)) =
    NormedSpace.normalize (B (A x.val))
  rw [map_smul]
  exact NormedSpace.normalize_smul_of_pos
    (inv_pos.mpr (norm_pos_iff.mpr (puncturedMap A hA x).property)) _

theorem sphereMap_trans (A : E ≃L[ℝ] F) (B : F ≃L[ℝ] G) :
    sphereMap (A.trans B).toContinuousLinearMap (A.trans B).injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap A.toContinuousLinearMap A.injective) :=
  (sphereMap_comp A.toContinuousLinearMap B.toContinuousLinearMap A.injective B.injective).symm

/-- The original small-radius linear boundary normalizes to the unit-radius operator map. -/
theorem normalized_linearSphereMap (A : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    PuncturedRadial.toSphere.comp (LocalDegree.linearSphereMap A r hr) =
      sphereMap A.toContinuousLinearMap A.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (A (r • x.val)) = NormedSpace.normalize (A x.val)
  rw [map_smul, NormedSpace.normalize_smul_of_pos hr]

/-- Compare a linear map with an arbitrary fixed frame, retaining both actual sphere maps. -/
theorem sphereMap_relative (A B : E ≃L[ℝ] F) :
    sphereMap A.toContinuousLinearMap A.injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap (A.trans B.symm).toContinuousLinearMap (A.trans B.symm).injective) := by
  rw [← sphereMap_trans]
  have heq : (A.trans B.symm).trans B = A := by
    ext x
    exact B.apply_symm_apply (A x)
  rw [heq]

end Wikipedia.SmoothSixDPoincare.LinearSphereAction
