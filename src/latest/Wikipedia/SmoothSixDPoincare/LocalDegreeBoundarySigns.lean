import Wikipedia.SmoothSixDPoincare.LinearSphereHomology
import Wikipedia.SmoothSixDPoincare.LinearSphereComposition
import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundaryHomology

/-!
# The actual local boundary homology map has the derivative's determinant sign

Compare with any single fixed target frame. The zero-avoiding linearization,
the exact positive-radius normalization, and the proved linear sphere action
give the sign formula for the original nonlinear boundary map.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

namespace LinearSphereAction

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem homology_relative_sign (n : ℕ)
    (A B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (k : ℕ) (a : SingularHomology (UnitSphere (n + 1)) (k + 1)) :
    singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective) (k + 1) a =
      (SignType.sign (A.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  rw [sphereMap_relative A B, singularHomologyMap_comp, LinearMap.comp_apply,
    homology_eq_sign_smul]
  exact map_zsmul _ _ _

end LinearSphereAction

namespace LocalDegree.BoundaryData

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normalized_homology_compare {f : E → F} {L : E ≃L[ℝ] F} {s : Set E}
    (b : BoundaryData f L s) (k : ℕ) :
    singularHomologyMap b.normalizedMap k =
      singularHomologyMap (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) k := by
  change singularHomologyMap (PuncturedRadial.toSphere.comp b.map) k = _
  rw [singularHomologyMap_comp, b.homology_compare, ← singularHomologyMap_comp,
    LinearSphereAction.normalized_linearSphereMap]

/-- Local nonlinear boundary action, with its actual derivative compared to one fixed frame. -/
theorem normalized_homology_eq_sign_smul (n : ℕ)
    {f : EuclideanSpace ℝ (Fin (n + 2)) → F}
    {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {s : Set (EuclideanSpace ℝ (Fin (n + 2)))} (b : BoundaryData f L s)
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (k : ℕ) (a : SingularHomology (UnitSphere (n + 1)) (k + 1)) :
    singularHomologyMap b.normalizedMap (k + 1) a =
      (SignType.sign (L.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        singularHomologyMap
          (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  rw [b.normalized_homology_compare]
  exact LinearSphereAction.homology_relative_sign n L B k a

end LocalDegree.BoundaryData

end Wikipedia.SmoothSixDPoincare
