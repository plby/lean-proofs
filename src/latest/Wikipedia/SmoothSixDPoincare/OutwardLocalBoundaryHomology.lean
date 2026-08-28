import Wikipedia.SmoothSixDPoincare.SphereLocalDegreeOrientation

/-!
# Actual local boundary homology in the outward sphere convention

Correct the input boundary class by the original chart's radial orientation.
The induced map is then multiplication by the fixed normal Jacobian sign,
followed by the actual normalized reference-frame map. All maps and
derivatives are those of the original sphere chart and the original function.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {V F : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The outward-corrected boundary action is exactly the original normal sign. -/
theorem localBoundary_homology_outward (n : ℕ)
    [Fact (Module.finrank ℝ V = (n + 2) + 1)]
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 2))) (𝓡 (n + 2))
      (EuclideanSpace ℝ (Fin (n + 2))) (sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (hz : (0 : EuclideanSpace ℝ (Fin (n + 2))) ∈ c.source)
    (f : sphere (0 : V) 1 → F) (hf : MDifferentiableAt (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0))
    (hA : (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0)).IsInvertible)
    (L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (hL : L.toContinuousLinearMap = fderiv ℝ (f ∘ c) 0)
    {s : Set (EuclideanSpace ℝ (Fin (n + 2)))} (b : LocalDegree.BoundaryData (f ∘ c) L s)
    (k : ℕ) (a : SingularHomology (UnitSphere (n + 1)) (k + 1)) :
    singularHomologyMap b.normalizedMap (k + 1)
        ((SignType.sign (chartJacobian c j B 0) : ℤ) • a) =
      (SignType.sign (normalJacobian j (c 0)
        (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0))) : ℤ) •
          singularHomologyMap
            (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  have hs := chartJacobian_sign_factor c j B hz f hf hA
  have hd : (L.trans B.symm).toLinearEquiv.toLinearMap.det =
      (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) 0)).det := by
    rw [← hL]
    rfl
  rw [← hd] at hs
  have hi := congrArg (fun v : SignType => (v : ℤ)) hs
  simp only [SignType.coe_mul] at hi
  rw [map_zsmul, b.normalized_homology_eq_sign_smul n B k a, smul_smul, hi]

end Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates
