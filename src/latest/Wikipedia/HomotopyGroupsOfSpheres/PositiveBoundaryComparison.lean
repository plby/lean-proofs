import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundarySigns

/-! # Positive derivative comparisons give equal actual boundary homology maps -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.LocalBoundaryComparison

open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology
open ContinuousMap

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Finite ι] [Nontrivial ι]

theorem linearSphere_homotopic (b : Module.Basis ι ℝ E) (A B : E ≃L[ℝ] F)
    (h : 0 < (A.trans B.symm).toLinearEquiv.toLinearMap.det) :
    (LinearSphereAction.sphereMap A.toContinuousLinearMap A.injective).Homotopic
      (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) := by
  have hp := LinearSphereAction.homotopic_of_det_mul_pos b (A.trans B.symm)
    (ContinuousLinearEquiv.refl ℝ E) (by
      change 0 < (A.trans B.symm).toLinearEquiv.toLinearMap.det *
        (LinearMap.id : E →ₗ[ℝ] E).det
      rwa [LinearMap.det_id, mul_one])
  change (LinearSphereAction.sphereMap (A.trans B.symm).toContinuousLinearMap
    (A.trans B.symm).injective).Homotopic
      (LinearSphereAction.sphereMap (ContinuousLinearMap.id ℝ E) Function.injective_id) at hp
  rw [LinearSphereAction.sphereMap_id] at hp
  rw [LinearSphereAction.sphereMap_relative A B]
  simpa only [ContinuousMap.comp_id] using
    (Homotopic.refl (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)).comp hp

/-- This compares the original nonlinear boundary maps, at their actual chosen radii. -/
theorem normalized_homology_eq (b : Module.Basis ι ℝ E)
    {f g : E → F} {A B : E ≃L[ℝ] F} {s t : Set E}
    (a : LocalDegree.BoundaryData f A s) (c : LocalDegree.BoundaryData g B t)
    (h : 0 < (A.trans B.symm).toLinearEquiv.toLinearMap.det) (k : ℕ) :
    singularHomologyMap a.normalizedMap k = singularHomologyMap c.normalizedMap k := by
  rw [a.normalized_homology_compare, c.normalized_homology_compare]
  exact homotopic_homologyMap (linearSphere_homotopic b A B h) k

end Wikipedia.HomotopyGroupsOfSpheres.LocalBoundaryComparison
