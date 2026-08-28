import Wikipedia.HomotopyGroupsOfSpheres.CompactifiedRegularFiberSum
import Wikipedia.SmoothSixDPoincare.OutwardLocalBoundaryHomology
import Wikipedia.SmoothSixDPoincare.SphereOutwardClass

/-!
# Positive native normal signs give the actual global fiber-count formula

The native one-point source classes and the actual nonlinear boundary maps
are compared in one fixed outward convention. The global connecting map
therefore equals the fiber cardinality times the fixed source isomorphism.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres.CompactifiedRegularFiberSum

open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.SphereHomology Wikipedia.HopfProblem.SingularMayerVietoris

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) := ⟨by simp⟩

variable (n : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {P : Set (UnitSphere (n + 2))} [Fintype P]
  {f : UnitSphere (n + 2) → F} {W : Set (UnitSphere (n + 2))}
  (D : LocalDegree.SeparatedNeighborhoods (EuclideanSpace ℝ (Fin (n + 2))) P f W)
  (j : (ℝ × F) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
  (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)

theorem localClass_outward (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 2)) (k + 2)) (i : P) :
    localClass D (k + 1) a i =
      (SignType.sign (SphereNormalCoordinates.chartJacobian
        (NativeParametrization.centered i.val) j B 0) : ℤ) •
          SpherePoint.outwardClass n j B k a := by
  rw [localClass_singlePoint]
  exact SpherePoint.pointConnecting_eq_outward n j B i.val (D.data i) k a

theorem localBoundary_positive
    (hf : ∀ x ∈ P, MDifferentiableAt (𝓡 (n + 2)) 𝓘(ℝ, F) f x)
    (hA : ∀ x ∈ P, (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f x).IsInvertible)
    (hS : ∀ x ∈ P, SignType.sign (SphereNormalCoordinates.normalJacobian j x
      (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f x)) = 1)
    (k : ℕ) (a : SingularHomology (UnitSphere (n + 2)) (k + 2)) (i : P) :
    singularHomologyMap (D.data i).innerBoundary.normalizedMap (k + 1)
      (localClass D (k + 1) a i) =
        singularHomologyMap (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) (SpherePoint.outwardClass n j B k a) := by
  rw [localClass_outward n D j B]
  have hc0 := NativeParametrization.centered_zero
    (D := EuclideanSpace ℝ (Fin (n + 2))) i.val
  have h := SphereNormalCoordinates.localBoundary_homology_outward n
    (NativeParametrization.centered i.val) j B
    (NativeParametrization.zero_mem_centered_source i.val) f
    (hc0.symm ▸ hf i.val i.property) (hc0.symm ▸ hA i.val i.property)
    (D.linear i) (D.derivative_eq i) (D.data i).innerBoundary k
    (SpherePoint.outwardClass n j B k a)
  rw [hc0, hS i.val i.property, SignType.coe_one, one_smul] at h
  exact h

include D in
theorem sphereConnecting_positive_count (G : C(UnitSphere (n + 2), OnePoint F))
    (hzero : ∀ x, G x = ((0 : F) : OnePoint F) ↔ x ∈ P)
    (hfinite : ∀ x ∈ W, G x = (f x : OnePoint F))
    (hf : ∀ x ∈ P, MDifferentiableAt (𝓡 (n + 2)) 𝓘(ℝ, F) f x)
    (hA : ∀ x ∈ P, (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f x).IsInvertible)
    (hS : ∀ x ∈ P, SignType.sign (SphereNormalCoordinates.normalJacobian j x
      (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f x)) = 1)
    (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 2)) (k + 2)) :
    OnePointCover.sphereConnecting r hr (k + 1) (singularHomologyMap G (k + 2) a) =
      Fintype.card P •
        singularHomologyMap (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) (SpherePoint.outwardClass n j B k a) := by
  apply (sphereConnecting_sum D G hzero hfinite r hr (k + 1) a).trans
  calc
    _ = ∑ _i : P,
        singularHomologyMap (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) (SpherePoint.outwardClass n j B k a) := by
      apply Finset.sum_congr rfl
      intro i _
      exact localBoundary_positive n D j B hf hA hS k a i
    _ = _ := by simp

end Wikipedia.HomotopyGroupsOfSpheres.CompactifiedRegularFiberSum
