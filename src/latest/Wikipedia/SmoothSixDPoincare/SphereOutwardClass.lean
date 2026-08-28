import Wikipedia.SmoothSixDPoincare.SphereOutwardPointClass

/-!
# A constructed global outward source-class isomorphism

Choose one actual sphere point and construct a native chart neighborhood for
its own inverse coordinate function. Its outward point class is independent
of every such choice. This supplies a fixed source isomorphism even when a
particular collapse map has no belt crossings.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SpherePoint

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris SphereNormalCoordinates

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) := ⟨by simp⟩

def referencePoint (n : ℕ) : UnitSphere (n + 2) :=
  Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)

def referenceNeighborhood (n : ℕ) (x : UnitSphere (n + 2)) :
    LocalDegree.NeighborhoodData
      (((NativeParametrization.centered (D := EuclideanSpace ℝ (Fin (n + 2))) x).symm ∘
        Diffeomorph.refl (𝓡 (n + 2)) (UnitSphere (n + 2)) ∞) ∘
          NativeParametrization.centered x)
      (NativeChartTransition.linear x x
        (Diffeomorph.refl (𝓡 (n + 2)) (UnitSphere (n + 2)) ∞) rfl)
      ((NativeParametrization.centered x).source ∩
        NativeParametrization.centered x ⁻¹' (univ : Set (UnitSphere (n + 2)))) :=
  Classical.choice (NativeChartTransition.nonempty_neighborhoodData x x
    (Diffeomorph.refl (𝓡 (n + 2)) (UnitSphere (n + 2)) ∞) rfl univ (by simp))

variable (n : ℕ) {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
  (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
  (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H)

def outwardClass (k : ℕ) :
    SingularHomology (UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularHomology (UnitSphere (n + 1)) (k + 1) :=
  outwardPointClass n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

def outwardClassEquiv (k : ℕ) :
    SingularHomology (UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularHomology (UnitSphere (n + 1)) (k + 1) :=
  outwardPointClassEquiv n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

theorem outwardClassEquiv_apply (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 2)) (k + 2)) :
    outwardClassEquiv n j B k a = outwardClass n j B k a := rfl

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (x : UnitSphere (n + 2)) {f : UnitSphere (n + 2) → F}
  {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F} {W : Set (UnitSphere (n + 2))}
  (d : LocalDegree.NeighborhoodData (f ∘ NativeParametrization.centered x) L
    ((NativeParametrization.centered x).source ∩ NativeParametrization.centered x ⁻¹' W))

theorem outwardPointClass_eq_global (k : ℕ) :
    outwardPointClass n j B x d k = outwardClass n j B k :=
  outwardPointClass_eq n j B (referencePoint n) x
    (referenceNeighborhood n (referencePoint n)) d k

theorem pointConnecting_eq_outward (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 2)) (k + 2)) :
    LocalDegree.NativeNeighborhood.sphereConnecting x d (k + 1) a =
      (SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) : ℤ) •
        outwardClass n j B k a := by
  rw [connecting_eq_sign_outward n j B x d k a, outwardPointClass_eq_global]

end Wikipedia.SmoothSixDPoincare.SpherePoint
