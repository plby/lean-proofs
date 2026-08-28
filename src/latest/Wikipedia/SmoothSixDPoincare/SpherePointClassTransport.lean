import Wikipedia.SmoothSixDPoincare.SphereTransportDiffeomorph
import Wikipedia.SmoothSixDPoincare.NativePointDiffeomorphNaturality

/-!
# Exact comparison of native point classes at any two original sphere points

The constructed determinant-one sphere diffeomorphism acts trivially on
ambient homology. Its actual centered-chart derivative therefore compares
the two point connecting classes by its proved determinant sign. All point
motion, auxiliary neighborhoods, and linearization are constructed.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SpherePoint

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) := ⟨by simp⟩

def pointDiffeomorph (n : ℕ) (x y : UnitSphere (n + 2)) :
    Diffeomorph (𝓡 (n + 2)) (𝓡 (n + 2)) (UnitSphere (n + 2)) (UnitSphere (n + 2)) ∞ :=
  sphereDiffeomorph (positiveTransport (n + 1) x y)

theorem pointDiffeomorph_apply (n : ℕ) (x y : UnitSphere (n + 2)) :
    pointDiffeomorph n x y x = y := positiveTransport_moves (n + 1) x y

def pointChartLinear (n : ℕ) (x y : UnitSphere (n + 2)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  NativeChartTransition.linear x y (pointDiffeomorph n x y) (pointDiffeomorph_apply n x y)

variable (n : ℕ) {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (x y : UnitSphere (n + 2)) {fx : UnitSphere (n + 2) → F} {fy : UnitSphere (n + 2) → G}
  {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
  {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G} {Wx Wy : Set (UnitSphere (n + 2))}
  (dx : LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
    ((NativeParametrization.centered x).source ∩ NativeParametrization.centered x ⁻¹' Wx))
  (dy : LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered y) Ly
    ((NativeParametrization.centered y).source ∩ NativeParametrization.centered y ⁻¹' Wy))

/-- Point classes differ by the determinant sign of the actual coordinate transition. -/
theorem pointClass_sign_compare (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 2)) (k + 2)) :
    LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a =
      (SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det : ℤ) •
        LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a := by
  have h := LocalDegree.pointConnecting_diffeomorph x y dx dy
    (pointDiffeomorph n x y) (pointDiffeomorph_apply n x y) (k + 1) a
  have hid : singularHomologyMap
      (pointDiffeomorph n x y).toHomeomorph.toHomotopyEquiv.toFun (k + 2) a = a :=
    positiveTransport_homology (n + 1) x y (k + 2) a
  rw [hid] at h
  apply h.trans
  exact LinearSphereAction.homology_eq_sign_smul n (pointChartLinear n x y) k _

end Wikipedia.SmoothSixDPoincare.SpherePoint
