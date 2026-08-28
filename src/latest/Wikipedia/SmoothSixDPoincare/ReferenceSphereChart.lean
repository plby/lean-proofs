import Wikipedia.SmoothSixDPoincare.PuncturedSphereChart
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph

/-!
# A fixed full-source native sphere chart in any Euclidean coordinate model

An orthonormal basis identifies the domain isometrically with the standard
model. The centered stereographic chart supplies the reference sphere disk;
its full source and omitted antipode are proved, not additional data.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereCoordinates

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (n : ℕ) (hdim : Module.finrank ℝ F = n)

def referenceIsometry : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((stdOrthonormalBasis ℝ F).reindex (finCongr hdim)).repr

def referencePole : Hemisphere.Sphere n :=
  Hemisphere.point true ⟨0, mem_closedBall_self zero_le_one⟩

def referenceChart : PartialDiffeomorph 𝓘(ℝ, F) (𝓡 n) F (Hemisphere.Sphere n) ∞ :=
  (referenceIsometry F n hdim).toContinuousLinearEquiv.toDiffeomorph.toPartialDiffeomorph.trans
    (NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) (referencePole n))

theorem referenceChart_source : (referenceChart F n hdim).source = univ := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  ext x
  change (x ∈ (univ : Set F) ∧ referenceIsometry F n hdim x ∈
    (NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n))
      (referencePole n)).source) ↔ x ∈ univ
  rw [NativeParametrization.centered_sphere_source]
  simp only [mem_univ, and_self]

theorem referenceChart_target : (referenceChart F n hdim).target = {-referencePole n}ᶜ := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  ext x
  change (x ∈ (NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n))
      (referencePole n)).target ∧
    (NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n))
      (referencePole n)).symm x ∈ (univ : Set (EuclideanSpace ℝ (Fin n)))) ↔
    x ∈ {-referencePole n}ᶜ
  rw [NativeParametrization.centered_sphere_target]
  simp only [mem_univ, and_true]

theorem referenceChart_zero : referenceChart F n hdim (0 : F) = referencePole n := by
  change NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n))
    (referencePole n) (referenceIsometry F n hdim 0) = referencePole n
  rw [map_zero]
  exact NativeParametrization.centered_zero (referencePole n)

end Wikipedia.SmoothSixDPoincare.SphereCoordinates
