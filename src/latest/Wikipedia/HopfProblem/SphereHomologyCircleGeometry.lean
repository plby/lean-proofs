import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The literal Euclidean unit sphere in dimension two and the native complex circle

The comparison is the restriction of the actual real linear isometry
`(x₀,x₁) ↦ x₀ + x₁ I`. Both directions use the original subspace
topologies and metrics. No homology calculation or replacement definition
of a sphere is used here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SphereHomology

/-- The actual real linear isometry from the Euclidean plane to the complex plane. -/
def euclideanPlaneComplexIsometry : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

@[simp] theorem euclideanPlaneComplexIsometry_apply (x : EuclideanSpace ℝ (Fin 2)) :
    euclideanPlaneComplexIsometry x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := rfl

@[simp] theorem euclideanPlaneComplexIsometry_symm_apply (z : ℂ) :
    euclideanPlaneComplexIsometry.symm z = ![z.re, z.im] := rfl

/-- Membership in the actual Euclidean sphere is preserved by the actual isometry. -/
theorem euclideanPlaneComplexIsometry_mem_sphere (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    euclideanPlaneComplexIsometry x ∈ Metric.sphere (0 : ℂ) r ↔
      x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) r := by
  simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]

/-- The original Euclidean unit sphere is homeomorphic to Mathlib's native complex unit circle. -/
def sphereCircleHomeomorph :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ _root_.Circle :=
  euclideanPlaneComplexIsometry.toHomeomorph.subtype
    (fun x => (euclideanPlaneComplexIsometry_mem_sphere x 1).symm)

/-- The comparison is literally the stated coordinate map on every point of the sphere. -/
@[simp] theorem sphereCircleHomeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (sphereCircleHomeomorph x : ℂ) = (x.val 0 : ℂ) + (x.val 1 : ℂ) * Complex.I := rfl

/-- The inverse is the actual real and imaginary coordinate vector. -/
@[simp] theorem sphereCircleHomeomorph_symm_apply (z : _root_.Circle) :
    (sphereCircleHomeomorph.symm z : EuclideanSpace ℝ (Fin 2)) =
      ![(z : ℂ).re, (z : ℂ).im] := rfl

/-- In fact the sphere comparison preserves the original metrics. -/
theorem sphereCircleHomeomorph_isometry : Isometry sphereCircleHomeomorph := by
  intro x y
  change edist (euclideanPlaneComplexIsometry x.val) (euclideanPlaneComplexIsometry y.val) =
    edist x.val y.val
  exact euclideanPlaneComplexIsometry.isometry x.val y.val

end Wikipedia.HopfProblem.SphereHomology
