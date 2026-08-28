import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexVariation
import Wikipedia.HomotopyGroupsOfSpheres.RealCurveCalculus

/-!
# Chart tangents of actual symplectic exponential variations

The tangent in the product Cayley chart is `-W/2`. Consequently an
injective family of quaternionic body directions gives independent actual
tangent vectors in the symplectic vertex manifold.
-/

open Filter
open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open VertexSpace Exponential

variable {n m : ℕ}

theorem coordinates_vertexVariation (v : Space n m) (W : Model n m) (s : ℝ) (i : Fin m) :
    atVertices v (vertexVariation v W s) i = cayleyChart n (exp (s • W i)) := by
  rw [atVertices_apply, CayleyAtlas.atOperator_apply]
  change cayleyCoordinates n ((v i)⁻¹ * (v i * exp (s • W i))) =
    cayleyCoordinates n (exp (s • W i))
  rw [inv_mul_cancel_left]

theorem hasFDerivAt_chart_exp_zero :
    HasFDerivAt (fun K : SkewSpace n => cayleyChart n (exp K))
      (realScalarOperator (SkewSpace n) (-(1 / 2))) 0 := by
  apply (hasFDerivAt_inCoordinates_zero (n := n)).congr_of_eventuallyEq
  filter_upwards [(isOpen_coordinateDomain n).mem_nhds (zero_mem_coordinateDomain n)] with K hK
  exact (inCoordinates_eq_chart K hK).symm

theorem hasDerivAt_chart_exp_smul_zero (K : SkewSpace n) :
    HasDerivAt (fun s : ℝ => cayleyChart n (exp (s • K))) ((-(1 / 2) : ℝ) • K) 0 :=
  real_hasDerivAt_comp_smul_zero (E := SkewSpace n) (hasFDerivAt_chart_exp_zero (n := n)) K

theorem hasDerivAt_vertexVariation_coordinates (v : Space n m) (W : Model n m) :
    HasDerivAt (fun s => atVertices v (vertexVariation v W s)) ((-(1 / 2) : ℝ) • W) 0 := by
  apply real_hasDerivAt_pi (E := SkewSpace n)
  intro i
  simpa only [coordinates_vertexVariation, Pi.smul_apply] using hasDerivAt_chart_exp_smul_zero (W i)

theorem independent_chart_tangents (v : Space n m) {d : ℕ}
    (R : (Fin d → ℝ) →ₗ[ℝ] Model n m) (hR : Function.Injective R) :
    Function.Injective (fun c => deriv (fun s => atVertices v (vertexVariation v (R c) s)) 0) := by
  intro c e h
  change deriv (fun s => atVertices v (vertexVariation v (R c) s)) 0 =
    deriv (fun s => atVertices v (vertexVariation v (R e) s)) 0 at h
  rw [real_deriv_eq_of_hasDerivAt (E := Model n m)
      (hasDerivAt_vertexVariation_coordinates v (R c)),
    real_deriv_eq_of_hasDerivAt (E := Model n m)
      (hasDerivAt_vertexVariation_coordinates v (R e))] at h
  apply hR
  exact (smul_right_injective (M := Model n m) (by norm_num : (-(1 / 2) : ℝ) ≠ 0)) h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
