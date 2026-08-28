import Wikipedia.NoExoticSixSphere.OrthogonalVertexVariation

/-!
# Actual chart tangents of exponential vertex variations

In the existing product Cayley atlas, an exponential vertex variation in
direction `W` has derivative `-W/2`. Thus an injective linear family of
body directions gives independent actual tangent vectors, not merely
independent labels for curves.
-/

open Filter
open scoped Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace

variable {n m : ℕ}

theorem coordinates_vertexVariation (v : Space n m) (W : Model n m) (s : ℝ) (i : Fin m) :
    atVertices v (vertexVariation v W s) i = CayleyTransform.chart (exp (s • W i)) := by
  rw [atVertices_apply, CayleyAtlas.atOperator_apply]
  change coordinates ((v i)⁻¹ * (v i * exp (s • W i))) = coordinates (exp (s • W i))
  rw [inv_mul_cancel_left]

theorem hasFDerivAt_chart_exp_zero :
    HasFDerivAt (fun K : SkewOperators n ↦ CayleyTransform.chart (exp K))
      ((-(1 / 2) : ℝ) • (1 : SkewOperators n →L[ℝ] SkewOperators n)) 0 := by
  apply (hasFDerivAt_inCoordinates_zero (n := n)).congr_of_eventuallyEq
  filter_upwards [(isOpen_coordinateDomain n).mem_nhds (zero_mem_coordinateDomain n)] with K hK
  exact (inCoordinates_eq_chart K hK).symm

theorem hasDerivAt_chart_exp_smul_zero (K : SkewOperators n) :
    HasDerivAt (fun s : ℝ ↦ CayleyTransform.chart (exp (s • K))) ((-(1 / 2) : ℝ) • K) 0 := by
  have hd : HasDerivAt (fun s : ℝ ↦ s • K) K 0 := by
    simpa only [one_smul] using! (hasDerivAt_id (0 : ℝ)).smul_const K
  have hc := hasFDerivAt_chart_exp_zero (n := n)
  have hzero : (0 : ℝ) • K = 0 := zero_smul ℝ K
  rw [← hzero] at hc
  simpa only [smul_apply, one_apply_eq_self] using!
    hc.comp_hasDerivAt 0 hd

theorem hasDerivAt_vertexVariation_coordinates (v : Space n m) (W : Model n m) :
    HasDerivAt (fun s ↦ atVertices v (vertexVariation v W s)) ((-(1 / 2) : ℝ) • W) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [coordinates_vertexVariation, Pi.smul_apply] using hasDerivAt_chart_exp_smul_zero (W i)

theorem independent_chart_tangents (v : Space n m) {d : ℕ}
    (R : (Fin d → ℝ) →ₗ[ℝ] Model n m) (hR : Function.Injective R) :
    Function.Injective (fun c ↦ deriv (fun s ↦ atVertices v (vertexVariation v (R c) s)) 0) := by
  intro c e h
  change deriv (fun s ↦ atVertices v (vertexVariation v (R c) s)) 0 =
    deriv (fun s ↦ atVertices v (vertexVariation v (R e) s)) 0 at h
  rw [(hasDerivAt_vertexVariation_coordinates v (R c)).deriv,
    (hasDerivAt_vertexVariation_coordinates v (R e)).deriv] at h
  apply hR
  exact (smul_right_injective (M := Model n m) (by norm_num : (-(1 / 2) : ℝ) ≠ 0)) h

end NoExoticSixSphere.OrthogonalPolygon
