import Wikipedia.NoExoticSixSphere.SphereCurveDistance
import Wikipedia.NoExoticSixSphere.SkewShortExponential
import Wikipedia.NoExoticSixSphere.SkewGram
import Wikipedia.NoExoticSixSphere.OrthogonalBasisEnergy
import Wikipedia.NoExoticSixSphere.OrthogonalSegmentEnergy

/-!
# Short orthogonal exponential segments minimize energy

An actual skew generator of operator norm at most `π` has the least energy
among smooth orthogonal paths with its endpoint increment. The comparison
is proved on any nondegenerate interval from the endpoint-angle estimates
in the actual Gram eigenbasis.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalPathEnergy

open GLOrthonormalization CayleyTransform HilbertSchmidt OrthogonalExponential
  SkewSpectralPlane SkewShortExponential

variable {n : ℕ}

theorem short_generator_energy_bound {γ : ℝ → OrthogonalOperators n}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1)) (K : SkewOperators n)
    (hK : ‖(K : Vector n →L[ℝ] Vector n)‖ ≤ Real.pi)
    {l u : ℝ} (hlu : l < u) (hend : γ u = γ l * exp K) :
    squareNorm (K : Vector n →L[ℝ] Vector n) ≤
      (u - l) * energy (fun t ↦ (γ t).1.1) l u := by
  let hS := gram_isSymmetric K
  let b := hS.eigenvectorBasis finrank_euclideanSpace_fin
  let μ := hS.eigenvalues finrank_euclideanSpace_fin
  have hi (i : Fin n) : μ i ≤ (u - l) *
      ∫ t : ℝ in l..u, ‖deriv (fun s ↦ (γ s).1.1) t (b i)‖ ^ 2 := by
    have hcol : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1 (b i)) := hγ.clm_apply contDiff_const
    have hn (t : ℝ) : ‖(γ t).1.1 (b i)‖ = 1 :=
      ((γ t).2 (b i)).trans (b.orthonormal.norm_eq_one i)
    have he : inner ℝ ((γ l).1.1 (b i)) ((γ u).1.1 (b i)) =
        inner ℝ (b i) ((exp K).1.1 (b i)) := by
      rw [hend]
      exact (OrthogonalPaths.toEquiv (γ l)).inner_map_map _ _
    have hb := SphereCurveAngle.endpoint_angle_sq_le_energy hcol hn hlu
    rw [he, eigenvector_endpoint_angle_sq K hK (b.orthonormal.norm_eq_one i)
      (hS.apply_eigenvectorBasis finrank_euclideanSpace_fin i)] at hb
    simpa only [deriv_apply_const hγ] using! hb
  rw [squareNorm_eq_eigenvalue_sum, energy_eq_basis_sum hγ b, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ hi i)

theorem short_generator_energy_div_le {γ : ℝ → OrthogonalOperators n}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1)) (K : SkewOperators n)
    (hK : ‖(K : Vector n →L[ℝ] Vector n)‖ ≤ Real.pi)
    {l u : ℝ} (hlu : l < u) (hend : γ u = γ l * exp K) :
    squareNorm (K : Vector n →L[ℝ] Vector n) / (u - l) ≤
      energy (fun t ↦ (γ t).1.1) l u := by
  apply (div_le_iff₀ (sub_pos.mpr hlu)).mpr
  simpa only [mul_comm] using short_generator_energy_bound hγ K hK hlu hend

/-- Replacing a smooth path segment by a short exponential segment never
increases its actual integral energy. -/
theorem short_segment_energy_le {γ : ℝ → OrthogonalOperators n}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1)) (K : SkewOperators n)
    (hK : ‖(K : Vector n →L[ℝ] Vector n)‖ ≤ Real.pi)
    {l u : ℝ} (hlu : l < u) (hend : γ u = γ l * exp K) :
    energy (fun t ↦ (rescaledSegment (γ l) K l u t).1.1) l u ≤
      energy (fun t ↦ (γ t).1.1) l u := by
  rw [energy_rescaledSegment]
  exact short_generator_energy_div_le hγ K hK hlu hend

end NoExoticSixSphere.OrthogonalPathEnergy
