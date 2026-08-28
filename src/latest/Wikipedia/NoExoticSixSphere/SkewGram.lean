import Wikipedia.NoExoticSixSphere.SkewSpectralPlane
import Wikipedia.NoExoticSixSphere.HilbertSchmidt

/-!
# Gram operators and Hilbert--Schmidt norms

The squared Hilbert--Schmidt norm is the sum of the Gram eigenvalues, with
respect to the actual orthonormal spectral basis.
-/

namespace NoExoticSixSphere.SkewSpectralPlane

open GLOrthonormalization CayleyTransform HilbertSchmidt

variable {n : ℕ}

theorem gram_smul (r : ℝ) (K : SkewOperators n) :
    gram (r • K) = r ^ 2 • gram K := by
  rw [gram, adjoint_eq_neg (r • K), gram, adjoint_eq_neg K]
  simp only [Submodule.coe_smul, ContinuousLinearMap.neg_comp,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, pow_two,
    smul_neg]

theorem squareNorm_eq_eigenvalue_sum (K : SkewOperators n) :
    squareNorm (K : Vector n →L[ℝ] Vector n) =
      ∑ i : Fin n, (gram_isSymmetric K).eigenvalues finrank_euclideanSpace_fin i := by
  let b := (gram_isSymmetric K).eigenvectorBasis finrank_euclideanSpace_fin
  rw [squareNorm, innerForm_eq_trace, ← sum_inner_eq_trace b]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_self_eq_norm_sq]
  have he : gram K (b i) =
      (gram_isSymmetric K).eigenvalues finrank_euclideanSpace_fin i • b i :=
    (gram_isSymmetric K).apply_eigenvectorBasis finrank_euclideanSpace_fin i
  simpa only [b.orthonormal.norm_eq_one i, one_pow, mul_one] using
    norm_apply_sq_of_eigenvector K he

end NoExoticSixSphere.SkewSpectralPlane
