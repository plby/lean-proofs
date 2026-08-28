import Wikipedia.NoExoticSixSphere.SkewAntipodalSpectrum
import Wikipedia.NoExoticSixSphere.OrthogonalMinimalGenerators
import Wikipedia.NoExoticSixSphere.OrthogonalPathEnergy

/-!
# Minimum energy among antipodal exponential generators

The actual Gram eigenvalues of an antipodal generator are at least `π²`.
Their sum is its squared Hilbert--Schmidt norm. Equality holds exactly on
the locus obtained by scaling orthogonal complex structures by `π`.

This file compares exponential paths. It does not yet compare them with
all smooth or broken paths with the same endpoints.
-/

namespace NoExoticSixSphere.SkewAntipodalSpectrum

open GLOrthonormalization CayleyTransform HilbertSchmidt SkewSpectralPlane
  OrthogonalExponential OrthogonalComplexStructures

variable {n : ℕ}

theorem squareNorm_of_gram_scalar (K : SkewOperators n) (c : ℝ)
    (h : gram K = c • (1 : Vector n →L[ℝ] Vector n)) :
    squareNorm (K : Vector n →L[ℝ] Vector n) = n * c := by
  rw [squareNorm_eq_sum]
  calc
    _ = ∑ _i : Fin n, c := by
      apply Finset.sum_congr rfl
      intro i _
      have he : gram K (EuclideanSpace.basisFun (Fin n) ℝ i) =
          c • EuclideanSpace.basisFun (Fin n) ℝ i := by rw [h]; rfl
      simpa only [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i,
        one_pow, mul_one] using norm_apply_sq_of_eigenvector K he
    _ = n * c := by simp

theorem squareNorm_ge (K : SkewOperators n)
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n)) :
    (n : ℝ) * Real.pi ^ 2 ≤ squareNorm (K : Vector n →L[ℝ] Vector n) := by
  rw [squareNorm_eq_eigenvalue_sum]
  have hi (i : Fin n) : Real.pi ^ 2 ≤
      (gram_isSymmetric K).eigenvalues finrank_euclideanSpace_fin i :=
    gram_eigenvalue_ge_pi_sq K hexp
      (((gram_isSymmetric K).eigenvectorBasis finrank_euclideanSpace_fin).orthonormal.norm_eq_one i)
      ((gram_isSymmetric K).apply_eigenvectorBasis finrank_euclideanSpace_fin i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
  simpa using hsum

theorem squareNorm_eq_iff (K : SkewOperators n)
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n)) :
    squareNorm (K : Vector n →L[ℝ] Vector n) = (n : ℝ) * Real.pi ^ 2 ↔
      gram K = Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n) := by
  constructor
  · intro h
    let hS := gram_isSymmetric K
    let b := hS.eigenvectorBasis finrank_euclideanSpace_fin
    let μ := hS.eigenvalues finrank_euclideanSpace_fin
    have hb (i : Fin n) : gram K (b i) = μ i • b i :=
      hS.apply_eigenvectorBasis _ i
    have hge (i : Fin n) : Real.pi ^ 2 ≤ μ i :=
      gram_eigenvalue_ge_pi_sq K hexp (b.orthonormal.norm_eq_one i) (hb i)
    have hs : ∑ i : Fin n, (μ i - Real.pi ^ 2) = 0 := by
      rw [Finset.sum_sub_distrib]
      have ht := squareNorm_eq_eigenvalue_sum K
      change squareNorm (K : Vector n →L[ℝ] Vector n) = ∑ i, μ i at ht
      rw [← ht, h]
      simp
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ sub_nonneg.mpr (hge i))).mp hs
    have he : (gram K).toLinearMap =
        (Real.pi ^ 2 • (1 : Vector n →L[ℝ] Vector n)).toLinearMap := by
      apply b.toBasis.ext
      intro i
      have hi := hb i
      rw [sub_eq_zero.mp (hzero i (Finset.mem_univ i))] at hi
      exact hi
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun he x
  · exact squareNorm_of_gram_scalar K (Real.pi ^ 2)

theorem squareNorm_eq_iff_complexStructure (K : SkewOperators n)
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n)) :
    squareNorm (K : Vector n →L[ℝ] Vector n) = (n : ℝ) * Real.pi ^ 2 ↔
      ∃ J : Space n, Real.pi • J.1 = K :=
  (squareNorm_eq_iff K hexp).trans (gram_minimum_iff K)

end NoExoticSixSphere.SkewAntipodalSpectrum
